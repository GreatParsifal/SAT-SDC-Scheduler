#include "common.h"
#include "SDC.h"
#include "SAT.h"
#include "minisat/core/Solver.h"
#include <iostream>
#include <fstream>
#include <unordered_map>
#include <queue>

using namespace std;

// 返回 true 表示成功并填充 LB, UB；false 表示发现环或其它失败
bool compute_LB_UB_topo(DFG* dfg, std::vector<int>& LB, std::vector<int>& UB) {
    int n = dfg->stmts.size();
    LB.assign(n, 0);
    UB.assign(n, 0);
    if (n == 0) return true;

    // 1) 构造邻接（uses）与入度
    std::vector<std::vector<int>> adj(n);
    std::vector<int> indeg(n, 0);
    vec2d<int> deps;
    vec2d<int> uses;
    get_deps_and_uses(dfg, deps, uses);
    for (int u = 0; u < n; ++u) {
        for (int v : uses[u]) { // 如果你的结构不是这样，改为 get_uses(u)
            adj[u].push_back(v);
            indeg[v] += 1;
        }
    }

    // 2) 拓扑排序（Kahn）
    std::queue<int> q;
    for (int i = 0; i < n; ++i) if (indeg[i] == 0) q.push(i);

    std::vector<int> topo;
    topo.reserve(n);
    while (!q.empty()) {
        int u = q.front(); q.pop();
        topo.push_back(u);
        for (int v : adj[u]) {
            indeg[v] -= 1;
            if (indeg[v] == 0) q.push(v);
        }
    }
    if ((int)topo.size() != n) {
        // 存在环（DFG 不应有环），返回失败
        std::cerr << "[compute_LB_UB_topo] DFG has cycles (topo size=" << topo.size() << ", n=" << n << ")\n";
        return false;
    }

    // 3) 计算 dur(i)
    auto dur = [&](int i)->int {
        int lat = dfg->stmts[i]->op->latency;
        return (lat > 0 ? lat : 1);
    };

    // 4) 正向最长路径计算 ES = LB
    for (int i = 0; i < n; ++i) LB[i] = 0;
    for (int u : topo) {
        int end_u = LB[u] + dur(u); // earliest finish of u
        for (int v : adj[u]) {
            if (LB[v] < end_u) LB[v] = end_u;
        }
    }

    // 5) 计算项目总长度 T = max_i (ES[i] + dur[i])
    int T = 0;
    for (int i = 0; i < n; ++i) {
        T = std::max(T, LB[i] + dur(i));
    }

    // 6) 反向最晚允许 LS：初始化为 T - dur(i)
    const int INF = std::numeric_limits<int>::max() / 4;
    std::vector<int> LS(n, INF);
    // 先找 sinks（没有后继）并设其 LS = T - dur(sink)
    std::vector<int> outdeg(n, 0);
    for (int u = 0; u < n; ++u) {
        for (int v : adj[u]) outdeg[u] += 1;
    }
    // 对所有节点初始化 LS 为 T - dur(i)（安全）
    for (int i = 0; i < n; ++i) LS[i] = T - dur(i);

    // 按反向拓扑 relax： LS[u] = min( LS[u], LS[v] - dur(u) ) for each edge u->v
    for (int idx = (int)topo.size()-1; idx >= 0; --idx) {
        int u = topo[idx];
        for (int v : adj[u]) {
            // u must finish before v starts: LS[u] <= LS[v] - dur(u)
            int candidate = LS[v] - dur(u);
            if (candidate < LS[u]) LS[u] = candidate;
        }
    }

    // 7) 把 LS 作为 UB（latest start）。同时修正一下保证 LB <= UB
    for (int i = 0; i < n; ++i) {
        UB[i] = LS[i];
        if (UB[i] < LB[i]) {
            // 如果出现 LB > UB，说明约束下不可行（或上界过紧），将 UB 设为 LB（保守处理）
            // 你也可以选择返回 false 表示不一致
            UB[i] = LB[i];
        }
    }

    return true;
}

bool Joint_Solver(DFG* dfg, const std::vector<Op*>& ops,
              const std::vector<Constr*>& constrs, double clock_period, int mid, std::vector<int>& out_sc) {
    int n = dfg->stmts.size();
    if (n == 0) return false;

    // joint.log 每次覆盖（trunc），只保留本次 mid 的详细日志
    ofstream log("joint.log");
    if (!log) {
        cerr << "Failed to open joint.log, fallback to stdout\n";
    }
    auto& out = log.is_open() ? log : cout;

    out << "\n[JOINT] Trying makespan mid = " << mid << "\n";
    for (int i = 0; i < n; ++i) out << "[DFG] Stmt " << i << ": " << dfg->stmts[i]->op->name << endl;

    // SDC 初始化
    SDC sdc(dfg, ops, constrs, clock_period, out);
    sdc.init();

    // 如果 mid>0 则启用上界，否则跳过（第一次无上界）
    if (mid > 0) {
        if(!sdc.set_start_bound(mid)) {
            out << "[SDC] set_start_bound(" << mid << ") failed (negative cycle). prune this mid.\n";
            return false;
        }
    } else {
        out << "[SDC] No start bound enforced for this Joint_Solver run (mid <= 0).\n";
        // 注意：不调用 set_start_bound，保留 base_edges / base_dist
        // sdc.restore_base() 可以保持，但这里刚 init 过无需。
    }

    // 构造资源映射（每次 Joint_Solver 都用新的 SAT）
    unordered_map<int, vector<int>> res_to_stmts;
    unordered_map<int, vector<int>> mem_to_stmts;
    int ports = 0;
    for (int i = 0; i < n; ++i) {
        Stmt* stmt = dfg->stmts[i];
        Op* op = stmt->op;
        if (stmt->is_mem_stmt()) {
            int mem_id = stmt->get_arr_idx();
            mem_to_stmts[mem_id].push_back(i);
            ports = op->limit;
        }
        res_to_stmts[op->idx].push_back(i);
    }
    std::vector<int> LB, UB;
    LB.reserve(n);
    UB.reserve(n);
    if (!compute_LB_UB_topo(dfg, LB, UB)) {
        out << "[JOINT] compute_LB_UB_topo failed (DFG has cycle?). Aborting this mid.\n";
        return false;
    }
    // 2. build DUR vector
    std::vector<int> DUR(n);
    for (int i = 0; i < n; ++i) {
        int lat = dfg->stmts[i]->op->latency;
        DUR[i] = (lat > 0 ? lat : 1);
    }
    SAT sat(n,out);

    // 资源编码
    for (auto &kv : res_to_stmts) {
        int op_idx = kv.first;
        const vector<int> &group = kv.second;
        Op* rop = ops[op_idx];
        int limit = rop->limit;
        if (limit < 0) continue;
        out << "[SAT] encode resource type " << op_idx
            << " : size=" << group.size()
            << " limit=" << limit << endl;
        sat.encode_resource(group, limit, &LB, &UB, &DUR);
    }

    for (auto &kv : mem_to_stmts) {
        int mem_id = kv.first;
        const vector<int> &group = kv.second;
        int limit = ports;
        out << "[SAT] encode memory resource mem_id=" << mem_id
            << " : size=" << group.size()
            << " ports=" << limit << endl;
        sat.encode_resource(group, limit, &LB, &UB, &DUR);
    }

    // 主循环：SAT -> 提取 order -> 用 SDC 检查（可能 forbid 某个 order 并重试 SAT）
    while (true) {
        bool sat_ok = sat.solve();
        out << "[SAT] SAT solve result: " << (sat_ok ? "SAT" : "UNSAT") << endl;
        if (!sat_ok) {
            out << "[SAT] UNSAT: no feasible resource schedule under current constraints.\n";
            return false;
        }

        vector<pair<int,int>> orders;
        sat.get_true_orders(orders);
        out << "[SAT] Number of true orders: " << orders.size() << endl;

        // 恢复到基线（注意：如果 set_start_bound(mid>0) 成功时把 base_edges 更新为含 bound 的基线，
        // restore_base() 不会移除 bound）
        sdc.restore_base();
        bool conflict = false;

        for (auto [i, j] : orders) {
            // start(j) >= start(i) + sep  =>  x_i - x_j <= -sep
            int sep = std::max(dfg->stmts[i]->op->latency, 1);
            bool no_neg = sdc.solve(i, j, -sep);
            if (!no_neg) {
                out << "[SDC] Conflict with order (" << i << " -> " << j
                    << "), forbidding this order and retrying SAT." << endl;
                // 这里保留你原来的做法：forbid 单条 order（注意：如前讨论，这可能过强；可用 blocking clause 替代）
                sat.forbid_order(i, j);
                conflict = true;
                break;
            }
        }

        if (!conflict) {
            out << "[SDC] All orders accepted";
            if (mid > 0) out << " under bound=" << mid;
            out << ", extracting schedule..." << endl;
            vector<int> sc;
            sdc.get_start_cycles(sc);
            out_sc = sc;
            for (int i = 0; i < n; ++i) {
                out << "[SCHEDULE] Stmt " << i << " : start_cycle = " << sc[i] << endl;
            }
            return true;
        }

        // 若 conflict，则回到 while 重试 SAT（sat 已被 forbid 修改，会在下一轮反映）
    }

    // unreachable
    return false;
}

static int compute_upper_bound(DFG* dfg) {
    int hi = 0;
    for (auto *st : dfg->stmts) {
        int lat = st->op->latency;
        hi += (lat > 0 ? lat : 1);
    }
    return std::max(hi, 1);
}

void schedule(DFG* dfg, const std::vector<Op*>& ops,
              const std::vector<Constr*>& constrs, double clock_period) {

    int n = dfg->stmts.size();
    if (n == 0) return;

    // 覆盖旧的 schedule.log
    { ofstream clr("schedule.log"); }

    int l = 1;
    int r = compute_upper_bound(dfg); // 保守默认上界
    int ans = -1;
    std::vector<int> best_sc;
    ofstream slog("schedule.log", ios::app);
    auto& sout = slog.is_open() ? slog : cout;

    // ===== 第一次：不加约束（mid <= 0 表示 skip bound）来求一个可行调度并得到实际上界 =====
    sout << "[SCHEDULE] Running initial unconstrained Joint_Solver to get an upper bound..." << endl;
    std::vector<int> initial_sc;
    bool initial_ok = Joint_Solver(dfg, ops, constrs, clock_period, 0, initial_sc); // mid=0 => no bound
    if (initial_ok && !initial_sc.empty()) {
        // 计算最大 start_cycle 作为 r
        int max_sc = initial_sc[0];
        for (int x : initial_sc) if (x > max_sc) max_sc = x;
        r = max_sc;
        sout << "[SCHEDULE] Initial unconstrained schedule found. upper bound r = " << r << endl;
        best_sc = initial_sc; // 记录先前的可行解（若以后没找到更好可以返回它）
        ans = r;
    } else {
        // 若没有找到初始可行解，保持 r 为保守上界 compute_upper_bound(dfg)
        sout << "[SCHEDULE] Initial unconstrained run failed; fallback r = " << r << endl;
    }

    // ===== 二分搜索最小 makespan =====
    while (l <= r) {
        int mid = (l + r) / 2;
        sout << "[SCHEDULE] Try mid = " << mid << endl;
        std::vector<int> sc;
        bool ok = Joint_Solver(dfg, ops, constrs, clock_period, mid, sc); // mid>0 -> set_start_bound enforced
        if (ok) {
            // 成功：记录解并缩小上界
            sout << "[SCHEDULE] mid = " << mid << " feasible" << endl;
            ans = mid;
            best_sc = sc;
            r = mid - 1;
        } else {
            sout << "[SCHEDULE] mid = " << mid << " infeasible" << endl;
            l = mid + 1;
        }
    }

    // 写最终结果
    if (!best_sc.empty()) {
        sout << "\n[RESULT] minimal start bound = " << ans << endl;
        for (int i = 0; i < n; ++i) {
            dfg->stmts[i]->start_cycle = best_sc[i];
            sout << "[SCHEDULE] Stmt " << i << " start=" << best_sc[i] << endl;
        }
    } else {
        sout << "\n[RESULT] no feasible schedule" << endl;
    }
}