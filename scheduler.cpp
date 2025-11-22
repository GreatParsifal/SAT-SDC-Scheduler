#include "common.h"
#include "SDC.h"
#include "SAT.h"
#include "minisat/core/Solver.h"
#include <iostream>
#include <fstream>
#include <unordered_map>

using namespace std;

bool Joint_Solver(DFG* dfg, const std::vector<Op*>& ops,
              const std::vector<Constr*>& constrs, double clock_period, int mid, std::vector<int>& out_sc) {
    int n = dfg->stmts.size();
    if (n == 0) return false;

    // 打开日志文件（append 模式或新建由上层决定）
    ofstream log("joint.log");
    if (!log) {
        cerr << "Failed to open sched.log, fallback to stdout\n";
    }
    auto& out = log.is_open() ? log : cout;

    out << "\n[JOINT] Trying makespan mid = " << mid << "\n";
    for (int i = 0; i < n; ++i) out << "[DFG] Stmt " << i << ": " << dfg->stmts[i]->op->name << endl;

    // SDC 初始化
    SDC sdc(dfg, ops, constrs, clock_period, out);
    sdc.init();

    // 启用上界（若立即不可行，直接返回 false）
    if (!sdc.set_start_bound(mid)) {
        out << "[SDC] set_start_bound(" << mid << ") failed (negative cycle). prune this mid.\n";
        return false;
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

    SAT sat(n);

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
        sat.encode_resource(group, limit);
    }

    for (auto &kv : mem_to_stmts) {
        int mem_id = kv.first;
        const vector<int> &group = kv.second;
        int limit = ports;
        out << "[SAT] encode memory resource mem_id=" << mem_id
            << " : size=" << group.size()
            << " ports=" << limit << endl;
        sat.encode_resource(group, limit);
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

        // 恢复到基线（注意：如果 set_start_bound 成功时把 base_edges 更新为含 bound 的基线，
        // restore_base() 不会移除 bound）
        sdc.restore_base();
        bool conflict = false;

        for (auto [i, j] : orders) {
            // start(j) >= start(i) + sep  =>  x_i - x_j <= -sep
            int sep = std::max(dfg->stmts[i]->op->latency, 1);
            //out << "[ORDER] try enforce: " << i << " -> " << j << " sep=" << sep << endl;
            bool no_neg = sdc.solve(i, j, -sep);
            if (!no_neg) {
                out << "[SDC] Conflict with order (" << i << " -> " << j
                    << "), forbidding this order and retrying SAT." << endl;
                sat.forbid_order(i, j);
                conflict = true;
                break;
            }
        }

        if (!conflict) {
            out << "[SDC] All orders accepted under bound=" << mid << ", extracting schedule..." << endl;
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
    { ofstream clr("schedule.log"); }

    int l = 1;
    int r = compute_upper_bound(dfg);
    int ans = -1;
    std::vector<int> best_sc;
    ofstream slog("schedule.log", ios::app);
    auto& sout = slog.is_open() ? slog : cout;

    while (l <= r) {
        int mid = (l + r) / 2;
        std::vector<int> sc;
        sout << "[JOINT] Trying makespan mid = " << mid << endl;
        bool ok = Joint_Solver(dfg, ops, constrs, clock_period, mid, sc);
        if (ok) {
            ans = mid;
            best_sc = sc;
            r = mid - 1;
        } else {
            l = mid + 1;
        }
    }



    if (!best_sc.empty()) {
        sout << "\n[RESULT] minimal start bound = " << ans << "\n";
        for (int i = 0; i < n; ++i) {
            dfg->stmts[i]->start_cycle = best_sc[i];
            sout << "[SCHEDULE] Stmt " << i << " start=" << best_sc[i] << "\n";
        }
    } else {
        sout << "\n[RESULT] no feasible schedule\n";
    }
}
