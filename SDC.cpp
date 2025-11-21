#include "SDC.h"
#include <limits>
#include <queue>
#include <cmath>
#include <iostream>
#include <fstream>

using namespace std;

SDC::SDC(DFG* dfg_,
         const std::vector<Op*>& ops_,
         const std::vector<Constr*>& constrs_,
         double clock_period_,
         std::ostream& out_
         )
    : dfg(dfg_),
      ops(ops_),
      constrs(constrs_),
      clock_period(clock_period_),
      out(out_)
    {
    n = dfg->stmts.size();
    dist.assign(n, 0);
    edges.assign(10000, {0,0,0});
    base_edges.assign(10000, {0,0,0});
    base_dist.assign(n, 0);
}

void SDC::add_edge(int from, int to, int w) {
    out << "SDC Edge: " << from << " -> " << to << " , w=" << w << " ";
    edges.push_back({from, to, w});
}

void SDC::init() {
    edges.clear();

    // 1. 获取依赖关系
    get_deps_and_uses(dfg, deps, uses);

    // —— 用于组合链路累积检测的工具函数 ——
    auto get_latency = [&](int x) -> int {
        return dfg->stmts[x]->op->latency;
    };
    auto get_delay = [&](int x) -> double {
        return dfg->stmts[x]->op->delay;
    };

    // 以“起点逻辑 s”和其直接后继 first 作为起链对，先判断 s+first，
    // 若可同周期，则继续从 first 向后做累积；超过 Tclk 则对 v -> s 加边 1
    auto chain_from_pair = [&](int s, int first) {
        const double T = clock_period;
        const double INF_D = std::numeric_limits<double>::infinity();

        double acc0 = get_delay(s) + get_delay(first);
        if (acc0 > T) {
            // s 与 first 本身不能同周期
            if(get_latency(s) > 0) add_edge(first, s, -get_latency(s));
            else add_edge(first, s, -1);
            return;
        }
        else{
            if(get_latency(s) > 0) add_edge(first, s, -get_latency(s) + 1);
            else add_edge(first, s, 0);
        }

        std::vector<double> best(n, INF_D);
        best[first] = acc0;

        std::queue<int> q;
        q.push(first);

        while (!q.empty()) {
            int u = q.front(); q.pop();
            for (int v : uses[u]) {
                if (get_latency(v) > 0) continue;
                double acc = best[u] + get_delay(v);
                if (acc <= T) {
                    if (acc < best[v]) {
                        best[v] = acc;
                        q.push(v);
                        add_edge(v, s, 0);
                    }
                } else {
                    // v 与起点 s 不能同周期
                    if(get_latency(s) > 0)
                        add_edge(v, s, -get_latency(s));
                    else
                        add_edge(v, s, -1);
                }
            }
        }
    };

    // 2. 根据依赖 + latency + delay/period 建 SDC 边
    for (int i = 0; i < n; ++i) {
        Stmt* si = dfg->stmts[i];
        Op* opi = si->op;
        int    lat_i   = opi->latency;
        double delay_i = opi->delay;
        out << "[SDC] Stmt " << i << " uses: ";
        for (int j : uses[i]) { // i -> j
            out << j << " ";
            Stmt* sj = dfg->stmts[j];
            Op* opj = sj->op;
            int    lat_j   = opj->latency;
            double delay_j = opj->delay;

            // (1) latency 约束：start(j) >= start(i) + delta
            if  (lat_i > 0 && lat_j > 0) {
                add_edge(j, i, -lat_i);
            }
            else if (lat_i > 0 && lat_j == 0) {
                chain_from_pair(i, j);
            }
            else if (lat_i == 0 && lat_j > 0) {
                add_edge(j, i, -1);
            }
            else {
                chain_from_pair(i, j);
            }
        }
        out << endl;
    }

    // 3. 额外约束：start(o0) - start(o1) <= diff
    for (auto c : constrs) {
        int o0 = c->op_0;
        int o1 = c->op_1;
        int d  = c->difference;
        // x[o0] - x[o1] <= d  => edge: from=o1, to=o0, w=d
        add_edge(o1-1, o0-1, d);
        out << endl;
    }

    // 4. 跑 Bellman-Ford
    const int INF = std::numeric_limits<int>::max() / 4;

    std::fill(dist.begin(), dist.end(), 0);

    bool updated = true;
    for (int it = 0; it < n - 1 && updated; ++it) {
        updated = false;
        for (const auto& e : edges) {
            int u = e.from;
            int v = e.to;
            int w = e.w;
            if (dist[u] != INF && dist[v] > dist[u] + w) {
                dist[v] = dist[u] + w;
                updated = true;
            }
        }
    }
    for(int i = 0; i < n; i++){
        out << "dist" << i << "=" << dist[i]<<endl;
    }
    base_edges = edges;
    base_dist = dist;
}

bool SDC::has_negative_cycle(const std::vector<int>& d) {
    const int INF = std::numeric_limits<int>::max() / 4;
    for (const auto& e : edges) {
        int u = e.from;
        int v = e.to;
        int w = e.w;
        if (d[u] == INF) continue;          // 不可达的点忽略
        if (d[v] > d[u] + w) {
            // 违反 x_v - x_u <= w
            return true;
        }
    }
    return false;
}

void SDC::restore_base() {
    edges = base_edges;
    dist = base_dist;
}
bool SDC::bellman_ford_with_detection(std::vector<int>& out_dist) {
    const long long INFLL = std::numeric_limits<long long>::max() / 4;
    int N = n;
    // 我们将做标准的 Bellman-Ford：先把所有 d = 0，并在 edges 上松弛 N 次
    // 更稳妥的做法是引入一个 super-node s'，并把 s'->i 的边加入（weight 0），
    // 然后对 N (or N+1) 个节点跑 BF。为简单，我们用 d[i]=0 的方式（等价）。
    std::vector<long long> d(N, 0); // 注意：所有 0 是安全的，用于检测任意负环

    // 我们做 N-1 轮松弛（标准），然后第 N 轮检测负环
    for (int it = 0; it < N - 1; ++it) {
        bool updated = false;
        for (const auto &e : edges) {
            int u = e.from;
            int v = e.to;
            long long w = (long long)e.w;
            if (d[v] > d[u] + w) {
                d[v] = d[u] + w;
                updated = true;
            }
        }
        if (!updated) break;
    }

    // 第 N 轮检测：若还有被松弛的边则存在负环
    for (const auto &e : edges) {
        int u = e.from;
        int v = e.to;
        long long w = (long long)e.w;
        if (d[v] > d[u] + w) {
            return false; // 发现负环
        }
    }

    // 无负环：我们需要构造一个满足约束的 out_dist。
    // d 现在是某个可行解（不一定是最小），但满足所有 x_v - x_u <= w。
    // 为兼容现有类型（int），把 long long clamp 到 int 范围（保持语义）
    out_dist.assign(N, 0);
    const long long CLAMP = std::numeric_limits<int>::max() / 4;
    for (int i = 0; i < N; ++i) {
        long long val = d[i];
        if (val <= -CLAMP) out_dist[i] = (int)(-CLAMP);
        else if (val >= CLAMP) out_dist[i] = (int)(CLAMP);
        else out_dist[i] = (int)val;
    }
    return true;
}

// 修正后的 solve：实现你的增量伪代码（Edmonds-Karp-length 风格），但用超源 BF 做安全检测/回退
bool SDC::solve(int u, int v, int c) {
    // 1) 在 edges 中添加新约束 v -> u (weight c)
    add_edge(v, u, c);

    const long long INFLL = std::numeric_limits<long long>::max() / 4;
    const int INF = std::numeric_limits<int>::max() / 4;

    // 2) 准备势能 V（等于当前 dist）
    std::vector<int> V = dist; // 当前势能（旧的可行解）

    // 3) 检查重权能否满足（即对所有边 cp = w + V[from] - V[to] >= 0）
    bool cp_all_nonneg = true;
    for (const auto &e : edges) {
        int from = e.from;
        int to   = e.to;
        int w    = e.w;
        // 如果某个节点的势能被标记为 INF（不可达），则不能用重权技巧
        if (V[from] == INF || V[to] == INF) {
            cp_all_nonneg = false;
            break;
        }
        long long cp = (long long)w + (long long)V[from] - (long long)V[to];
        if (cp < 0) {
            cp_all_nonneg = false;
            break;
        }
    }

    // 4) 若重权检查失败，直接用超源 Bellman-Ford 求解（安全）
    if (!cp_all_nonneg) {
        std::vector<int> bf_dist;
        bool ok = bellman_ford_with_detection(bf_dist);
        if (!ok) {
            // 发现负环，回滚并返回 false
            edges = base_edges;
            dist = base_dist;
            return false;
        } else {
            // BF 给出一个合法解，接受并返回 true
            dist = bf_dist;
            return true;
        }
    }

    // 5) 重权通过：构建重权图邻接表并用 Dijkstra 从 v 出发（增量松弛）
    struct AdjEdge { int to; int w; };
    std::vector<std::vector<AdjEdge>> adj(n);
    for (const auto &e : edges) {
        int from = e.from;
        int to   = e.to;
        int w    = e.w;
        long long cp_ll = (long long)w + (long long)V[from] - (long long)V[to];
        int cp;
        if (cp_ll > std::numeric_limits<int>::max() / 4) cp = std::numeric_limits<int>::max() / 4;
        else cp = (int)cp_ll;
        adj[from].push_back({to, cp});
    }

    // dprime 存重权图上从 v 出发到各点的距离（int 使用 INF）
    std::vector<int> dprime(n, INF);
    int s = v;
    dprime[s] = 0;
    using P = std::pair<int,int>;
    std::priority_queue<P, std::vector<P>, std::greater<P>> pq;
    pq.push({0, s});

    while (!pq.empty()) {
        auto [du, node] = pq.top(); pq.pop();
        if (du != dprime[node]) continue;
        for (const auto &ed : adj[node]) {
            int to = ed.to;
            int w  = ed.w;
            if (dprime[to] > dprime[node] + w) {
                dprime[to] = dprime[node] + w;
                pq.push({dprime[to], to});
            }
        }
    }

    // 6) 用 dprime 还原到原尺度并构造 candidate，更新 dist（注意 clamp）
    int Du = dist[u];
    int Vv = V[v];
    for (int x = 0; x < n; ++x) {
        if (dprime[x] == INF) continue; // v -> x 不可达，跳过
        long long dvx_ll = (long long)dprime[x] + (long long)V[x] - (long long)Vv;
        long long candidate_ll = (long long)Du + dvx_ll + (long long)c;
        if (candidate_ll < -INF) candidate_ll = -INF;
        if (candidate_ll >  INF) candidate_ll =  INF;
        int candidate = (int)candidate_ll;
        if (candidate < dist[x]) dist[x] = candidate;
    }

    // 7) 最后做一个超源 BF 验证（可选但安全）：若 BF 发现负环则回滚
    std::vector<int> bf_check;
    if (!bellman_ford_with_detection(bf_check)) {
        edges = base_edges;
        dist = base_dist;
        return false;
    } else {
        // 采用 BF 给出的全局一致解（更稳妥）
        dist = bf_check;
        return true;
    }
}
/* bool SDC::solve(int u, int v, int c) {
    
    add_edge(v, u, c);

    const int INF = std::numeric_limits<int>::max() / 4;

    std::vector<int> V = dist;

    struct AdjEdge {
        int to;
        int w;
    };
    
    std::vector<std::vector<AdjEdge>> adj(n);
    for (const auto& e : edges) {
        int from = e.from;
        int to   = e.to;
        int w    = e.w;
        int cp = w + V[from] - V[to];
        adj[from].push_back({to, cp});
    }
    out << 1 << endl;
    std::vector<int> dprime(n, INF);
    int s = v;
    dprime[s] = 0;
    using P = std::pair<int, int>;
    std::priority_queue<P, std::vector<P>, std::greater<P>> pq;
    pq.push({0, s});
    
    while (!pq.empty()) {
        auto [dist_u, u] = pq.top();
        pq.pop();
        if (dist_u != dprime[u]) continue;

        for (const auto& e : adj[u]) {
            int to = e.to;
            int w  = e.w;
            if (dprime[to] > dprime[u] + w) {
                dprime[to] = dprime[u] + w;
                pq.push({dprime[to], to});
            }
        }
    }
    out << 2 << endl;
    int Du = dist[u];
    int Vv = V[v];

    for (int x = 0; x < n; ++x) {
        if (dprime[x] == INF) {
            // v 到 x 不可达，这条新约束对 x 不产生更紧的上界
            continue;
        }
        int dvx = dprime[x] + V[x] - Vv; // d(v->x)
        int candidate = Du + dvx + c;                           // D(u)+d(v->x)+c

        if (candidate < dist[x]) {
            if (candidate < -INF) candidate = -INF;
            if (candidate >  INF) candidate =  INF;
            dist[x] = (int)candidate;
        }
    }

     if (has_negative_cycle(dist)) {
        
        return false;
    }
    return true;
}*/
void SDC::get_start_cycles(std::vector<int>& sc) const {
    const int INF = std::numeric_limits<int>::max()/4;
    sc = dist;
    for(int i = 0; i < n; i++){
        out  << "dist" << i << "=" << dist[i] << endl;
    }
    if (n == 0) return;

    // 识别参与约束的节点
    std::vector<char> constrained(n, 0);
    for (auto &e : edges) {
        constrained[e.from] = 1;
        constrained[e.to]   = 1;
    }

    // 统计有效最小值（忽略“未约束”并且是 INF 的点）
    bool first = true;
    int mn = 0;
    for (int i = 0; i < n; ++i) {
        if (!constrained[i]) continue; // 不参与边的点延后处理
        if (sc[i] >= INF/2) continue;  // 若以后用 INF 初始化
        if (first) { mn = sc[i]; first = false; }
        else if (sc[i] < mn) mn = sc[i];
    }
    if (first) mn = 0; // 所有点都未约束，统一从 0 开始

    int offset = -mn;
    for (int i = 0; i < n; ++i) {
        if (constrained[i] && sc[i] < INF/2) {
            sc[i] += offset;
        }
    }

    // 为未约束点赋默认周期（这里设为 1；也可以设为最大已用周期+1）
    int max_cycle = 0;
    for (int i = 0; i < n; ++i) {
        if (constrained[i] && sc[i] > max_cycle) max_cycle = sc[i];
    }
    for (int i = 0; i < n; ++i) {
        if (!constrained[i]) sc[i] = 1; // 或 max_cycle+1
        else sc[i] += 1; // 原设计：整体 +1
    }
}

