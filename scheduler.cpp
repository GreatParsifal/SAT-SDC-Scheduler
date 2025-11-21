#include "common.h"
#include "SDC.h"
#include "SAT.h"
#include "minisat/core/Solver.h"
#include <iostream>
#include <fstream>
#include <unordered_map>

using namespace std;

void schedule(DFG* dfg, const std::vector<Op*>& ops,
              const std::vector<Constr*>& constrs, double clock_period) {
    int n = dfg->stmts.size();
    if (n == 0) return;

    // 打开日志文件
    ofstream log("sched.log");
    if (!log) {
        // 打不开日志就退回到标准输出
        // 也可以直接 return，看你需求
        cerr << "Failed to open sched.log, fallback to stdout\n";
    }

    auto& out = log.is_open() ? log : cout;  // 统一用 out 写日志
    //auto& out = cout;
    for (int i = 0; i < n; ++i) out << "[DFG] Stmt " << i << ": " << dfg->stmts[i]->op->name << endl;

    SDC sdc(dfg, ops, constrs, clock_period, out);
    sdc.init();

    unordered_map<int, vector<int>> res_to_stmts;
    unordered_map<int, vector<int>> mem_to_stmts;
    int ports = 0;
    for (int i = 0; i < n; ++i) {
        Stmt* stmt = dfg->stmts[i];
        Op* op = stmt->op;
        const string& name = op->name;
        if (stmt->is_mem_stmt()) {
            int mem_id = stmt->get_arr_idx();
            mem_to_stmts[mem_id].push_back(i);
            ports = op->limit;
        }
        res_to_stmts[op->idx].push_back(i);
    }

    SAT sat(n);

    for (auto &kv : res_to_stmts) {
        int op_idx = kv.first;
        const vector<int> &group = kv.second;

        Op* rop = ops[op_idx];
        int limit = rop->limit;
        if (limit < 0) continue;  // 不限资源不编码

        out << "[SAT] encode resource type " << op_idx;
        out << " : size=" << group.size()
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


    while (true) {
        bool sat_ok = sat.solve();
        out << "[SAT] SAT solve result: " << (sat_ok ? "SAT" : "UNSAT") << endl;
        if (!sat_ok) {
            out << "[SAT] UNSAT: no feasible resource schedule under current constraints." << endl;
            break;
        }

        vector<pair<int,int>> orders;
        sat.get_true_orders(orders);
        out << "[SAT] Number of true orders: " << orders.size() << endl;

        sdc.restore_base();
        bool conflict = false;

        for (auto [i, j] : orders) {
            // start(j) >= start(i) + 1  =>  x_i - x_j <= -1
            int sep = std::max(dfg->stmts[i]->op->latency, 1);
            bool no_neg = sdc.solve(i, j, -sep);out << i << " " << j << endl;
            if (!no_neg) {
                out << "[SDC] Conflict with order (" << i << " -> " << j
                    << "), forbidding this order and retrying SAT." << endl;
                sat.forbid_order(i, j);
                conflict = true;
                break;
            }
        }

        if (!conflict) {
            out << "[SDC] All orders accepted, extracting schedule..." << endl;
            vector<int> sc;
            sdc.get_start_cycles(sc);
            for (int i = 0; i < n; ++i) {
                dfg->stmts[i]->start_cycle = sc[i];
                out << "[SCHEDULE] Stmt " << i << " : start_cycle = " << sc[i] << endl;
            }
            break;
        }
    }
}