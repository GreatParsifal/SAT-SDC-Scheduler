#pragma once
#include <vector>
#include <iostream>
#include "common.h"

struct Edge {
    int from;
    int to;
    int w; // x_to - x_from <= w
};

class SDC {
public:
    SDC(DFG* dfg,
        const std::vector<Op*>& ops,
        const std::vector<Constr*>& constrs,
        double clock_period,
        std::ostream& out_
        );    

    void init();

    bool bellman_ford_with_detection(std::vector<int>& out_dist);

    bool solve(int u, int v ,int c);

    bool has_negative_cycle(const std::vector<int>& d);

    const std::vector<int>& get_dist() const { return dist; }

    void add_edge(int from, int to, int w);

    void restore_base();

    void get_start_cycles(std::vector<int>& sc) const;

    bool set_start_bound(int L);      // 约束: start_i <= L
    void clear_start_bound();
private:
    DFG* dfg;
    const std::vector<Op*>& ops;
    const std::vector<Constr*>& constrs;
    double clock_period;
    std::ostream& out;

    int n;                      // 变量个数 = stmt 数
    int super_idx;
    int total_n;
    bool bound_active;
    int bound_value;

    std::vector<Edge> edges;    
    std::vector<int> dist;
    
    vec2d<int> deps;
    vec2d<int> uses;

    std::vector<Edge> base_edges;
    std::vector<int> base_dist;
};