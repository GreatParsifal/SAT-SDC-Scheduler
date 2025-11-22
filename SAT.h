#pragma once
#include "common.h"
#include <minisat/core/Solver.h>
#include <vector>
#include <iostream>

class SAT {
public:
    SAT(int n_ops,std::ostream& out_);

    void encode_resource(const std::vector<int>& ops_idx, int limit,
                     const std::vector<int>* LB = nullptr,
                     const std::vector<int>* UB = nullptr,
                     const std::vector<int>* DUR = nullptr);

    bool solve();

    bool is_before(int i, int j) const;

    void forbid_order(int i, int j);

    void get_true_orders(std::vector<std::pair<int, int>>& orders) const;
private:
    int n;
    Minisat::Solver solver;
    std::ostream& out;

    std::vector<std::vector<Minisat::Var>> before;

    std::vector<std::vector<Minisat::Var>> B; // B_ik
    std::vector<std::vector<Minisat::Var>> R; // R_ij
};