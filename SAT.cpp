#include "SAT.h"
#include <iostream>

SAT::SAT(int n_ops,std::ostream& out_) : n(n_ops), out(out_) {
    before.resize(n, std::vector<Minisat::Var>(n, Minisat::var_Undef));
    B.clear();
    R.clear();
}

void SAT::encode_resource(const std::vector<int>& ops_idx, int limit,
                          const std::vector<int>* LB,
                          const std::vector<int>* UB,
                          const std::vector<int>* DUR) {
    int m = ops_idx.size();
    int L = limit;
    if (m == 0 || L <= 0) return;

    // B 用全局 stmt idx 做第一维，第二维是实例编号 0..L-1
    if ((int)B.size() != n || (!B.empty() && (int)B[0].size() != L)) {
        B.assign(n, std::vector<Minisat::Var>(L, Minisat::var_Undef));
    }
    // R 同样用全局 i,j
    if ((int)R.size() != n || (!R.empty() && (int)R[0].size() != n)) {
        R.assign(n, std::vector<Minisat::Var>(n, Minisat::var_Undef));
    }

    // 1) 对每个参与此资源的 op_i，建 B_ik 并加 ⋁_k B_ik
    for (int a = 0; a < m; ++a) {
        int i = ops_idx[a];           // 全局 i
        for (int k = 0; k < L; ++k) {
            if (B[i][k] == Minisat::var_Undef)
                B[i][k] = solver.newVar();
        }
        Minisat::vec<Minisat::Lit> clause;
        for (int k = 0; k < L; ++k) {
            clause.push(Minisat::mkLit(B[i][k]));
        }
        solver.addClause(clause);     // ⋁_k B_ik
        // 至多一个
        for (int k1 = 0; k1 < L; ++k1) {
            for (int k2 = k1 + 1; k2 < L; ++k2) {
                solver.addClause(Minisat::mkLit(B[i][k1], true),
                                 Minisat::mkLit(B[i][k2], true));
            }
        }
    }

    // 2) 对每对 (i,j) 做：
    // A_ijk = B_ik ∧ B_jk
    // (¬A_ijk ∨ B_ik) ∧ (¬A_ijk ∨ B_jk) ∧ (A_ijk ∨ ¬B_ik ∨ ¬B_jk)
    // (⋀_k (R_ij ∨ ¬A_ijk)) ∧ (¬R_ij ∨ ⋁_k A_ijk)
    // R_ij → (O_ij ∨ O_ji)
    // ¬(O_ij ∧ O_ji)
    for (int a = 0; a < m; ++a) {
        int i = ops_idx[a];
        for (int b = a + 1; b < m; ++b) {
            int j = ops_idx[b];

            // ---------- LB/UB/DUR 剪枝检查（保守） ----------
            if (LB && UB && DUR) {
                // 检查索引有效性（防御性）
                if ((int)LB->size() > i && (int)LB->size() > j &&
                    (int)UB->size() > i && (int)UB->size() > j &&
                    (int)DUR->size() > i && (int)DUR->size() > j) {
                    int di = (*DUR)[i];
                    int dj = (*DUR)[j];
                    // 保守取 dur >= 1，如果输入可能为0，确保最小为1
                    if (di <= 0) di = 1;
                    if (dj <= 0) dj = 1;
                    // 判定：若 i 在其最晚开始并完成仍不影响 j 的最早开始，
                    // 或 j 在其最晚开始并完成仍不影响 i 的最早开始，
                    // 则两者无重叠可能，可以跳过对它们的 ordering 编码。
                    if ( (*UB)[i] + di <= (*LB)[j] || (*UB)[j] + dj <= (*LB)[i] ) {
                        // debug 输出，便于观测剪枝效果；需要时删掉或改为日志记录
                        out << "[SAT] prune pair (i=" << i << ", j=" << j
                                  << ") by LB/UB/DUR: UB[i]+" << di << "=" << ((*UB)[i] + di)
                                  << " <= LB[j]=" << (*LB)[j] << " OR UB[j]+" << dj
                                  << "=" << ((*UB)[j] + dj) << " <= LB[i]=" << (*LB)[i] << std::endl;
                        continue; // 跳过此对
                    }
                }
                // 若 LB/UB/DUR 尺寸不够或无效，则退回不剪枝
            }

            // R_ij 只创建一次
            if (R[i][j] == Minisat::var_Undef) {
                Minisat::Var Rij = solver.newVar();
                R[i][j] = R[j][i] = Rij;
            }
            Minisat::Var Rij = R[i][j];

            // 为每个 k 创建 A_ijk
            std::vector<Minisat::Var> A_ijk(L);
            for (int k = 0; k < L; ++k) {
                A_ijk[k] = solver.newVar();

                Minisat::Var Bik = B[i][k];
                Minisat::Var Bjk = B[j][k];
                Minisat::Var A   = A_ijk[k];

                // A_ijk → B_ik: (¬A_ijk ∨ B_ik)
                solver.addClause(Minisat::mkLit(A, true),
                                 Minisat::mkLit(Bik));
                // A_ijk → B_jk: (¬A_ijk ∨ B_jk)
                solver.addClause(Minisat::mkLit(A, true),
                                 Minisat::mkLit(Bjk));
                // (B_ik ∧ B_jk) → A_ijk: (A_ijk ∨ ¬B_ik ∨ ¬B_jk)
                solver.addClause(Minisat::mkLit(A),
                                 Minisat::mkLit(Bik, true),
                                 Minisat::mkLit(Bjk, true));
            }

            // ⋀_k (R_ij ∨ ¬A_ijk)
            for (int k = 0; k < L; ++k) {
                solver.addClause(Minisat::mkLit(Rij),
                                 Minisat::mkLit(A_ijk[k], true));
            }

            // (¬R_ij ∨ ⋁_k A_ijk)
            Minisat::vec<Minisat::Lit> clause_R;
            clause_R.push(Minisat::mkLit(Rij, true)); // ¬R_ij
            for (int k = 0; k < L; ++k) {
                clause_R.push(Minisat::mkLit(A_ijk[k]));
            }
            solver.addClause(clause_R);

            // 顺序变量 O_(i->j), O_(j->i)
            if (before[i][j] == Minisat::var_Undef)
                before[i][j] = solver.newVar();
            if (before[j][i] == Minisat::var_Undef)
                before[j][i] = solver.newVar();

            Minisat::Var Oij = before[i][j];
            Minisat::Var Oji = before[j][i];

            // R_ij → (O_ij ∨ O_ji)  === (¬R_ij ∨ O_ij ∨ O_ji)
            solver.addClause(Minisat::mkLit(Rij, true),
                             Minisat::mkLit(Oij),
                             Minisat::mkLit(Oji));

            // ¬(O_ij ∧ O_ji) === (¬O_ij ∨ ¬O_ji)
            solver.addClause(Minisat::mkLit(Oij, true),
                             Minisat::mkLit(Oji, true));
        }
    }
}


////cpp
bool SAT::solve() {
    return solver.solve();
}

bool SAT::is_before(int i, int j) const {
    if (i == j) return false;
    Minisat::Var v = before[i][j];
    if (v == Minisat::var_Undef) return false;
    Minisat::lbool val = solver.modelValue(v);
    return val == Minisat::l_True;
}

void SAT::forbid_order(int i, int j) {
    if (i == j) return;
    Minisat::Var v = before[i][j];
    if (v == Minisat::var_Undef) return;
    // 加子句 (¬O_ij)
    solver.addClause(Minisat::mkLit(v, true));
}

void SAT::get_true_orders(std::vector<std::pair<int,int>>& orders) const {
    orders.clear();
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            if (i == j) continue;
            if (is_before(i, j)) {
                orders.emplace_back(i, j);
            }
        }
    }
}
