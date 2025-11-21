#include "common.h"
#include <cstdio>
#include <cstring>
#include <string>

int main(int argc, char** argv) {
    if (argc < 3) {
        printf("Usage: %s path/to/dfg path/to/ops path/to/constr [path/to/schedule]", argv[0]);
        exit(1);
    }

    FILE* dfg_file = fopen(argv[1], "r");
    FILE* op_file = fopen(argv[2], "r");
    FILE* constr_file = fopen(argv[3], "r");

    FILE* schedule_file;
    if (argc >= 5) {
        schedule_file = fopen(argv[4], "w");
    } else {
        schedule_file = stdout;
    }

    fflush(stdout);
    DFG dfg;
    std::vector<Op*> ops;
    std::vector<Constr*> constrs;
    double clock_period;

    parse(dfg_file, op_file, constr_file, &dfg, ops, constrs, clock_period);

    schedule(&dfg, ops, constrs, clock_period);

    for (Stmt* stmt : dfg.stmts) {
        fprintf(schedule_file, "%d\n", stmt->start_cycle);
    }
}
