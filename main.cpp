#include <iostream>
#include <fstream>
#include <vector>
#include <unordered_set>
#include <set>
#include "z3++.h"

using namespace z3;

const int N = 3;
const int twoN = 2 * N;
const int C = 8;
const int M = 15;
std::vector<std::set<int>> inputClauses;
int literals[twoN];
int vars[N];
std::vector<z3::expr_vector*> clauseVars;

int encodeLiteral(int literal) {
    return ((literal < 0) ? -literal + N : literal) - 1;
}

expr getClauseVar(int c, int l) {
    return (*clauseVars[c])[encodeLiteral(l)];
}

expr equivalent(expr f1, expr f2) {
    //(f1 & f2) | ((~f1 & ~f2)
    return (f1 && f2) || (!(f1) && !(f2));
}
std::string getKey(int c, int v) {
    return std::to_string(c) +  "," + std::to_string(v);
}

const char *getKeyCStr(int c, int v) {
    return getKey(c, v).c_str();
}

//Used for \Phi_init

void populateLiterals() {
    for (int i = 1; i < N+1; i++) {
        literals[i-1] = i;
        literals[(i-1) + N] = -i;
        vars[i-1] = i;
    }
}

expr phi_init(context & c) {
    auto retVal = c.bool_val(true);
    for (int i = 0; i < C; i++) {
        std::set<int> & tempSet = inputClauses[i];
        for (int v : literals) {
            auto curr = (*clauseVars[i])[encodeLiteral(v)];
            if (tempSet.find(v) == tempSet.end()) {
                //v does not exist in clause
                curr = !curr;
            }
            retVal = retVal && curr;
        }
    }
    return retVal;
}

expr phi_consistent_p1(context & c) {
    //Cth index is C+1th clause
    expr f1 = c.bool_val(true);
    for (int i = C; i < M; i++) {
        expr f2 = c.bool_val(false);
        for (int j = 0; j < i; j++) {
            for (int jp = 0; jp < j; jp++) {
                expr f3 = c.bool_val(false);
                for (int v : vars) {
                    expr f3p1 = (getClauseVar(j, v) && getClauseVar(jp, -v))
                                ||
                                (getClauseVar(j, -v) && getClauseVar(jp, v));
                    expr f3p2 = c.bool_val(true);
                    for (int l : literals) {
                        if (l != v && l != -v) {
                            expr left = getClauseVar(i, l);
//                            expr right = (getClauseVar(j, l) && !getClauseVar(jp, -l))
//                                         ||
//                                         (getClauseVar(jp, l) && !getClauseVar(j, -l));

                            expr right = (getClauseVar(j, l) || getClauseVar(jp, l));
                            f3p2 = f3p2 && equivalent(left, right);
                        }
                    }
                    f3 = f3 || (f3p1 && f3p2);
                }
                f2 = f2 || f3;
            }
        }
        //And f1 with f1 and f2
        f1 = f1 && f2;
    }
    return f1;
}

expr phi_consistent_p2(context & c) {
    expr f1 = c.bool_val(true);
    for (int i = 0; i < M; i++) {
        expr f2 = c.bool_val(true);
        for (int v : vars) {
            expr tempNot = !(((*clauseVars[i])[encodeLiteral(v)]) && ((*clauseVars[i])[encodeLiteral(-v)]));
            f2 = f2 && tempNot;
        }
        //And f1 with f1 and f2
        f1 = f1 && f2;
    }
    return f1;
}

expr phi_consistent(context & c) {
    return phi_consistent_p1(c) && phi_consistent_p2(c);
}

expr phi_empty(context & c) {
    //ith index is i+1th clause
    auto retVal = c.bool_val(false);
    for (int i = 0; i < M; ++i) {
        auto currAnd = c.bool_val(true);
        for (int l : literals) {
            auto temp = !((*clauseVars[i])[encodeLiteral(l)]);
            currAnd = currAnd && temp;
        }
        retVal = retVal || currAnd;
    }
    return retVal;
}

bool bruteMatchesPBR(const std::string &filename) {
    std::ifstream infile(filename);
//    int a, b, c, d;
//    while (infile >> a >> b >> c >> d) {
//        std::set<int> temp({a, b, c});
//        inputClauses.push_back(temp);
//    }
    int a, b, c, d;
    while (infile >> a >> b >> c >> d) {
        std::set<int> temp({-a, -b, -c});
        inputClauses.push_back(temp);
    }
    context con;
    populateLiterals();
    for (int i = 0; i < M; i++) {
        auto *clause_i= new expr_vector(con);
        for (int l : literals) {
            std::string name = getKey(i, l);
            auto in = con.bool_const(name.c_str());
            clause_i->push_back(in);
        }
        clauseVars.push_back(clause_i);
    }
    //Populated all clause variables
    expr p_init = phi_init(con);
    expr p_cons = phi_consistent(con);
    expr p_empty = phi_empty(con);
    expr phi = p_init && p_cons && p_empty;

    solver s(con);
    s.add(phi);
    check_result PBR = s.check();
    model m(con, s.get_model());
    for (int i = 0; i < M; i++) {
        for (int l : literals) {
            expr z3_expr = (*clauseVars[i])[encodeLiteral(l)];
            if (m.eval(z3_expr, false).bool_value() == Z3_L_TRUE) {
                std::cout << l << ", ";
            }
        }
        std::cout << "\n\n";
    }
    infile.close();
    for (auto i : clauseVars) {
        delete i;
    }
    //Now will do brute force method
    std::ifstream brutefile(filename);
//    int a, b, c, d;
//    while (infile >> a >> b >> c >> d) {
//        std::set<int> temp({a, b, c});
//        inputClauses.push_back(temp);
//    }
    context bruteCon;
    expr brute = bruteCon.bool_val(true);
    int bClauseNum = 0;
    while (brutefile >> a >> b >> c >> d) {
        expr temp1 = (a > 0) ? (bruteCon.bool_const(std::to_string(a).c_str())) : !(bruteCon.bool_const(std::to_string(-a).c_str()));
        expr temp2 = (b > 0) ? (bruteCon.bool_const(std::to_string(b).c_str())) : !(bruteCon.bool_const(std::to_string(-b).c_str()));
        expr temp3 = (c > 0) ? (bruteCon.bool_const(std::to_string(c).c_str())) : !(bruteCon.bool_const(std::to_string(-c).c_str()));
        brute = brute && !(temp1 && temp2 && temp3);
        bClauseNum++;
    }
    solver bruteS(bruteCon);
    bruteS.add(brute);
    check_result bruteRes = bruteS.check();
    brutefile.close();
    std::cout << brute << std::endl;
    switch (PBR) {
        case unsat:   std::cout << "UNSAT\n"; break;
        case sat:     std::cout << "SAT\n"; break;
        case unknown: std::cout << "unknown\n"; break;
    }
    switch (bruteRes) {
        case unsat:   std::cout << "UNSAT\n"; break;
        case sat:     std::cout << "SAT\n"; break;
        case unknown: std::cout << "unknown\n"; break;
    }
}

int main() {
    //TODO: create func that reads DNF input, negates, checks sat, and should say unsat when we say sat
    // 2QBFProofSearch
    bruteMatchesPBR("sat10.cnf");
//    delete phi;
    return 0;
}
