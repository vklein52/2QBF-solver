#include <iostream>
#include <fstream>
#include <vector>
#include <unordered_set>
#include <set>
#include "z3++.h"

using namespace z3;

// Num variables
const int N = 3;
const int twoN = 2 * N;
// Num clauses - likely want to extract initialization to the file parsing portion of code
const int C = 8;
// Max clauses generated - needs to be tweaked per file ran on - expression to generate upper bound perhaps?
const int M = 15;

// inputClauses allows us to define all variables that will be used and reduce memory consumption
std::vector<std::set<int>> inputClauses;

std::set<int> xVars, yVars;

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
            auto curr = getClauseVar(i, v);

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
        std::cout << "Generated clause: " << i << " out of " << M << std::endl;
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

expr linear_phi_consistent_p1(context &c) {
    //Cth index is C+1th clause
    expr f1 = c.bool_val(true);
    for (int i = C; i < M; i++) {
        std::cout << "Generated clause: " << i << " out of " << M << std::endl;
        expr f2 = c.bool_val(false);
        for (int j = 0; j < i - 1; j++) {
            int jp = i - 1;
            expr f3 = c.bool_val(false);
            for (int v : vars) {
                expr f3p1 = (getClauseVar(j, v) && getClauseVar(jp, -v))
                            ||
                            (getClauseVar(j, -v) && getClauseVar(jp, v));
                expr f3p2 = c.bool_val(true);
                for (int l : literals) {
                    if (l != v && l != -v) {
                        expr left = getClauseVar(i, l);

                        expr right = (getClauseVar(j, l) || getClauseVar(jp, l));
                        f3p2 = f3p2 && equivalent(left, right);
                    }
                }
                f3 = f3 || (f3p1 && f3p2);
            }
            f2 = f2 || f3;

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

// Could use this instead of phi_consistent - needs larger 'M' and can be slower at times
expr linear_phi_consistent(context &c) {
    return linear_phi_consistent_p1(c) && phi_consistent_p2(c);
}

expr phi_empty(context & c) {
    //ith index is i+1th clause
    auto retVal = c.bool_val(false);
    for (int i = 0; i < M; ++i) {
        auto currAnd = c.bool_val(true);
        for (int l : xVars) {
            auto temp = !((*clauseVars[i])[encodeLiteral(l)]);
            currAnd = currAnd && temp;
        }
        retVal = retVal || currAnd;
    }
    return retVal;
}

void bruteMatchesPBR(const std::string &filename) {
    std::ifstream infile(filename);
    int a, b, c, d;
    while (infile >> a && a != 0) {
        yVars.insert(a);
        yVars.insert(-a);
    }
    while (infile >> a && a != 0) {
        xVars.insert(a);
        xVars.insert(-a);
    }
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
    std::cout << "Generated PHI_INIT" << std::endl;
    expr p_cons = phi_consistent(con);
    // Uncomment following line and comment above to use linear phi_consistent
//    expr lin_p_cons = linear_phi_consistent(con);
    std::cout << "Generated PHI_CONSISTENT" << std::endl;
    expr p_empty = phi_empty(con);
    std::cout << "Generated PHI_EMPTY" << std::endl;
    expr phi = p_init && p_cons && p_empty;

    solver s(con);
    s.add(phi);
    std::cout << "Starting solver" << std::endl;
    check_result PBR = s.check();
    // Uncomment following lines to see debug info - (clauses created) - will cause z3 exception if unsat for any reason
    // i.e. simply unsat, too small M, etc.
//    model m(con, s.get_model());
//    for (int i = 0; i < M; i++) {
//        for (int l : literals) {
//            expr z3_expr = (*clauseVars[i])[encodeLiteral(l)];
//            if (m.eval(z3_expr, false).bool_value() == Z3_L_TRUE) {
//                std::cout << l << ", ";
//            }
//        }
//        std::cout << "\n\n";
//    }
    infile.close();
    for (auto i : clauseVars) {
        delete i;
    }
//    //Now will do brute force method
    std::ifstream brutefile(filename);
    while (infile >> a >> b >> c >> d) {
        std::set<int> temp({a, b, c});
        inputClauses.push_back(temp);
    }
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

    std::cout << "PBR RESULT: ";
    switch (PBR) {
        case unsat:   std::cout << "UNSAT\n"; break;
        case sat:     std::cout << "SAT\n"; break;
        case unknown: std::cout << "unknown\n"; break;
    }
    std::cout << "BRUTE RESULT: ";
    switch (bruteRes) {
        case unsat:   std::cout << "UNSAT\n"; break;
        case sat:     std::cout << "SAT\n"; break;
        case unknown: std::cout << "unknown\n"; break;
    }
}

int main() {
    // 2QBFProofSearch
    bruteMatchesPBR("sat10.cnf");
    return 0;
}
