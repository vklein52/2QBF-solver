#include <iostream>
#include <fstream>
#include <vector>
#include <unordered_set>
#include <set>
#include "z3++.h"

using namespace z3;

const int N = 2;
const int twoN = 2 * N;
const int C = 4;
const int M = 7;
std::vector<std::set<int>> inputClauses;
int literals[twoN];
int vars[N];
std::vector<z3::expr_vector*> clauseVars;

int encodeLiteral(int literal) {
    return ((literal < 0) ? -literal + N : literal) - 1;
}

expr equivalent(expr f1, expr f2) {
    //(f1 & f2) | ((~f1 & ~f2)
    return (f1 && f2) || (!(f1) && !(f2));
}
//
//expr implies(expr f1, expr f2) {
//    return (!f1 || f2);
//}

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
        literals[i+(N-1)] = -i;
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

//expr phi_consistent_p1(context & c) {
//    //Cth index is C+1th clause
//    expr f1 = c.bool_val(true);
//    for (int i = C; i < M; i++) {
//        expr f2 = c.bool_val(false);
//        for (int j = 0; j < i; j++) {
//            for (int jp = 0; jp < i; jp++) {
//                if (j != jp) {
//                    //Equivalence part of formula
//                    expr f3l = c.bool_val(true);
//                    for (int l : literals) {
//                        expr orForm = (*clauseVars[j])[encodeLiteral(l)] || (*clauseVars[jp])[encodeLiteral(l)];
//                        expr andForm = !((*clauseVars[j])[encodeLiteral(-l)]) && !((*clauseVars[jp])[encodeLiteral(l)]);
//                        expr combForm = orForm && andForm;
//                        expr equivForm = equivalent((*clauseVars[i])[encodeLiteral(l)], combForm);
//                        f3l = f3l && equivForm;
//                    }
//                    //literal and -literal in the two
//                    expr f3v = c.bool_val(false);
//                    for (int v : vars) {
//                        expr temp = ((*clauseVars[j])[encodeLiteral(v)]) && ((*clauseVars[jp])[encodeLiteral(-v)]);
//                        f3v = f3v || temp;
//                    }
//                    //Combine the two
//                    expr f3 = f3l && f3v;
//                    f2 = f2 || f3;
//                }
//            }
//        }
//        //And f1 with f1 and f2
//        f1 = f1 && f2;
//    }
//    return f1;
//}

expr phi_consistent_p1(context & c) {
    //Cth index is C+1th clause
    expr f1 = c.bool_val(true);
    for (int i = C; i < M; i++) {
        expr f2 = c.bool_val(false);
        for (int j = 0; j < i; j++) {
            for (int jp = 0; jp < j; jp++) {
                if (j != jp) {
                    //Equivalence part of formula
                    expr f3l = c.bool_val(true);
                    expr f3v = c.bool_val(false);
                    for (int l : literals) {
                        //f3l part
                        expr orForm = (*clauseVars[j])[encodeLiteral(l)] || (*clauseVars[jp])[encodeLiteral(l)];
                        expr andForm = !((*clauseVars[j])[encodeLiteral(-l)]) && !((*clauseVars[jp])[encodeLiteral(-l)]);
                        expr combForm = orForm && andForm;
                        expr equivForm = equivalent((*clauseVars[i])[encodeLiteral(l)], combForm);
                        f3l = f3l && equivForm;
                        //f3v part
                        expr atLeast1 = (
                                            ((*clauseVars[j])[encodeLiteral(l)])
                                            &&
                                            ((*clauseVars[jp])[encodeLiteral(-l)])
                                        )
                                        ||
                                        (
                                                ((*clauseVars[j])[encodeLiteral(-l)]) && ((*clauseVars[jp])[encodeLiteral(l)])
                                        );
                        expr exactly1 = c.bool_val(true);
                        for (int lp : literals) {
                            if (l != lp) {
                                expr tempAnd =
                                        !((*clauseVars[j])[encodeLiteral(-lp)]) && !((*clauseVars[jp])[encodeLiteral(-lp)]);
                                expr temp = implies((*clauseVars[i])[encodeLiteral(lp)], tempAnd);
                                exactly1 = exactly1 && temp;
                            }
                        }
                        expr res = atLeast1 && exactly1;
                        f3v = f3v || res;
                    }

                    //Combine the two
                    expr f3 = f3l && f3v;
                    f2 = f2 || f3;
                }
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
        for (int l : literals) {
            expr tempNot = !(((*clauseVars[i])[encodeLiteral(l)]) && ((*clauseVars[i])[encodeLiteral(-l)]));
            f2 = f2 && tempNot;
        }
        //And f1 with f1 and f2
        f1 = f1 && f2;
    }
    return f1;
}

expr phi_consistent(context & c) {
    expr p1 = phi_consistent_p1(c);
    std::cout << "p1:\n\n" << p1 << std::endl;
    return p1 && phi_consistent_p2(c);
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

expr clause5(context& c) {
    return ((*clauseVars[4])[encodeLiteral(-1)]) && !(((*clauseVars[4])[encodeLiteral(1)])) && !(((*clauseVars[4])[encodeLiteral(-2)])) && !(((*clauseVars[4])[encodeLiteral(2)]));
}

expr clause6(context& c) {
    return ((*clauseVars[5])[encodeLiteral(1)]) && !(((*clauseVars[5])[encodeLiteral(-1)])) && !(((*clauseVars[5])[encodeLiteral(-2)])) && !(((*clauseVars[5])[encodeLiteral(2)]));
}

int main() {
    std::ifstream infile("isat10.cnf");
//    int a, b, c, d;
//    while (infile >> a >> b >> c >> d) {
//        std::set<int> temp({a, b, c});
//        inputClauses.push_back(temp);
//    }
    int a, b, d;
    while (infile >> a >> b >> d) {
        std::set<int> temp({-a, -b});
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

//    expr phi_expr = p_init;// && phi_cons_expr && phi_empty_expr;
    solver s(con);
    s.add(phi);
//    std::cout << phi << std::endl;
//    std::cout << s << "\n";
//    std::cout << s.to_smt2() << "\n";
    std::cout << "Will check satisfiability\n\n";
    switch (s.check()) {
        case unsat:   std::cout << "UNSAT\n"; break;
        case sat:     std::cout << "SAT\n"; break;
        case unknown: std::cout << "unknown\n"; break;
    }
//    std::cout << "Resolution expressions:\n\n";
    model m(con, s.get_model());
    for (int i = 0; i < M; i++) {
        for (int l : literals) {
            expr z3_expr = (*clauseVars[i])[encodeLiteral(l)];
            if (m.eval(z3_expr, false).bool_value() == Z3_L_TRUE) {
                std::cout << l <<", ";
            }
        }
        std::cout << "\n\n";
    }
//    int n = m.num_consts();
//    std::cout << n << std::endl;
//    for (unsigned i = 0; i < n; i++) {
//        expr r = m.get_const_interp(m.get_const_decl(i));
//        std::cout << m.get_const_decl(i) << ", " << r << std::endl;
//    }
    infile.close();
    for (auto i : clauseVars) {
        delete i;
    }
//    delete phi;
    return 0;
}
