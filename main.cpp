#include <iostream>
#include <fstream>
#include <vector>
#include <unordered_set>
#include <set>
#include "z3++.h"

using namespace z3;

const int N = 3;
const int twoN = 2 * N;
const int C = 1;
const int M = 3;
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

expr phi_consistent_p1(context & c) {
    //Cth index is C+1th clause
    expr f1 = c.bool_val(true);
    for (int i = C; i < M; i++) {
        expr f2 = c.bool_val(false);
        for (int j = 0; j < i; j++) {
            for (int jp = 0; jp < i; jp++) {
                if (j != jp) {
                    //Equivalence part of formula
                    expr f3l = c.bool_val(true);
                    for (int l : literals) {
                        expr orForm = (*clauseVars[j])[encodeLiteral(l)] || (*clauseVars[jp])[encodeLiteral(l)];
                        expr andForm = !((*clauseVars[j])[encodeLiteral(-l)]) && !((*clauseVars[jp])[encodeLiteral(l)]);
                        expr combForm = orForm && andForm;
                        expr equivForm = equivalent((*clauseVars[i])[encodeLiteral(l)], combForm);
                        f3l = f3l && equivForm;
                    }
                    //literal and -literal in the two
                    expr f3v = c.bool_val(false);
                    for (int v : vars) {
                        expr temp = ((*clauseVars[j])[encodeLiteral(v)]) && ((*clauseVars[jp])[encodeLiteral(-v)]);
                        f3v = f3v || temp;
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

int main() {
    std::ifstream infile("isat10.cnf");
    int a, b, c, d;
    while (infile >> a >> b >> c >> d) {
        std::set<int> temp({a, b, c});
        inputClauses.push_back(temp);
    }
    //Formula* p_cons = phi_consistent();
    //Formula* p_empty = phi_empty();

//    Formula* phi_temp = new AndFormula(p_init, p_cons);

//    std::cout << "Reached 1" << std::endl;
//    Formula* phi = new AndFormula(phi_temp, p_empty);
//    std::cout << "Reached 2" << std::endl;

    context con;
    populateLiterals();
    for (int i = 0; i < M; i++) {
        auto *clause_i= new expr_vector(con);
        for (int l : literals) {
            std::string name = getKey(i, l);
            auto in = con.bool_const(name.c_str());
            std::cout << in << std::endl;
            clause_i->push_back(in);
        }
        clauseVars.push_back(clause_i);
    }
    expr p_init = phi_init(con);
    expr p_cons = phi_consistent(con);
    expr p_empty = phi_empty(con);
    expr phi = p_init && p_cons && p_empty;

//    expr phi_expr = p_init;// && phi_cons_expr && phi_empty_expr;
    solver s(con);
    std::cout << phi << std::endl;
    std::cout << s << "\n";
    std::cout << s.to_smt2() << "\n";
    switch (s.check()) {
        case unsat:   std::cout << "UNSAT\n"; break;
        case sat:     std::cout << "SAT\n"; break;
        case unknown: std::cout << "unknown\n"; break;
    }
//    model m = s.get_model();
//    for (int i = 0; i < M; i++) {
//        for (int l : literals) {
//            expr z3_expr = clauseVars[i][encodeLiteral(l)];
//            if (z3_expr.bool_value() == Z3_L_TRUE) {
//                std::cout << l;
//            }
//        }
//        std::cout << "\n\n";
//    }

    //std::ofstream myfile;
    //myfile.open("out.cnf");
    //myfile << p_init;
    //myfile << p_cons;
    //myfile << p_empty;
    //myfile.close();
    infile.close();
//    std::cout << "Reached 3" << std::endl;
//    delete p_init;
//    std::cout << "Reached 4" << std::endl;
//    delete p_cons;
//    std::cout << "Reached 5" << std::endl;
//    delete p_empty;
    for (auto i : clauseVars) {
        delete i;
    }
    std::cout << "Reached 6" << std::endl;
//    delete phi;
    return 0;
}
