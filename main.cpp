#include <iostream>
#include <string>
#include <fstream>
#include <vector>
#include <unordered_set>
#include <set>
#include "Formulas/Formula.h"
#include "Formulas/VarFormula.h"
#include "Formulas/NotFormula.h"
#include "Formulas/AndFormula.h"
#include "Formulas/OrFormula.h"
#include "Formulas/FormulaHelper.h"

const int N = 100;
const int twoN = 2 * N;
const int C = 430;
const int M = 10000;
std::vector<std::set<int>> inputClauses;
int literals[twoN];
int vars[N];

//Used for \Phi_init
int encodeLiteral(int literal) {
    return (literal < 0) ? -literal + N : literal;
}

void populateLiterals() {
    for (int i = 1; i < N+1; i++) {
        literals[i-1] = i;
        literals[i+(N-1)] = -i;
        vars[i-1] = i;
    }
}

Formula* phi_init() {
    auto* retVal = new AndFormula(nullptr, nullptr);
    for (int i = 0; i < C; i++) {
        std::set<int> & tempSet = inputClauses[i];
        for (int v : literals) {
            Formula* curr = new VarFormula(i, v);
            if (tempSet.find(v) == tempSet.end()) {
                //v does not exist in clause
                curr = new NotFormula(curr);
            }
            if (!retVal->left_) {
                retVal->left_ = curr;
            } else if (!retVal->right_) {
                retVal->right_ = curr;
            } else {
                AndFormula* temp = retVal;
                retVal = new AndFormula(temp, curr);
            }
        }
    }
    return retVal;
}

Formula* phi_consistent_p1() {
    //Cth index is C+1th clause
    auto* f1 = new AndFormula(nullptr, nullptr);
    for (int i = C; i < M; i++) {
        auto* f2 = new OrFormula(nullptr, nullptr);
        for (int j = 1; j < i; j++) {
            for (int jp = 1; jp < i; jp++) {
                if (j != jp) {
                    //Equivalence part of formula
                    auto* f3l = new AndFormula(nullptr, nullptr);
                    for (int l : literals) {
                        auto *orForm = new OrFormula(new VarFormula(j, l), new VarFormula(jp, l));
                        auto *andForm = new AndFormula(new NotFormula(new VarFormula(j, -l)),
                                                       new NotFormula(new VarFormula(jp, -l)));
                        auto *combForm = new AndFormula(orForm, andForm);
                        auto *equivForm = equivalent(new VarFormula(i, l), combForm);
                        if (!f3l->left_) {
                            f3l->left_ = equivForm;
                        } else if (!f3l->right_) {
                            f3l->right_ = equivForm;
                        } else {
                            AndFormula *tempAnd = f3l;
                            f3l = new AndFormula(tempAnd, equivForm);
                        }
                    }
                    //literal and -literal in the two
                    auto* f3v = new OrFormula(nullptr, nullptr);
                    for (int v : vars) {
                        auto* temp = new AndFormula(new VarFormula(j, v), new VarFormula(jp, -v));
                        if (!f3v->left_) {
                            f3v->left_ = temp;
                        } else if (!f3v->right_) {
                            f3v->right_ = temp;
                        } else {
                            OrFormula* tempOr = f3v;
                            f3v = new OrFormula(tempOr, temp);
                        }
                    }
                    //Combine the two
                    auto* f3 = new AndFormula(f3l, f3v);
                    if (!f2->left_) {
                        f2->left_ = f3;
                    } else if (!f2->right_) {
                        f2->right_ = f3;
                    } else {
                        OrFormula *tempOr = f2;
                        f2 = new OrFormula(tempOr, f3);
                    }
                }
            }
        }
        //And f1 with f1 and f2
        if (!f1->left_) {
            f1->left_ = f2;
        } else if (!f1->right_) {
            f1->right_ = f2;
        } else {
            AndFormula *tempAnd = f1;
            f1 = new AndFormula(tempAnd, f2);
        }
    }
    return f1;
}

Formula* phi_consistent_p2() {
    auto* f1 = new AndFormula(nullptr, nullptr);
    for (int i = 0; i < M; i++) {
        auto* f2 = new AndFormula(nullptr, nullptr);
        for (int l : literals) {
            auto* tempNot = new NotFormula(new AndFormula(new VarFormula(i, l), new VarFormula(i, -l)));
            if (!f2->left_) {
                f2->left_ = tempNot;
            } else if (!f2->right_) {
                f2->right_ = tempNot;
            } else {
                AndFormula *tempAnd = f2;
                f2 = new AndFormula(tempAnd, tempNot);
            }
        }
        //And f1 with f1 and f2
        if (!f1->left_) {
            f1->left_ = f2;
        } else if (!f1->right_) {
            f1->right_ = f2;
        } else {
            AndFormula *tempAnd = f1;
            f1 = new AndFormula(tempAnd, f2);
        }
    }
    return f1;
}

Formula* phi_consistent() {
    return new AndFormula(phi_consistent_p1(), phi_consistent_p2());
}

Formula* phi_empty() {
    //ith index is i+1th clause
    auto* retVal = new OrFormula(nullptr, nullptr);
    for (int i = 0; i < M; ++i) {
        auto* currAnd = new AndFormula(nullptr, nullptr);
        for (int l : literals) {
            auto* temp = new NotFormula(new VarFormula(i, l));
            if (!currAnd->left_) {
                currAnd->left_ = temp;
            } else if (!currAnd->right_) {
                currAnd->right_ = temp;
            } else {
                AndFormula* tempAnd = currAnd;
                currAnd = new AndFormula(tempAnd, temp);
            }
        }
        if (!retVal->left_) {
            retVal->left_ = currAnd;
        } else if (!retVal->right_) {
            retVal->right_ = currAnd;
        } else {
            OrFormula* tempOr = retVal;
            retVal = new OrFormula(tempOr, currAnd);
        }
    }
    return retVal;
}

int main() {
    std::ifstream infile("sat100.cnf");
    int a, b, c, d;
    while (infile >> a >> b >> c >> d) {
        std::set temp({a, b, c});
        inputClauses.push_back(temp);
    }
    populateLiterals();
    Formula* p_init = phi_init();
    Formula* p_cons = phi_consistent();
    Formula* p_empty = phi_empty();

    std::ofstream myfile;
    myfile.open("out.cnf");
    //myfile << p_init;
    //myfile << p_cons;
    //myfile << p_empty;
    myfile.close();
    infile.close();
    delete p_init;
    delete p_cons;
    delete p_empty;
    return 0;
}
