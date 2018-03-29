//
// Created by vklein52 on 3/14/18.
//

#include "OrFormula.h"

OrFormula::OrFormula(Formula* l, Formula* r) : left_(l), right_(r) {

}

OrFormula::~OrFormula() { // NOLINT
    if (left_)
        delete left_;
    if (right_)
        delete right_;
}
