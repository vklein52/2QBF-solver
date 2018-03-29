//
// Created by vklein52 on 3/14/18.
//

#include "AndFormula.h"

AndFormula::AndFormula(Formula* l, Formula* r) : left_(l), right_(r){

}

AndFormula::~AndFormula() { // NOLINT
    if (left_)
        delete left_;
    if (right_)
        delete right_;
}




