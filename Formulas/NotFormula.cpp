//
// Created by vklein52 on 3/14/18.
//

#include "NotFormula.h"

NotFormula::NotFormula(Formula* f) : formula_(f){

}

NotFormula::~NotFormula() { // NOLINT
    if (formula_)
        delete formula_;
}
