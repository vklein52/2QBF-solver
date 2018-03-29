//
// Created by vklein52 on 3/15/18.
//

#ifndef RESEARCH_FORMULAHELPER_H
#define RESEARCH_FORMULAHELPER_H

#include "NotFormula.h"
#include "AndFormula.h"
#include "OrFormula.h"

Formula* equivalent(Formula *f1, Formula *f2) {
    //(f1 & f2) | ((~f1 & ~f2)
    auto* a1 = new AndFormula(f1, f2);
    auto* n1 = new NotFormula(f1);
    auto* n2 = new NotFormula(f2);
    auto* a2 = new AndFormula(n1, n2);
    return new OrFormula(a1, a2);
}

#endif //RESEARCH_FORMULAHELPER_H
