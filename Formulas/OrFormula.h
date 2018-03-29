//
// Created by vklein52 on 3/14/18.
//

#ifndef RESEARCH_ORFORMULA_H
#define RESEARCH_ORFORMULA_H
#include "Formula.h"

class OrFormula : public Formula {
public:
    Formula* left_;
    Formula* right_;
    OrFormula(Formula* l, Formula* r);
    ~OrFormula() override;
};


#endif //RESEARCH_ORFORMULA_H
