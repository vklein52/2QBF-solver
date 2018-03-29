//
// Created by vklein52 on 3/14/18.
//

#ifndef RESEARCH_ANDFORMULA_H
#define RESEARCH_ANDFORMULA_H
#include "Formula.h"

class AndFormula : public Formula {
public:
    Formula* left_;
    Formula* right_;
    AndFormula(Formula* l, Formula* r);
    ~AndFormula() override;
};


#endif //RESEARCH_ANDFORMULA_H
