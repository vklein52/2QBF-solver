//
// Created by vklein52 on 3/14/18.
//

#ifndef RESEARCH_VARFORMULA_H
#define RESEARCH_VARFORMULA_H
#include "ClauseVar.h"
#include "Formula.h"

class VarFormula : public Formula{
public:
    int clause_;
    int var_;
    VarFormula(int c, int v);
    ~VarFormula() override = default;
};


#endif //RESEARCH_VARFORMULA_H
