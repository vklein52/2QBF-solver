//
// Created by vklein52 on 3/14/18.
//

#ifndef RESEARCH_NOTFORMULA_H
#define RESEARCH_NOTFORMULA_H
#include "Formula.h"

class NotFormula : public Formula {
public:
    Formula* formula_;
    explicit NotFormula(Formula* f);
    ~NotFormula() override;
};


#endif //RESEARCH_NOTFORMULA_H
