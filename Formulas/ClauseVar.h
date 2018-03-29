//
// Created by vklein52 on 3/14/18.
//

#ifndef RESEARCH_CLAUSEVAR_H
#define RESEARCH_CLAUSEVAR_H


class ClauseVar {
private:
    int clause_;
    int var_;
public:
    ClauseVar(int c, int v);
    ~ClauseVar();
};


#endif //RESEARCH_CLAUSEVAR_H
