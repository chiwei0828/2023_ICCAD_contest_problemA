#ifndef _walk_h_INCLUDED
#define _walk_h_INCLUDED

struct kissat;

char kissat_walk (struct kissat *);
int kissat_walk_initially (struct kissat *);
int select_strategy_by_decision_tree(struct kissat *, int NVARS, int NCLS, double CLS_TO_VAR, int MIN_LEN, double AVG_LEN, int MAX_LEN);

#endif
