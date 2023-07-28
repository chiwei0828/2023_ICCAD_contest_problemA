#ifndef _bump_h_INCLUDED
#define _bump_h_INCLUDED

struct kissat;
struct infols;


void kissat_bump_variables (struct kissat *);

// void infols_bump(struct kissat *, struct infols *);

void infols_bump_update(struct kissat*);

#define MAX_SCORE 1e150

#endif
