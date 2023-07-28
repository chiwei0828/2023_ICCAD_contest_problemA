#ifndef _walk_h_INCLUDED
#define _walk_h_INCLUDED

struct kissat;

char kissat_walk (struct kissat *);
int kissat_walk_initially (struct kissat *);
bool kissat_walk_relaxed (struct kissat *);

#endif
