#ifndef _analyze_h_INCLUDED
#define _analyze_h_INCLUDED

#include <stdbool.h>

struct clause;
struct kissat;

int kissat_analyze (struct kissat *, struct clause *);

int kissat_analyze_exp (struct kissat *, struct clause *);

#endif
