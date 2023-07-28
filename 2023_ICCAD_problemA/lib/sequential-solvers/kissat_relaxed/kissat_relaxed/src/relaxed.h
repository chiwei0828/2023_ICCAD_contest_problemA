#ifndef _relaxed_h_INCLUDED
#define _relaxed_h_INCLUDED

#include <stdbool.h>

struct kissat;

unsigned    level_before_relaxed_call_ls;
unsigned    freeze_restarts;
unsigned    top_trail_sz;
unsigned    ls_call_num;
int         condition_enter_num;
double      confl_ratio;
double      percent_ratio;
double      ls_time;

void initialize_relaxed_parameters();
bool kissat_meet_relaxed_condition(struct kissat *);
int kissat_relaxed_propagate (struct kissat *);
#endif