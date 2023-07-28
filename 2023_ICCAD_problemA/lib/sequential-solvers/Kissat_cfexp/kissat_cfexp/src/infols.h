#ifndef _infols_h_INCLUDED
#define _infols_h_INCLUDED

typedef struct infols infols;

struct kissat;

struct infols
{
    unsigned ls_steps;
    unsigned *conflicts_num;
    unsigned *last_updata_age;
    unsigned conflicted_sz;
    unsigned *conflicted;
    unsigned should_free;
    unsigned var_nums;
};

void infols_initialize(struct kissat*);
// void infols_update_and_free(struct kissat*, struct infols*);


void infols_free(struct kissat*);
void infols_reset(struct kissat*);
void infols_get_confl_num(struct kissat* solver);
#endif