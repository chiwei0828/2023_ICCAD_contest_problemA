#include "infols.h"
#include "internal.h"
#include "bump.h"

void infols_initialize(struct kissat* solver){
    infols *ils = &solver->ils;
    ils->conflicted      = (unsigned*)malloc(sizeof(unsigned)*solver->vars);
    ils->conflicts_num   = (unsigned*)malloc(sizeof(unsigned)*solver->vars);
    ils->last_updata_age = (unsigned*)malloc(sizeof(unsigned)*solver->vars);
    ils->conflicted_sz   = 0;
    ils->ls_steps        = 0;
    ils->var_nums        = 0;
}



void infols_get_confl_num(struct kissat* solver){
    infols *ils = &solver->ils;
    unsigned ls_trans = solver->options.aa_trans_confl;
    for(all_variables(var)){
      unsigned confl_num = ils->conflicts_num[var]*ls_trans/ils->ls_steps;
      if(confl_num > 0)
        ils->conflicts_num[var] = confl_num;
      else if(ils->conflicts_num[var]>0) // confl_num<1;
        ils->conflicts_num[var] = 1;

      if(ils->conflicts_num[var]>0){
        ils->conflicted[ils->conflicted_sz++] = var;
      }
    }
}


void infols_free(struct kissat* solver ){
    infols *ils = &solver->ils;
    free(ils->conflicted);
    free(ils->conflicts_num);
    free(ils->last_updata_age);
}

void infols_reset(struct kissat* solver){
    infols *ils = &solver->ils;
    infols_free(solver);
    ils->conflicted      = (unsigned*)malloc(sizeof(unsigned)*solver->vars);
    ils->conflicts_num   = (unsigned*)malloc(sizeof(unsigned)*solver->vars);
    memset(ils->conflicts_num,0,sizeof(unsigned)*solver->vars);
    ils->last_updata_age = (unsigned*)malloc(sizeof(unsigned)*solver->vars);
    memset(ils->last_updata_age,0,sizeof(unsigned)*solver->vars);
    ils->conflicted_sz   = 0;
    ils->ls_steps        = 0;
    ils->var_nums        = solver->vars;
}