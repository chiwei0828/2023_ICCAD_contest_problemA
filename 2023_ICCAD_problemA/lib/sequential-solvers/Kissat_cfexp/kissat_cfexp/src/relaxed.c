#include "relaxed.h"
#include "internal.h"
#include "clause.h"
#include "decide.h"
#include "propsearch.h"
#include "ccanr.h"
#include "backtrack.h"
#include "allocate.h"
#include "stack.h"
#include "resources.h"
#include "relaxed.h"
#include <stdio.h>



void initialize_relaxed_parameters(){
    freeze_restarts = 500;//solver->options.restarts_gap;
    top_trail_sz = ccanr_call_num = ccanr_time = 0;
    confl_ratio = 0.5;//(solver->options.confl_ratio+0.0)/100;
    percent_ratio = 0.9;//(solver->options.percent_ratio+0.0)/100;
    printf("c parameters for relaxed:\n"); 
    // printf("c confl_ratio=%.2f  \tpercent_ratio=%.2f \trestarts_gap=%d\n",confl_ratio,percent_ratio,solver->options.restarts_gap);
    // printf("c last_ls=%d\t best_ls=%d top_tral=%d \tdiverse_reverse=%d\n",solver->options.last_LS_phase,solver->options.best_LS_phase,solver->options.top_trail_phase,solver->options.diverse_reverse);
}

bool kissat_meet_relaxed_condition(struct kissat *solver){
    if(freeze_restarts>0) return false;
    int assigned_sz = SIZE_STACK (solver->trail);
    if( ((double)(assigned_sz+0.0)/(solver->vars)) >= confl_ratio)
        return true;
    if( ((double)(assigned_sz+0.0)/(top_trail_sz)) >= percent_ratio)
        return true;
    return false;
}


inline int ilit_to_dimacs(unsigned int lit){
    int dimacs = lit>>2;
    if((lit&0x01)==1) return -dimacs-1;
    return dimacs+1;
}


bool kissat_call_relaxed_solver(kissat *solver, ccanr_solver *s){
    for(unsigned v=1;v<=solver->vars;++v){
        unsigned lit = LIT(v-1);
        if(solver->values[lit]>0)
            s->_best_solution[v] = s->_solution[v] = 1;
        else
            s->_best_solution[v] = s->_solution[v] = 0;
    }
    bool res = ccanr_doLS(s);
    
    ccanr_call_num ++;
    return res;
}


int kissat_get_cls_num_without_trail(kissat *solver){
    int cls_num = 0;
     for(all_literals(lit)){
        watches *watches = &WATCHES(lit);
        watch *p = BEGIN_WATCHES(*watches);
        const watch *end = END_WATCHES(*watches);
        while(p!=end){
            const watch head = *p++;
            if(head.type.binary)
                cls_num++;
        }
        
    }
    cls_num/=2;
    for(all_clauses(c)) if(!c->garbage) cls_num++;
    return cls_num;
}

void kissat_trans_data_to_ccanr(kissat *solver, ccanr_solver *s){
    s->_num_clauses  = kissat_get_cls_num_without_trail(solver);
    s->_num_vars     = solver->vars;
    int trail_sz     = 0;
    if(SIZE_STACK(solver->frames)>1)
        trail_sz = (solver->frames.begin+1)->trail;
    else trail_sz = SIZE_STACK(solver->trail);
    s->_num_clauses += trail_sz;

    ccanr_alloc(s);
   
    int ct = 0;
    for(all_literals(lit)){
        watches *watches = &WATCHES(lit);
        watch *p = BEGIN_WATCHES(*watches);
        const watch *end = END_WATCHES(*watches);
        while(p!=end){
            const watch head = *p++;
            if(head.type.binary){
                const unsigned other = head.binary.lit;
                if(other < lit) continue;
                s->_clauses[ct].literals = (ccanr_lit*)malloc(sizeof(ccanr_lit)*2);
                ccanr_lit_init(&(s->_clauses[ct].literals[0]),ilit_to_dimacs(other),ct);
                ccanr_lit_init(&(s->_clauses[ct].literals[1]),ilit_to_dimacs(lit),ct);
                s->_clauses[ct].literals_sz = 2;
                ++ct;
            }
        }
    }
    for(all_clauses(c)){
        if(c->garbage) continue;
        s->_clauses[ct].literals = (ccanr_lit*)malloc(sizeof(ccanr_lit)*c->size);
        int size = 0;
        for(all_literals_in_clause(lit, c))
            ccanr_lit_init(&(s->_clauses[ct].literals[size++]),ilit_to_dimacs(lit),ct);
        s->_clauses[ct].literals_sz = size;
        ++ct;
    }
    for(int i=0;i<trail_sz;++i){
        unsigned int lit = *(solver->trail.begin+i);
        int dimacs_lit = ilit_to_dimacs(lit);
        s->_clauses[ct].literals = (ccanr_lit*)malloc(sizeof(ccanr_lit)*1);
        ccanr_lit_init(&(s->_clauses[ct].literals[0]),dimacs_lit,ct);
        s->_clauses[ct].literals_sz = 1;
        ++ct;
    }
    ccanr_build_after_read(s);
}


bool kissat_relaxed_propagate (struct kissat *solver){
    double time_begin = kissat_process_time();
    
    ccanr_solver s;
    kissat_trans_data_to_ccanr(solver,&s);
    level_before_relaxed_call_ls = solver->level;
    while(solver->unassigned>0){
        kissat_search_propagate (solver);
        if(solver->unassigned>0){
            kissat_decide(solver);
        }
    }
    bool res = kissat_call_relaxed_solver(solver,&s);
    if(res){
        // for(unsigned v=1;v<=solver->vars;++v){
        //     unsigned lit = LIT(v-1);
        //     unsigned n_lit = NOT(lit);
        //     if(s._best_solution[v]==1) 
        //         solver->values[lit]=1,solver->values[n_lit]=-1;
        //     else
        //         solver->values[lit]=-1,solver->values[n_lit]=1;
        // }
    }
    for(unsigned v=1;v<=solver->vars;++v){
        unsigned lit = LIT(v-1);
        unsigned n_lit = NOT(lit);
        if(s._best_solution[v]==1) 
            solver->phases[lit].relaxed=1,solver->phases[n_lit].relaxed=-1;
        else
            solver->phases[lit].relaxed=-1,solver->phases[n_lit].relaxed=1;
    }
    kissat_backtrack(solver,level_before_relaxed_call_ls);
    freeze_restarts=500;//solver->options.restarts_gap;
    double this_call_time = kissat_process_time()-time_begin;
    ccanr_time += this_call_time;
    printf("c LS_res=%d, call=%d, restarts=%lu, conflicts=%lu, time=%.2f, all_ls_time=%.2f, step=%lld\n",res,ccanr_call_num,solver->statistics.restarts,solver->statistics.conflicts,this_call_time,ccanr_time,s._steps);
    ccanr_solver_release(&s);
    return res;
}
