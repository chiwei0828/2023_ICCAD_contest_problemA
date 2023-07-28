//
// Created by Yuqi on 2022/4/5.
//
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include "expscore.h"
#include "propsearch.h"
#include "internal.h"
#include "decide.h"
#include "literal.h"
#include "analyze.h"
#include "backtrack.h"
#include "stack.h"


void expscore_init(struct kissat * solver){
    expscore * exps = &solver->exps;
    exps->stepLBDMap = (unsigned**) malloc(sizeof(unsigned*)*2*solver->mW);
    exps->stepVarMap = (unsigned**) malloc(sizeof(unsigned*)*2*solver->mW);
    for(int i=0; i<2*solver->mW; ++i){
        exps->stepLBDMap[i] = (unsigned*)malloc(sizeof(unsigned)*2*solver->mS);
        exps->stepVarMap[i] = (unsigned*)malloc(sizeof(unsigned)*2*solver->mS);
    }
    exps->slm_sizes = (unsigned*)malloc(sizeof(unsigned)*2*solver->mW);
    exps->svm_sizes = (unsigned*)malloc(sizeof(unsigned)*2*solver->mW);
    exps->slm_size = exps->svm_size = 0;

    exps->walkWithConf = (bool*)malloc(sizeof(bool)*2*solver->mW);
    exps->wwc_size = 0;

    exps->expScore = (double*)malloc(sizeof(double)*solver->vars);
    exps->walkScore = (double*)malloc(sizeof(double)*solver->vars);
    exps->varOcc = (int*)malloc(sizeof(int)*solver->vars);
    exps->varInd = (unsigned*)malloc(sizeof(unsigned)*solver->vars);
    exps->exploring = false;
    exps->var_num = 0;
}

bool triggerExploration(struct kissat * solver){
    if(!solver->stable || !(solver->exp_ct++ % solver->options.aa_freeze_exp)) return false;
    solver->exp_ct = 0;
    if(solver->lastDecisionHadConflicts){
        solver->decisionsWithConflicts++;
        if(solver->successiveDecisionsWithoutConfs>0)
            solver->CDPhaseCount++;
        solver->successiveDecisionsWithoutConfs = 0;
        solver->lastDecisionHadConflicts = false;
    }
    else{
        solver->decisionsWithoutConflicts++;
        solver->successiveDecisionsWithoutConfs++;
    }
    int toReachConflict = 0;
    if(solver->decisionsWithConflicts)
        toReachConflict = (double) solver->decisionsWithoutConflicts / (double) solver->decisionsWithConflicts;
    double r = (double) (rand() % 100) / 100.0;
    bool retVal = (solver->CDPhaseCount>0 && solver->decisionsWithConflicts) && (solver->successiveDecisionsWithoutConfs >= ceil(toReachConflict)) && (r <= ((double) solver->prTh / 100.0));
    return retVal;
}

clause * performStep(struct kissat * solver, bool *flag, unsigned *next_var){
    clause *conflict;
    if(!kissat_empty_heap(&solver->scores)){
//        srand((unsigned)time(NULL));
        *next_var = rand() % kissat_size_heap(&solver->scores);
        //printf("expscore.c 66: next_var  %u. \n", *next_var);
//        const unsigned idx = kissat_next_decision_variable (solver);//PEEK_STACK(&solver->scores, rand() % SIZE_STACK(&solver->scores));
        value *values = solver->values;
        unsigned lit = LIT (*next_var);
        int value = values[lit]; int value_ = values[NOT(lit)];
        if(!value && !value_){
            kissat_internal_assume(solver, lit);
//            //printf("expscore.c 65: !!!\n");
            conflict = kissat_search_propagate(solver);
            //if(conflict) //printf("expscore.c 75: confl->size  %u. \n", conflict->size);
            *flag = true;
        }
        else{
            *flag = false;
        }
    }
    return conflict;
}

// performs exploration for mW walks and mS number of steps per walk.
void explore(struct kissat * solver){
    //printf("expscore.c 78: !!!\n");
    expscore *exps = &solver->exps;
    exps->exploring = true;
    expscore_reset(solver);
    for(int i=0; i<solver->mW; ++i){
        int expStep = 0;
        bool endsWithAConf = false;
        unsigned level = solver->level;
        int tmp = SIZE_STACK(solver->trail); int tmp1 = PEEK_STACK(solver->trail, tmp-2); int tmp2 = PEEK_STACK(solver->trail, tmp-1); int value560 = (solver->values)[560];
        for(int j=0; j<solver->mS; ++j){
            bool flag;
            unsigned stepVar;
            clause * confl = performStep(solver, &flag, &stepVar);
            //printf("expscore.c 90: next_var  %u. \n", stepVar);
            if(flag){
                //printf("expscore.c 92: !!!\n");
                exps->stepVarMap[i][expStep] = stepVar;
                exps->svm_sizes[i]++;
                if(confl){
                    //printf("expscore.c 93: confl->size %u!!! \n", confl->size);
//                    solver->lastDecisionHadConflicts = true;
                    kissat_analyze_exp(solver, confl);
                    //printf("expscore.c 96: decision_level: %d, prev_level: %d!!!\n", solver->level, level);
                    exps->stepLBDMap[i][expStep] = solver->new_clause_lbd;
                    exps->slm_sizes[i]++;
//                    //printf("expscore.c 99: !!!\n");
                    endsWithAConf = true;
                    kissat_backtrack_exp(solver, level);
                    break;
                }
                expStep++;
            }
        }
        //printf("expscore.c 112: !!!\n");
        exps->walkWithConf[exps->wwc_size++] = endsWithAConf;
        if(endsWithAConf == false) {
            kissat_backtrack_exp(solver, level);
            //cancelUntil(dLevel);
        }
        //int tmp3 = SIZE_STACK(solver->trail);
//        printf("expscore.c, 129, trail->size: %d, old_trail_size: %d \n", tmp3, tmp);
//        printf("expscore.c 130, trail[-2]: %u, trail[-1]: %u \n", PEEK_STACK(solver->trail, tmp3-2), PEEK_STACK(solver->trail, tmp3-1));
//        printf("expscore.c 131, old_trail[-2]: %u, old_trail[-1]: %u \n", tmp1, tmp2);
        //printf("expscore.c 132, value560: %d, old_value560: %d \n", (solver->values)[560], value560);
    }
    exps->exploring = false;
    //printf("expscore.c 121: !!!\n");
}

// computes the exploration scores.
void computeExplorationScore(struct kissat * solver){
    expscore * exps = &solver->exps;
    //printf("wwc_size %d\n", exps->wwc_size);
    for(int walk=0; walk<exps->wwc_size; walk++){
        if(exps->walkWithConf[walk]==true && (double) exps->stepLBDMap[walk][exps->svm_sizes[walk]-1] <= solver->avg_lbd){
            int stepsCount = exps->svm_sizes[walk];
            //printf("expscore.c 119: stepsCount %d\n", stepsCount);
            for(int revStep=stepsCount-1; revStep>=0; revStep--){
                if(exps->stepLBDMap[walk][stepsCount - 1] != 0){
                    double stepScore = ((1.0 / (double) exps->stepLBDMap[walk][stepsCount - 1])) *
                                       pow(0.9, stepsCount - revStep - 1);
                    unsigned stepVar = exps->stepVarMap[walk][revStep];
                    exps->walkScore[stepVar] += stepScore;
                    exps->varOcc[stepVar]++;
                }
                //printf("expscore.c 153: stepLBDMap: %d, walkscore: %f, varOcc: %d \n", exps->stepLBDMap[walk][stepsCount-1], exps->walkScore[stepVar], exps->varOcc[stepVar]);
            }
        }
    }
    for(all_variables(var)){
        exps->expScore[var] = exps->walkScore[var] / (double) exps->varOcc[var];
        if(exps->expScore[var]>0){
            //printf("expscore.c 130: expscore: %f\n", exps->expScore[var]);
            exps->varInd[exps->var_num++] = var;
        }
    }
}


void expscore_free(struct kissat * solver){
    expscore * exps = &solver->exps;
    for(int i=0; i<2*solver->mW; ++i){
        free(exps->stepLBDMap[i]);
        free(exps->stepVarMap[i]);
    }
    free(exps->stepLBDMap);
    free(exps->stepVarMap);

    free(exps->slm_sizes);
    free(exps->svm_sizes);

    free(exps->walkWithConf);

    free(exps->varInd);
    free(exps->expScore);
    free(exps->walkScore);
    free(exps->varOcc);
}

void expscore_reset(struct kissat * solver){
    expscore * exps = &solver->exps;
    expscore_free(solver);

    exps->stepLBDMap = (unsigned**) malloc(sizeof(unsigned*)*2*solver->mW);
    exps->stepVarMap = (unsigned**) malloc(sizeof(unsigned*)*2*solver->mW);
    for(int i=0; i<2*solver->mW; ++i){
        exps->stepLBDMap[i] = (unsigned*)malloc(sizeof(unsigned)*2*solver->mS);
        memset(exps->stepLBDMap[i],0,sizeof(unsigned)*2*solver->mS);
        exps->stepVarMap[i] = (unsigned*)malloc(sizeof(unsigned)*2*solver->mS);
        memset(exps->stepVarMap[i],0,sizeof(unsigned)*2*solver->mS);
    }
    exps->slm_sizes = (unsigned*)malloc(sizeof(unsigned)*2*solver->mW);
    memset(exps->slm_sizes,0,sizeof(unsigned)*2*solver->mW);
    exps->svm_sizes = (unsigned*)malloc(sizeof(unsigned)*2*solver->mW);
    memset(exps->svm_sizes,0,sizeof(unsigned)*2*solver->mW);
    exps->slm_size = exps->svm_size = 0;

    exps->walkWithConf = (bool*)malloc(sizeof(bool)*2*solver->mW);
    exps->wwc_size = 0;

    exps->expScore = (double*)malloc(sizeof(double)*solver->vars);
    memset(exps->expScore,0,sizeof(double)*solver->vars);
    exps->walkScore = (double*)malloc(sizeof(double)*solver->vars);
    memset(exps->walkScore,0,sizeof(double)*solver->vars);
    exps->varOcc = (int*)malloc(sizeof(int)*solver->vars);
    memset(exps->varOcc,0,sizeof(int)*solver->vars);
    exps->varInd = (unsigned*)malloc(sizeof(unsigned)*solver->vars);
    exps->var_num = 0;
}