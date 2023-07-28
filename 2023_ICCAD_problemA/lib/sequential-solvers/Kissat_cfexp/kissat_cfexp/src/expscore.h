//
// Created by Yuqi on 2022/4/5.
//

#ifndef KISSAT_SAT_CF_WITH_PWD_EXPSCORE_H
#define KISSAT_SAT_CF_WITH_PWD_EXPSCORE_H

#include<stdbool.h>

typedef struct expscore expscore;

struct kissat;

struct expscore{
//    int * walk;   // index of stepVarMap stepLBDMap
    unsigned ** stepVarMap;
    unsigned ** stepLBDMap;

    unsigned svm_size, slm_size;

    unsigned * svm_sizes;
    unsigned * slm_sizes;

//    int * expStep; //2-nd index of two map

    bool * walkWithConf;
    unsigned wwc_size;

//    std::map<int,std::map<int,uint32_t> > stepVarMap;
//    std::map<int,std::map<int,bool> > stepConfFlagMap;
//    std::map<int,std::map<int,uint32_t> > stepLBDMap;

//    std::map<int,uint32_t> stepVarPair;
//    std::map<int,bool> stepConfFlagPair;
//    std::map<int,uint32_t> stepConfLBDPair;
//    vec<bool> walkWithConf;
    bool exploring;

    unsigned * varInd; //index of walkScore, varOcc, expScore
    unsigned var_num;

    double * walkScore;
    int * varOcc;
    double * expScore;
//    std::map<uint32_t,double> walkScore;
//    std::map<uint16_t,int> varOcc;
//    std::map<uint32_t,double> expScore;
};

void expscore_init(struct kissat * solver);

//clause * performStep(struct kissat * solver, bool *flag, unsigned *next_var);

bool triggerExploration(struct kissat * solver);
void explore(struct kissat * solver);
void computeExplorationScore(struct kissat * solver);


void expscore_free(struct kissat * solver);
void expscore_reset(struct kissat * solver);

//#define MAX_SCORE 1e150

#endif //KISSAT_SAT_CF_WITH_PWD_EXPSCORE_H
