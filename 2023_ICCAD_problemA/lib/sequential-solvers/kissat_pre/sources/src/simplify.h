#ifndef _simplify_h_INCLUDED
#define _simplify_h_INCLUDED
#include <stdbool.h>
#include "file.h"
#include "cvec.h"

typedef struct simplify simplify;
struct simplify{
    int vars;
    int clauses;
    int orivars;
    int oriclauses;
    int real_clauses;
    int **clause;
    int *clause_size;
    int res_clauses;
    int **res_clause;
    int *res_clause_size;
    int *resolution;
    int resolutions;
    int *clause_state;
    int *clause_delete;
    int *seen;
    int **occurp;
    int **occurn;
    int *occurp_size;
    int *occurn_size;
    int *clean;
    int *color;
    int *queue;
    int *varval;
    int *resseen;
    int *mapto;
    int *mapfrom;
    int *mapval;
    int cards;
    int **card_one;
    int *card_one_size;
    double **mat;
    int mats;
    int *cdel;
    int M_card;
    cvec* store_clause;
};



struct kissat;

bool kissat_simplify(struct kissat * solver, int *maxvar, file *file);
void kissat_complete_val(struct kissat * solver);

#endif