#ifndef CCNR_H
#define CCNR_H

//heads
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <sys/times.h> 
#include <unistd.h>
#include <time.h>
#include <string.h>

// mersenne twist
typedef struct ccanr_randgen ccanr_randgen;

#define ccanr_Mersenne_N 624
#define ccanr_Mersenne_M 397
#define ccanr_Mersenne_MATRIX_A 0x9908b0dfUL
#define ccanr_Mersenne_UPPER_MASK 0x80000000UL
#define ccanr_Mersenne_LOWER_MASK 0x7fffffffUL

struct ccanr_randgen
{
	unsigned mt[ccanr_Mersenne_N];
	int 	 mti;
};

void ccanr_Mersenne_init_with_seed(ccanr_randgen* randgen, int seed); 
// generates random integer in [0..bound), bound < 2^31
int ccanr_Mersenne_next(ccanr_randgen* randgen, int bound);  



typedef struct ccanr_var ccanr_var;
typedef struct ccanr_lit ccanr_lit;
typedef struct ccanr_cls ccanr_cls;
typedef struct ccanr_solver ccanr_solver;

struct ccanr_lit
{
	unsigned char sense:1;	//is 1 for true literals, 0 for false literals.
	int clause_idx:31;		//clause num, begin with 0
	int var_idx;			//variable num, begin with 1
};

struct ccanr_var
{	
	int			literals_sz;
	ccanr_lit 	*literals;
	int 		neighbor_var_sz;
	int 		*neighbor_var;	
	long long	score;
	long long	last_flip_step;
	int			unsat_appear;	
	bool		cc_value;
	bool		is_in_ccd_vars;
};

struct ccanr_cls {
	int 		literals_sz;
	ccanr_lit 	*literals;	
	int			sat_count;
	int			sat_var;	
	long long	weight;
};

void ccanr_lit_init(ccanr_lit *tmp_lit,int the_lit, int the_clause);
bool ccanr_lit_is_equal(ccanr_lit *lit1, ccanr_lit *lit2);
ccanr_lit ccanr_minus_lit(ccanr_lit *lit);
int ccanr_lit_to_dimacs(ccanr_lit *lit);

struct ccanr_solver
{
	int 		_num_vars;
	int			_num_clauses;
	unsigned 	_additional_lens;
	int			_best_found_cost;
	double		_best_cost_time;
	long long 	_steps;
	long long 	_mems;
	long long   _max_mems;
	// long long	_max_steps;
	// int			_max_tries;
	int   		_swt_threshold;
	float 		_swt_p;
	float 		_swt_q;
	int			_avg_clause_weight;
	long long	_delta_total_clause_weight;
	bool 		_aspiration_active;
	int 		_aspiration_score;
	int 		_init_unsat_nums;
	float 		_prob_p;
	int			_unsat_cls_num;
	int 		_unsat_var_num;
	int 		_ccd_var_num;

	ccanr_var 	*_vars;
	ccanr_cls 	*_clauses;
	int			*_unsat_clauses;
	int			*_unsat_vars;
	int			*_idx_in_unsat_clauses;
	int			*_idx_in_unsat_vars;
	int			*_ccd_vars;
	char		*_solution;
	char		*_best_solution;
	ccanr_randgen randgen;
};


void ccanr_solver_release(ccanr_solver *s);
bool ccanr_build(ccanr_solver *s, char *filename);
void ccanr_initilize(ccanr_solver  *s);
bool ccanr_doLS(ccanr_solver  *s);
void ccanr_alloc(ccanr_solver *s);
void ccanr_build_after_read(ccanr_solver *s);
void ccanr_set_paprameter(ccanr_solver  *s);

#endif
