#include "hywalk.h"
#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item
#define hywalk_Mersenne_N 624
#define hywalk_Mersenne_M 397
#define hywalk_Mersenne_MATRIX_A 0x9908b0dfUL
#define hywalk_Mersenne_UPPER_MASK 0x80000000UL
#define hywalk_Mersenne_LOWER_MASK 0x7fffffffUL

void    hywalk_Mersenne_init_with_seed(hywalk_randgen* randgen, int seed); 
int     hywalk_Mersenne_next(hywalk_randgen* randgen, int bound);  
int     hywalk_rand(HyWalk*, int);


void	 pick_var(HyWalk*);
void	 pick_var_FPS(HyWalk*);
void	 pick_var_BandSAT(HyWalk*);
void	 pick_var_Simple(HyWalk*);
void	 pick_var_FS(HyWalk*);
void	 pick_var_BF(HyWalk*);
void init(HyWalk*,char*);
void unit_propagation(HyWalk*);
void preprocess(HyWalk*);
void flip(HyWalk*,int);
void flip2(HyWalk*,int);
void smooth_clause_weights(HyWalk*);
void update_clause_weights(HyWalk*);
void update_clause_scores(HyWalk*,int);
void set_clause_weighting(HyWalk*);

int select_strategy_by_decision_tree(HyWalk*, int NVARS, int NCLS, double CLS_TO_VAR, int MIN_LEN, double AVG_LEN, int MAX_LEN);

void default_initialize(HyWalk* lssolver){
	lssolver->formula_len=0;
	lssolver->unitclause_queue_beg_pointer=0;
    lssolver->unitclause_queue_end_pointer=0;
	lssolver->max_tries = 10000;
	lssolver->max_flips = 200000000;
	lssolver->ave_weight=1;
	lssolver->delta_total_weight=0;
	lssolver->q_scale=0;
	lssolver->q_init=0;
	lssolver->mems_left=50000000;
}

void alloc_memory(HyWalk *lssolver){
	int var_mem = lssolver->num_vars+2;
	int cls_mem = lssolver->num_clauses+2;
  int fps_cnum_mem = 10+2;
  int bandit_cnum_mem = 20+2;
	lssolver->score_inc_vars 	= (int*)malloc(sizeof(int)*var_mem);
	lssolver->score_inc_flag 	= (int*)malloc(sizeof(int)*var_mem);
	lssolver->var_lit 			= (lit**)malloc(sizeof(lit*)*var_mem);
	lssolver->var_lit_count 	= (int*)malloc(sizeof(int)*var_mem);
	lssolver->clause_lit  		= (lit**)malloc(sizeof(lit*)*cls_mem);
	lssolver->clause_lit_count	= (int*)malloc(sizeof(int)*cls_mem);
	lssolver->score				= (int*)malloc(sizeof(int)*var_mem);
	lssolver->time_stamp		= (int*)malloc(sizeof(int)*var_mem);
	lssolver->fix				= (int*)malloc(sizeof(int)*var_mem);
	lssolver->cscc 				= (int*)malloc(sizeof(int)*var_mem);
	lssolver->clause_weight		= (int*)malloc(sizeof(int)*cls_mem);
	lssolver->sat_count			= (int*)malloc(sizeof(int)*cls_mem);
	lssolver->sat_var			= (int*)malloc(sizeof(int)*cls_mem);
	lssolver->unsat_stack		= (int*)malloc(sizeof(int)*cls_mem);
	lssolver->index_in_unsat_stack=(int*)malloc(sizeof(int)*cls_mem);
	lssolver->unsatvar_stack  	= (int*)malloc(sizeof(int)*var_mem);
	lssolver->index_in_unsatvar_stack = (int*)malloc(sizeof(int)*var_mem);
	lssolver->unsat_app_count 	= (int*)malloc(sizeof(int)*var_mem);
	lssolver->goodvar_stack 	= (int*)malloc(sizeof(int)*var_mem);
	lssolver->already_in_goodvar_stack = (int*)malloc(sizeof(int)*var_mem);
	lssolver->unitclause_queue 	= (lit*)malloc(sizeof(lit)*var_mem);
	lssolver->clause_delete 	= (int*)malloc(sizeof(int)*cls_mem);
	lssolver->cur_soln			= (char*)malloc(sizeof(int)*var_mem);
	lssolver->best_soln			= (char*)malloc(sizeof(int)*var_mem);
	lssolver->conflict_ct		= (int*)malloc(sizeof(int)*var_mem);
	lssolver->in_conflict		= (int*)malloc(sizeof(int)*var_mem);
 
  lssolver->cscc2         = (int*)malloc(sizeof(int)*var_mem);
  
  lssolver->sel_cs        = (int*)malloc(sizeof(int)*cls_mem);
  lssolver->selected      = (int*)malloc(sizeof(int)*var_mem);
  lssolver->selected_during_flip = (int*)malloc(sizeof(int)*var_mem);
  lssolver->score2        = (int*)malloc(sizeof(int)*var_mem);
  lssolver->scores        = (int*)malloc(sizeof(int)*var_mem);
  lssolver->vars2         = (int*)malloc(sizeof(int)*var_mem);
  lssolver->goodvar_stack2 = (int*)malloc(sizeof(int)*var_mem);
  lssolver->best_vars     = (int*)malloc(sizeof(int)*var_mem);
  
  lssolver->selected_clauses = (int*)malloc(sizeof(int)*cls_mem);
  lssolver->selected_times = (int*)malloc(sizeof(int)*cls_mem);
  lssolver->sampled_clauses = (int*)malloc(sizeof(int)*cls_mem);
  lssolver->clause_score = (double*)malloc(sizeof(double)*cls_mem);
  
	for(int i=1;i<=lssolver->num_vars;++i) lssolver->conflict_ct[i]=0;
}

void free_memory(HyWalk *lssolver)
{
	int i;
	for (i = 0; i < lssolver->num_clauses; i++) 
	{
		free(lssolver->clause_lit[i]);
	}
	
	for(i=1; i<=lssolver->num_vars; ++i)
	{
		free(lssolver->var_lit[i]);
	}
	
	free(lssolver->score_inc_vars);
	free(lssolver->score_inc_flag);
	free(lssolver->var_lit);
	free(lssolver->var_lit_count); 
	free(lssolver->clause_lit); 
	free(lssolver->clause_lit_count); 
	free(lssolver->score);
	free(lssolver->time_stamp);
	free(lssolver->fix);	
	free(lssolver->cscc); 
	free(lssolver->clause_weight);	
	free(lssolver->sat_count);	
	free(lssolver->sat_var);		
	free(lssolver->unsat_stack);	
	free(lssolver->index_in_unsat_stack);
	free(lssolver->unsatvar_stack); 
	free(lssolver->index_in_unsatvar_stack);
	free(lssolver->unsat_app_count);
	free(lssolver->goodvar_stack);
	free(lssolver->already_in_goodvar_stack);
	free(lssolver->unitclause_queue);
	free(lssolver->clause_delete);
	free(lssolver->cur_soln);
	free(lssolver->best_soln);
	free(lssolver->conflict_ct);
	free(lssolver->in_conflict);
  
  free(lssolver->cscc2);
  
  free(lssolver->sel_cs);
  free(lssolver->selected);
  free(lssolver->selected_during_flip);
  free(lssolver->score2);
  free(lssolver->scores);
  free(lssolver->vars2);
  free(lssolver->goodvar_stack2);
  free(lssolver->best_vars);
  
  free(lssolver->selected_clauses);
  free(lssolver->selected_times);
  free(lssolver->sampled_clauses);
  free(lssolver->clause_score);
}


//pick a var to be flip
void pick_var(HyWalk *lssolver)
{
	int         i,k,c,v;
	int         best_var;
	lit*		clause_c;
	
  lssolver->tabu_step = 0;
 
	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(lssolver->goodvar_stack_fill_pointer>0)
	{
		lssolver->mems_left -= lssolver->goodvar_stack_fill_pointer;
		best_var = lssolver->goodvar_stack[0];
		
		for(i=1; i<lssolver->goodvar_stack_fill_pointer; ++i)
		{
			v=lssolver->goodvar_stack[i];
			if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
			else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
		}
		
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
		//return best_var;
	}
	
	/*SD (significant decreasing) mode, the level with aspiration*/
	best_var = 0;
	for(i=0; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		if(lssolver->score[lssolver->unsatvar_stack[i]]>lssolver->ave_weight) 
		{
			best_var = lssolver->unsatvar_stack[i];
			break;
		}
	}

	for(++i; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		v=lssolver->unsatvar_stack[i];
		if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
		else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
	}
		
	if(best_var!=0){
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
    //return best_var;
  }
		
	/**Diversification Mode**/
	update_clause_weights(lssolver);
	
	/*focused random walk*/
	c = lssolver->unsat_stack[hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];
	clause_c = lssolver->clause_lit[c];
	best_var = clause_c[0].var_num;
	for(k=1; k<lssolver->clause_lit_count[c]; ++k)
	{
		v=clause_c[k].var_num;
		//if(time_stamp[v]<time_stamp[best_var]) best_var = v;
		if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
		else if(lssolver->score[v]==lssolver->score[best_var]&&lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
	}
	
	flip(lssolver,best_var);
  lssolver->time_stamp[best_var] = lssolver->step;
  lssolver->step++;
  return;
  //return best_var;
}

void pick_var_Simple(HyWalk *lssolver)
{
  int         i,k,c,v;
	int         best_var;
	lit*		clause_c;
	
  lssolver->tabu_step = 1;
  
	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(lssolver->goodvar_stack_fill_pointer>0)
	{
		lssolver->mems_left -= lssolver->goodvar_stack_fill_pointer;
		best_var = lssolver->goodvar_stack[0];
		
		for(i=1; i<lssolver->goodvar_stack_fill_pointer; ++i)
		{
			v=lssolver->goodvar_stack[i];
			if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
			else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
		}
		
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
		//return best_var;
	}
 
	/*SD (significant decreasing) mode, the level with aspiration*/
	best_var = 0;
	for(i=0; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		if(lssolver->score[lssolver->unsatvar_stack[i]]>lssolver->ave_weight) 
		{
			best_var = lssolver->unsatvar_stack[i];
			break;
		}
	}

	for(++i; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		v=lssolver->unsatvar_stack[i];
		if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
		else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
	}
 
	if(best_var!=0){
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
    //return best_var;
  }
		
	/**Diversification Mode**/
	update_clause_weights(lssolver);
 
  /*focused random walk*/
  /*
  c = lssolver->unsat_stack[hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];
	clause_c = lssolver->clause_lit[c];
	best_var = clause_c[0].var_num;
	for(k=1; k<lssolver->clause_lit_count[c]; ++k)
	{
		v=clause_c[k].var_num;
		//if(time_stamp[v]<time_stamp[best_var]) best_var = v;
		if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
		else if(lssolver->score[v]==lssolver->score[best_var]&&lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
	}
  */
  
  best_var = 0;
  int j;
  int max_score = -10000000;
  for (i = 0; i < 10; i++){
    c = lssolver->unsat_stack[hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];//hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];
    for (j = 0; j < 5; j++){
      v = lssolver->clause_lit[c][hywalk_rand(lssolver,lssolver->clause_lit_count[c])].var_num;//hywalk_rand(lssolver,lssolver->clause_lit_count[c])].var_num;
      if (lssolver->cscc[v]==0)
        continue;
      if (lssolver->score[v] > max_score){
        max_score = lssolver->score[v];
        best_var = v;
      }
      else if (lssolver->score[v] == max_score && lssolver->time_stamp[v] < lssolver->time_stamp[best_var])
        best_var = v;
    }
  }
  
  //printf("%d ",best_var);
  
  if (best_var > 0){
  	flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
  }
  return;
}

void pick_var_FPS(HyWalk *lssolver)
{
  int         i,k,c,v;
	int         best_var;
	lit*		clause_c;
	
  lssolver->tabu_step = 1;
 
	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(lssolver->goodvar_stack_fill_pointer>0)
	{
		lssolver->mems_left -= lssolver->goodvar_stack_fill_pointer;
		best_var = lssolver->goodvar_stack[0];
		
		for(i=1; i<lssolver->goodvar_stack_fill_pointer; ++i)
		{
			v=lssolver->goodvar_stack[i];
			if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
			else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
		}
		
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
		//return best_var;
	}
	
	/*SD (significant decreasing) mode, the level with aspiration*/
	best_var = 0;
	for(i=0; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		if(lssolver->score[lssolver->unsatvar_stack[i]]>lssolver->ave_weight) 
		{
			best_var = lssolver->unsatvar_stack[i];
			break;
		}
	}

	for(++i; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		v=lssolver->unsatvar_stack[i];
		if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
		else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
	}
		
	if(best_var!=0){
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
    //return best_var;
  }
  
  lssolver->selected_nums = 10;
  int best_vars_num = 0;
  for (i = 0; i < 10; i++){
    lssolver->sel_cs[i] = lssolver->unsat_stack[hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];
    lssolver->best_vars[best_vars_num] = lssolver->clause_lit[lssolver->sel_cs[i]][hywalk_rand(lssolver,lssolver->clause_lit_count[lssolver->sel_cs[i]])].var_num;
    if (lssolver->selected[lssolver->best_vars[best_vars_num]] || lssolver->cscc[lssolver->best_vars[best_vars_num]] == 0){
      lssolver->selected_nums--;
    }
    else {
      lssolver->selected[lssolver->best_vars[best_vars_num]] = 1;
      best_vars_num++;
    }
  }
  
  for (i = 0; i < lssolver->selected_nums; i++)
    lssolver->selected[lssolver->best_vars[i]] = 0;
  
  if (lssolver->selected_nums == 0){
    update_clause_weights(lssolver);
    return;
  }
  
  if (lssolver->selected_nums == 1){
    update_clause_weights(lssolver);
    flip(lssolver,lssolver->best_vars[0]);
    lssolver->time_stamp[lssolver->best_vars[0]]=lssolver->step;
    lssolver->step++;
    return;
  }
  
  int max_score1 = -10000000, max_score2 = -10000000;
  int num1 = 0, num2 = 0;
  
  for (i = 0; i < lssolver->selected_nums; i++)
  {
      lssolver->scores[i] = lssolver->score[lssolver->best_vars[i]];
      if (lssolver->score[lssolver->best_vars[i]] > max_score1){
          max_score1 = lssolver->score[lssolver->best_vars[i]]; num1 = i;
      }
      else if (lssolver->score[lssolver->best_vars[i]] == max_score1){
          if (lssolver->time_stamp[lssolver->best_vars[i]] < lssolver->time_stamp[lssolver->best_vars[num1]])
              num1 = i;
      }
  }
  
  int j;
  
  for (i = 0; i < lssolver->selected_nums; i++)
  {
      //goodvar_stack2_num = 0;
      flip2(lssolver,lssolver->best_vars[i]);
      
      if (lssolver->goodvar_stack2_num > 0){
          if (lssolver->goodvar_stack2_num < 50)
          {
              lssolver->vars2[i] = lssolver->goodvar_stack2[0];
              for (j = 1; j < lssolver->goodvar_stack2_num; ++j)
              {
                  v = lssolver->goodvar_stack2[j];
                  if (lssolver->score2[v] > lssolver->score2[lssolver->vars2[i]])
                      lssolver->vars2[i] = v;
                  else if (lssolver->score2[v] == lssolver->score2[lssolver->vars2[i]])
                  {
                      if (lssolver->time_stamp[v] < lssolver->time_stamp[lssolver->vars2[i]])
                          lssolver->vars2[i] = v;
                  }
              }
          }
          else
          {
              lssolver->vars2[i] = lssolver->goodvar_stack2[hywalk_rand(lssolver,lssolver->goodvar_stack2_num)];
              for (j = 1; j < 50; ++j)
              {
                  v = lssolver->goodvar_stack2[hywalk_rand(lssolver,lssolver->goodvar_stack2_num)];
                  if (lssolver->score2[v] > lssolver->score2[lssolver->vars2[i]])
                      lssolver->vars2[i] = v;
                  else if (lssolver->score2[v] == lssolver->score2[lssolver->vars2[i]])
                  {
                      if (lssolver->time_stamp[v] < lssolver->time_stamp[lssolver->vars2[i]])
                          lssolver->vars2[i] = v;
                  }
              }
          }
          lssolver->scores[i] += lssolver->score2[lssolver->vars2[i]];
          if (lssolver->scores[i] > 0){
              flip(lssolver,lssolver->best_vars[i]);
              lssolver->time_stamp[lssolver->best_vars[i]] = lssolver->step;
              lssolver->step++;
              flip(lssolver,lssolver->vars2[i]);
              lssolver->time_stamp[lssolver->vars2[i]] = lssolver->step;
              lssolver->step++;
              return;
          }
      }
      else{
          lssolver->scores[i] -= 1000;
      }

      if (lssolver->scores[i] > max_score1){
          if (lssolver->scores[i] > max_score2){
              max_score2 = lssolver->scores[i]; num2 = i;
          }
          else if (lssolver->scores[i] == max_score2){
              if (lssolver->time_stamp[lssolver->best_vars[i]] + lssolver->time_stamp[lssolver->vars2[i]] < lssolver->time_stamp[lssolver->best_vars[num2]] + lssolver->time_stamp[lssolver->vars2[num2]])
                  num2 = i;
          }
      }
  }
  update_clause_weights(lssolver);
  
  if (max_score1 >= max_score2){
      flip(lssolver,lssolver->best_vars[num1]);
      lssolver->time_stamp[lssolver->best_vars[num1]] = lssolver->step;
      lssolver->step++;
      return;
  }
  else{
      flip(lssolver,lssolver->best_vars[num2]); 
      lssolver->time_stamp[lssolver->best_vars[num2]] = lssolver->step;
      lssolver->step++;
      flip(lssolver,lssolver->vars2[num2]);
      lssolver->time_stamp[lssolver->vars2[num2]] = lssolver->step;
      lssolver->step++;
      return;
  }
}

void pick_var_BandSAT(HyWalk *lssolver)
{
  int         i,k,c,v;
	int         best_var;
	lit*		clause_c;
	
  lssolver->tabu_step = 1;
 
	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(lssolver->goodvar_stack_fill_pointer>0)
	{
		lssolver->mems_left -= lssolver->goodvar_stack_fill_pointer;
		best_var = lssolver->goodvar_stack[0];
		
		for(i=1; i<lssolver->goodvar_stack_fill_pointer; ++i)
		{
			v=lssolver->goodvar_stack[i];
			if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
			else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
		}
		
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
		//return best_var;
	}
	
	/*SD (significant decreasing) mode, the level with aspiration*/
	best_var = 0;
	for(i=0; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		if(lssolver->score[lssolver->unsatvar_stack[i]]>lssolver->ave_weight) 
		{
			best_var = lssolver->unsatvar_stack[i];
			break;
		}
	}

	for(++i; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		v=lssolver->unsatvar_stack[i];
		if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
		else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
	}
		
	if(best_var!=0){
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
    //return best_var;
  }
		
	/**Diversification Mode**/
	update_clause_weights(lssolver);
 
  int sel_c;
  lit* p;
  
  lssolver->sampled_clauses[0] = lssolver->unsat_stack[hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];
  for (int i = 1; i < 20; i++){
      lssolver->sampled_clauses[i] = lssolver->unsat_stack[hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];
  }
  //else{
  double max_value = lssolver->clause_score[lssolver->sampled_clauses[0]] + 0.1 * sqrt((log(lssolver->local_times + 1)) / ((double)(lssolver->selected_times[lssolver->sampled_clauses[0]] + 1)));
  sel_c = lssolver->sampled_clauses[0];
  for (int i = 1; i < 20; i++){
      double dtemp = lssolver->clause_score[lssolver->sampled_clauses[i]] + 0.1 * sqrt((log(lssolver->local_times + 1)) / ((double)(lssolver->selected_times[lssolver->sampled_clauses[i]] + 1)));
      if (dtemp > max_value){
          max_value = dtemp;
          sel_c = lssolver->sampled_clauses[i];
      }
  }
  //printf("%0.2f ",lssolver->clause_score[sel_c]);
  //}
  lssolver->selected_times[sel_c]++;
  lssolver->selected_clauses[lssolver->local_times % 21] = sel_c;
  if (lssolver->local_times > 0){
      int s = lssolver->pre_unsat_nb - lssolver->unsat_stack_fill_pointer;
      update_clause_scores(lssolver,s);
  }
  lssolver->pre_unsat_nb = lssolver->unsat_stack_fill_pointer;
  lssolver->local_times++;
  
  best_var = 0;
  int j;
  int max_score = -10000000;
  
  p = lssolver->clause_lit[sel_c];
  
  for (j = 0; j < lssolver->clause_lit_count[sel_c]; j++){
    v = p[j].var_num;
    //if (lssolver->cscc[v]==0)
    //  continue;
    if (lssolver->score[v] > max_score){
      max_score = lssolver->score[v];
      best_var = v;
    }
    else if (lssolver->score[v] == max_score && lssolver->time_stamp[v] < lssolver->time_stamp[best_var])
      best_var = v;
  }
  
  if (best_var > 0){
  	flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
  }
  return;
  
  /*
  best_var = lssolver->clause_lit[sel_c][0].var_num;
  p = lssolver->clause_lit[sel_c];
  
  for (p++; (v = p->var_num) != 0; p++)
  {
      if (lssolver->score[v] > lssolver->score[best_var])
          best_var = v;
      else if (lssolver->score[v] == lssolver->score[best_var])
      {
          if (lssolver->time_stamp[v] < lssolver->time_stamp[best_var])
              best_var = v;
      }
  }
  */
  
}

void pick_var_FS(HyWalk *lssolver)
{
  int         i,j,k,c,v;
	int         best_var;
	lit*		clause_c;
	
  lssolver->tabu_step = 1;
 
	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(lssolver->goodvar_stack_fill_pointer>0)
	{
		lssolver->mems_left -= lssolver->goodvar_stack_fill_pointer;
		best_var = lssolver->goodvar_stack[0];
		
		for(i=1; i<lssolver->goodvar_stack_fill_pointer; ++i)
		{
			v=lssolver->goodvar_stack[i];
			if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
			else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
		}
		
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
		//return best_var;
	}
	
	/*SD (significant decreasing) mode, the level with aspiration*/
	best_var = 0;
	for(i=0; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		if(lssolver->score[lssolver->unsatvar_stack[i]]>lssolver->ave_weight) 
		{
			best_var = lssolver->unsatvar_stack[i];
			break;
		}
	}

	for(++i; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		v=lssolver->unsatvar_stack[i];
		if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
		else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
	}
		
	if(best_var!=0){
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
    //return best_var;
  }
  
  lssolver->selected_nums = 10;
    
  for (i = 0; i < 10; i++){
      lssolver->sel_cs[i] = lssolver->unsat_stack[hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];
  }

  int max_score1 = -10000000, max_score2 = -10000000;
  int num1_v = 0, num2 = 0;
  
  int best_vars_num = 0;
  
  for (i = 0; i < 10; i++){
      //int v_best = lssolver->clause_lit[lssolver->sel_cs[i]][hywalk_rand(lssolver,lssolver->clause_lit_count[lssolver->sel_cs[i]])].var_num;
      int max_score = -10000000;
      int v_best = 0;
      for (j = 0; j < 5; j++){
          v = lssolver->clause_lit[lssolver->sel_cs[i]][hywalk_rand(lssolver,lssolver->clause_lit_count[lssolver->sel_cs[i]])].var_num;
          if (lssolver->cscc[v] == 0)
            continue;
          if (lssolver->score[v] > max_score){
              v_best = v;
              max_score = lssolver->score[v];
          }
          else if (lssolver->score[v] == max_score){
              if (lssolver->time_stamp[v] < lssolver->time_stamp[v_best]){
                  v_best = v;
              }
          }
      }
      lssolver->best_vars[best_vars_num] = v_best;
      if (lssolver->selected[lssolver->best_vars[best_vars_num]] || v_best == 0){
          lssolver->selected_nums--;
      }
      else {
          lssolver->selected[lssolver->best_vars[best_vars_num]] = 1;
          best_vars_num++;
          if (lssolver->score[v_best] > max_score1){
              num1_v = v_best; max_score1 = lssolver->score[v_best];
          }
          else if (lssolver->score[v_best] == max_score1){
              if (lssolver->time_stamp[v_best] < lssolver->time_stamp[num1_v])
                  num1_v = v_best;
          }
      }
  }
  
  for (i = 0; i < lssolver->selected_nums; i++){
      lssolver->scores[i] = lssolver->score[lssolver->best_vars[i]];
      lssolver->selected[lssolver->best_vars[i]] = 0;
  }
  
  if (lssolver->selected_nums == 0){
      update_clause_weights(lssolver);
      return;
  }
  
  if (lssolver->selected_nums == 1){
      update_clause_weights(lssolver);
      flip(lssolver,lssolver->best_vars[0]);
      lssolver->time_stamp[lssolver->best_vars[0]]=lssolver->step;
      lssolver->step++;
      return;
  }
  
  for (i = 0; i < lssolver->selected_nums; i++)
  {
      //goodvar_stack2_num = 0;
      flip2(lssolver,lssolver->best_vars[i]);

      if (lssolver->goodvar_stack2_num > 0){
          if (lssolver->goodvar_stack2_num < 50)
          {
              lssolver->vars2[i] = lssolver->goodvar_stack2[0];
              for (j = 1; j < lssolver->goodvar_stack2_num; ++j)
              {
                  v = lssolver->goodvar_stack2[j];
                  if (lssolver->score2[v] > lssolver->score2[lssolver->vars2[i]])
                      lssolver->vars2[i] = v;
                  else if (lssolver->score2[v] == lssolver->score2[lssolver->vars2[i]])
                  {
                      if (lssolver->time_stamp[v] < lssolver->time_stamp[lssolver->vars2[i]])
                          lssolver->vars2[i] = v;
                  }
              }
          }
          else
          {
              lssolver->vars2[i] = lssolver->goodvar_stack2[hywalk_rand(lssolver,lssolver->goodvar_stack2_num)];
              for (j = 1; j < 50; ++j)
              {
                  v = lssolver->goodvar_stack2[hywalk_rand(lssolver,lssolver->goodvar_stack2_num)];
                  if (lssolver->score2[v] > lssolver->score2[lssolver->vars2[i]])
                      lssolver->vars2[i] = v;
                  else if (lssolver->score2[v] == lssolver->score2[lssolver->vars2[i]])
                  {
                      if (lssolver->time_stamp[v] < lssolver->time_stamp[lssolver->vars2[i]])
                          lssolver->vars2[i] = v;
                  }
              }
          }
          lssolver->scores[i] += lssolver->score2[lssolver->vars2[i]];
          if (lssolver->scores[i] > 0){
              flip(lssolver,lssolver->best_vars[i]);
              lssolver->time_stamp[lssolver->best_vars[i]] = lssolver->step;
              lssolver->step++;
              flip(lssolver,lssolver->vars2[i]);
              lssolver->time_stamp[lssolver->vars2[i]] = lssolver->step;
              lssolver->step++;
              return;
          }
      }
      else{
          lssolver->scores[i] -= 1000;
      }

      if (lssolver->scores[i] > max_score1){
          if (lssolver->scores[i] > max_score2){
              max_score2 = lssolver->scores[i]; num2 = i;
          }
          else if (lssolver->scores[i] == max_score2){
              if (lssolver->time_stamp[lssolver->best_vars[i]] + lssolver->time_stamp[lssolver->vars2[i]] < lssolver->time_stamp[lssolver->best_vars[num2]] + lssolver->time_stamp[lssolver->vars2[num2]])
                  num2 = i;
          }
      }
  }
  update_clause_weights(lssolver);
  if (max_score1 >= max_score2){
      flip(lssolver,num1_v);
      lssolver->time_stamp[num1_v] = lssolver->step;
      lssolver->step++;
      return;
  }
  else{
      flip(lssolver,lssolver->best_vars[num2]); 
      lssolver->time_stamp[lssolver->best_vars[num2]] = lssolver->step;
      lssolver->step++;
      flip(lssolver,lssolver->vars2[num2]);
      lssolver->time_stamp[lssolver->vars2[num2]] = lssolver->step;
      lssolver->step++;
      return;
  }
}

void pick_var_BF(HyWalk *lssolver)
{
  int         i,k,c,v;
	int         best_var;
	lit*		clause_c;
	
  lssolver->tabu_step = 1;
 
	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(lssolver->goodvar_stack_fill_pointer>0)
	{
		lssolver->mems_left -= lssolver->goodvar_stack_fill_pointer;
		best_var = lssolver->goodvar_stack[0];
		
		for(i=1; i<lssolver->goodvar_stack_fill_pointer; ++i)
		{
			v=lssolver->goodvar_stack[i];
			if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
			else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
		}
		
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
		//return best_var;
	}
	
	/*SD (significant decreasing) mode, the level with aspiration*/
	best_var = 0;
	for(i=0; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		if(lssolver->score[lssolver->unsatvar_stack[i]]>lssolver->ave_weight) 
		{
			best_var = lssolver->unsatvar_stack[i];
			break;
		}
	}

	for(++i; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		v=lssolver->unsatvar_stack[i];
		if(lssolver->score[v]>lssolver->score[best_var]) best_var = v;
		else if(lssolver->score[v]==lssolver->score[best_var] && lssolver->time_stamp[v]<lssolver->time_stamp[best_var]) best_var = v;
	}
		
	if(best_var!=0){
    flip(lssolver,best_var);
    lssolver->time_stamp[best_var] = lssolver->step;
    lssolver->step++;
    return;
    //return best_var;
  }
		
	/**Diversification Mode**/
	//update_clause_weights(lssolver);
 
  int sel_c;
  lit* p;
  
  lssolver->sampled_clauses[0] = lssolver->unsat_stack[hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];
  for (int i = 1; i < 20; i++){
      lssolver->sampled_clauses[i] = lssolver->unsat_stack[hywalk_rand(lssolver,lssolver->unsat_stack_fill_pointer)];
  }
  //else{
  double max_value = lssolver->clause_score[lssolver->sampled_clauses[0]] + 0.1 * sqrt((log(lssolver->local_times + 1)) / ((double)(lssolver->selected_times[lssolver->sampled_clauses[0]] + 1)));
  sel_c = lssolver->sampled_clauses[0];
  for (int i = 1; i < 20; i++){
      double dtemp = lssolver->clause_score[lssolver->sampled_clauses[i]] + 0.1 * sqrt((log(lssolver->local_times + 1)) / ((double)(lssolver->selected_times[lssolver->sampled_clauses[i]] + 1)));
      if (dtemp > max_value){
          max_value = dtemp;
          sel_c = lssolver->sampled_clauses[i];
      }
  }
  //printf("%0.2f ",lssolver->clause_score[sel_c]);
  //}
  lssolver->selected_times[sel_c]++;
  lssolver->selected_clauses[lssolver->local_times % 21] = sel_c;
  if (lssolver->local_times > 0){
      int s = lssolver->pre_unsat_nb - lssolver->unsat_stack_fill_pointer;
      update_clause_scores(lssolver,s);
  }
  lssolver->pre_unsat_nb = lssolver->unsat_stack_fill_pointer;
  lssolver->local_times++;
  
  /*
  if (lssolver->clause_lit_count[sel_c] <= 10){
      int best_vars_num = 0;
      for (int i = 0; i < lssolver->clause_lit_count[sel_c]; i++){
          v = lssolver->clause_lit[sel_c][i].var_num;
          //if (lssolver->cscc[v] == 0)
          //    continue;
          lssolver->best_vars[best_vars_num] = v;
          best_vars_num++;
      }
      lssolver->selected_nums = best_vars_num;
  }
  else{
  */
  lssolver->selected_nums = 10;
  int best_vars_num = 0;
  for (int i = 0; i < 10; i++){
      lssolver->best_vars[best_vars_num] = lssolver->clause_lit[sel_c][hywalk_rand(lssolver,lssolver->clause_lit_count[sel_c])].var_num;
      //if (lssolver->cscc[lssolver->best_vars[best_vars_num]] == 0)
      //    continue;
      if (lssolver->selected[lssolver->best_vars[best_vars_num]]){
          lssolver->selected_nums--;
      }
      else {
          lssolver->selected[lssolver->best_vars[best_vars_num]] = 1;
          best_vars_num++;
      }
  }
  //}
  
  for (i = 0; i < lssolver->selected_nums; i++)
      lssolver->selected[lssolver->best_vars[i]] = 0;
  
  if (lssolver->selected_nums == 0){
      update_clause_weights(lssolver);
      return;
  }
  
  if (lssolver->selected_nums == 1){
      update_clause_weights(lssolver);
      flip(lssolver,lssolver->best_vars[0]);
      lssolver->time_stamp[lssolver->best_vars[0]] = lssolver->step;
      lssolver->step++;
      return;
  }
  
  int max_score1 = -10000000, max_score2 = -10000000;
  int num1 = 0, num2 = 0;
  
  for (i = 0; i < lssolver->selected_nums; i++)
  {
      lssolver->scores[i] = lssolver->score[lssolver->best_vars[i]];
      if (lssolver->score[lssolver->best_vars[i]] > max_score1){
          max_score1 = lssolver->score[lssolver->best_vars[i]]; num1 = i;
      }
      else if (lssolver->score[lssolver->best_vars[i]] == max_score1){
          if (lssolver->time_stamp[lssolver->best_vars[i]] < lssolver->time_stamp[lssolver->best_vars[num1]])
              num1 = i;
      }
  }
  
  int j;
  
  for (i = 0; i < lssolver->selected_nums; i++)
  {
      //goodvar_stack2_num = 0;
      flip2(lssolver,lssolver->best_vars[i]);

      if (lssolver->goodvar_stack2_num > 0){
          if (lssolver->goodvar_stack2_num < 50)
          {
              lssolver->vars2[i] = lssolver->goodvar_stack2[0];
              for (j = 1; j < lssolver->goodvar_stack2_num; ++j)
              {
                  v = lssolver->goodvar_stack2[j];
                  if (lssolver->score2[v] > lssolver->score2[lssolver->vars2[i]])
                      lssolver->vars2[i] = v;
                  else if (lssolver->score2[v] == lssolver->score2[lssolver->vars2[i]])
                  {
                      if (lssolver->time_stamp[v] < lssolver->time_stamp[lssolver->vars2[i]])
                          lssolver->vars2[i] = v;
                  }
              }
          }
          else
          {
              lssolver->vars2[i] = lssolver->goodvar_stack2[hywalk_rand(lssolver,lssolver->goodvar_stack2_num)];
              for (j = 1; j < 50; ++j)
              {
                  v = lssolver->goodvar_stack2[hywalk_rand(lssolver,lssolver->goodvar_stack2_num)];
                  if (lssolver->score2[v] > lssolver->score2[lssolver->vars2[i]])
                      lssolver->vars2[i] = v;
                  else if (lssolver->score2[v] == lssolver->score2[lssolver->vars2[i]])
                  {
                      if (lssolver->time_stamp[v] < lssolver->time_stamp[lssolver->vars2[i]])
                          lssolver->vars2[i] = v;
                  }
              }
          }
          lssolver->scores[i] += lssolver->score2[lssolver->vars2[i]];
          if (lssolver->scores[i] > 0){
              flip(lssolver,lssolver->best_vars[i]);
              lssolver->time_stamp[lssolver->best_vars[i]] = lssolver->step;
              lssolver->step++;
              flip(lssolver,lssolver->vars2[i]);
              lssolver->time_stamp[lssolver->vars2[i]] = lssolver->step;
              lssolver->step++;
              return;
          }
      }
      else{
          lssolver->scores[i] -= 1000;
      }

      if (lssolver->scores[i] > max_score1){
          if (lssolver->scores[i] > max_score2){
              max_score2 = lssolver->scores[i]; num2 = i;
          }
          else if (lssolver->scores[i] == max_score2){
              if (lssolver->time_stamp[lssolver->best_vars[i]] + lssolver->time_stamp[lssolver->vars2[i]] < lssolver->time_stamp[lssolver->best_vars[num2]] + lssolver->time_stamp[lssolver->vars2[num2]])
                  num2 = i;
          }
      }
      //flip(lssolver,lssolver->best_vars[i]);
      //flip(best_vars[i]);
  }
  update_clause_weights(lssolver);
  if (max_score1 >= max_score2){
      flip(lssolver,lssolver->best_vars[num1]);
      lssolver->time_stamp[lssolver->best_vars[num1]] = lssolver->step;
      lssolver->step++;
      return;
  }
  else{
      flip(lssolver,lssolver->best_vars[num2]); 
      lssolver->time_stamp[lssolver->best_vars[num2]] = lssolver->step;
      lssolver->step++;
      flip(lssolver,lssolver->vars2[num2]);
      lssolver->time_stamp[lssolver->vars2[num2]] = lssolver->step;
      lssolver->step++;
      return;
  }
}

//set functions in the algorithm
void settings(HyWalk *lssolver,char *soln)
{
	set_clause_weighting(lssolver);
	init(lssolver,soln);
}

bool local_search(HyWalk *lssolver)
{
	int flipvar;
	lssolver->best_cost = lssolver->num_clauses;
  
  int NVARS = lssolver->num_vars;
  int NCLS = lssolver->num_clauses;
  double CLS_TO_VAR = ((double) NCLS) / ((double) NVARS);
  int MIN_LEN = lssolver->min_clause_len;
  double AVG_LEN = lssolver->avg_clause_len;
  int MAX_LEN = lssolver->max_clause_len;
  
  int selected_strategy = select_strategy_by_decision_tree(lssolver, NVARS, NCLS, CLS_TO_VAR, MIN_LEN, AVG_LEN, MAX_LEN);
  
  if (selected_strategy == 1){
    struct tms start_time,now;
  
    times(&start_time);
    
    lssolver->step = 0;
    while(1)
    {
      times(&now);
      
      if (lssolver->step >= lssolver->max_flips || (double)(now.tms_utime - start_time.tms_utime + now.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK) > 300)
        break;
        
  		if(lssolver->unsat_stack_fill_pointer < lssolver->best_cost){
  			lssolver->best_cost = lssolver->unsat_stack_fill_pointer;
  			for(int i=1;i<=lssolver->num_vars;++i) lssolver->best_soln[i]=lssolver->cur_soln[i];
  		}
  		if(lssolver->unsat_stack_fill_pointer==0) return true;
  		if(lssolver->mems_left<0 && lssolver->step>1000) return false;
     
      pick_var(lssolver);
  		//flipvar = pick_var(lssolver);
  		//flip(lssolver,flipvar);
  		//lssolver->time_stamp[flipvar] = lssolver->step;
  
  		//update conflicts information 
  		for(int i=0;i<lssolver->unsatvar_stack_fill_pointer;++i)
  			++lssolver->conflict_ct[lssolver->unsatvar_stack[i]];
  
  	}
  	return false;
  }
  else if (selected_strategy == 2){
    struct tms start_time,now;
  
    times(&start_time);
    
    lssolver->step = 0;
    while(1)
    {
      times(&now);
      
      if (lssolver->step >= lssolver->max_flips || (double)(now.tms_utime - start_time.tms_utime + now.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK) > 300)
        break;
        
  		if(lssolver->unsat_stack_fill_pointer < lssolver->best_cost){
  			lssolver->best_cost = lssolver->unsat_stack_fill_pointer;
  			for(int i=1;i<=lssolver->num_vars;++i) lssolver->best_soln[i]=lssolver->cur_soln[i];
  		}
  		if(lssolver->unsat_stack_fill_pointer==0) return true;
  		if(lssolver->mems_left<0 && lssolver->step>1000) return false;
     
      pick_var_BandSAT(lssolver);
  		//flipvar = pick_var(lssolver);
  		//flip(lssolver,flipvar);
  		//lssolver->time_stamp[flipvar] = lssolver->step;
  
  		//update conflicts information 
  		for(int i=0;i<lssolver->unsatvar_stack_fill_pointer;++i)
  			++lssolver->conflict_ct[lssolver->unsatvar_stack[i]];
  
  	}
  	return false;
  }
  else if (selected_strategy == 3){
    struct tms start_time,now;
  
    times(&start_time);
    
    lssolver->step = 0;
    while(1)
    {
      times(&now);
      
      if (lssolver->step >= lssolver->max_flips || (double)(now.tms_utime - start_time.tms_utime + now.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK) > 300)
        break;
        
  		if(lssolver->unsat_stack_fill_pointer < lssolver->best_cost){
  			lssolver->best_cost = lssolver->unsat_stack_fill_pointer;
  			for(int i=1;i<=lssolver->num_vars;++i) lssolver->best_soln[i]=lssolver->cur_soln[i];
  		}
  		if(lssolver->unsat_stack_fill_pointer==0) return true;
  		if(lssolver->mems_left<0 && lssolver->step>1000) return false;
     
      pick_var_BF(lssolver);
  		//flipvar = pick_var(lssolver);
  		//flip(lssolver,flipvar);
  		//lssolver->time_stamp[flipvar] = lssolver->step;
  
  		//update conflicts information 
  		for(int i=0;i<lssolver->unsatvar_stack_fill_pointer;++i)
  			++lssolver->conflict_ct[lssolver->unsatvar_stack[i]];
  
  	}
  	return false;
  }
  else if (selected_strategy == 4){
    struct tms start_time,now;
  
    times(&start_time);
    
    lssolver->step = 0;
    while(1)
    {
      times(&now);
      
      if (lssolver->step >= lssolver->max_flips || (double)(now.tms_utime - start_time.tms_utime + now.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK) > 300)
        break;
        
  		if(lssolver->unsat_stack_fill_pointer < lssolver->best_cost){
  			lssolver->best_cost = lssolver->unsat_stack_fill_pointer;
  			for(int i=1;i<=lssolver->num_vars;++i) lssolver->best_soln[i]=lssolver->cur_soln[i];
  		}
  		if(lssolver->unsat_stack_fill_pointer==0) return true;
  		if(lssolver->mems_left<0 && lssolver->step>1000) return false;
     
      pick_var_FPS(lssolver);
  		//flipvar = pick_var(lssolver);
  		//flip(lssolver,flipvar);
  		//lssolver->time_stamp[flipvar] = lssolver->step;
  
  		//update conflicts information 
  		for(int i=0;i<lssolver->unsatvar_stack_fill_pointer;++i)
  			++lssolver->conflict_ct[lssolver->unsatvar_stack[i]];
  
  	}
  	return false;
  }
  else if (selected_strategy == 5){
    struct tms start_time,now;
  
    times(&start_time);
    
    lssolver->step = 0;
    while(1)
    {
      times(&now);
      
      if (lssolver->step >= lssolver->max_flips || (double)(now.tms_utime - start_time.tms_utime + now.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK) > 300)
        break;
        
  		if(lssolver->unsat_stack_fill_pointer < lssolver->best_cost){
  			lssolver->best_cost = lssolver->unsat_stack_fill_pointer;
  			for(int i=1;i<=lssolver->num_vars;++i) lssolver->best_soln[i]=lssolver->cur_soln[i];
  		}
  		if(lssolver->unsat_stack_fill_pointer==0) return true;
  		if(lssolver->mems_left<0 && lssolver->step>1000) return false;
     
      pick_var_FS(lssolver);
  		//flipvar = pick_var(lssolver);
  		//flip(lssolver,flipvar);
  		//lssolver->time_stamp[flipvar] = lssolver->step;
  
  		//update conflicts information 
  		for(int i=0;i<lssolver->unsatvar_stack_fill_pointer;++i)
  			++lssolver->conflict_ct[lssolver->unsatvar_stack[i]];
  
  	}
  	return false;
  }
  else {
    struct tms start_time,now;
  
    times(&start_time);
    
    lssolver->step = 0;
    while(1)
    {
      times(&now);
      
      if (lssolver->step >= lssolver->max_flips || (double)(now.tms_utime - start_time.tms_utime + now.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK) > 300)
        break;
        
  		if(lssolver->unsat_stack_fill_pointer < lssolver->best_cost){
  			lssolver->best_cost = lssolver->unsat_stack_fill_pointer;
  			for(int i=1;i<=lssolver->num_vars;++i) lssolver->best_soln[i]=lssolver->cur_soln[i];
  		}
  		if(lssolver->unsat_stack_fill_pointer==0) return true;
  		if(lssolver->mems_left<0 && lssolver->step>1000) return false;
     
      pick_var_Simple(lssolver);
  		//flipvar = pick_var(lssolver);
  		//flip(lssolver,flipvar);
  		//lssolver->time_stamp[flipvar] = lssolver->step;
  
  		//update conflicts information 
  		for(int i=0;i<lssolver->unsatvar_stack_fill_pointer;++i)
  			++lssolver->conflict_ct[lssolver->unsatvar_stack[i]];
  
  	}
  	return false;
  }
}



inline void unsat(HyWalk *lssolver, int clause)
{
	lssolver->index_in_unsat_stack[clause] = lssolver->unsat_stack_fill_pointer;
	push(clause,lssolver->unsat_stack);
	
	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v;
	for(lit* p=lssolver->clause_lit[clause]; (v=p->var_num)!=0; p++)
	{	
		lssolver->unsat_app_count[v]++;
		if(lssolver->unsat_app_count[v]==1)
		{
			lssolver->index_in_unsatvar_stack[v] = lssolver->unsatvar_stack_fill_pointer;
			push(v,lssolver->unsatvar_stack);	
		}
	}
}

inline void sat(HyWalk *lssolver, int clause)
{
	int index,last_unsat_clause;

	//since the clause is satisfied, its position can be reused to store the last_unsat_clause
	last_unsat_clause = pop(lssolver->unsat_stack);
	index = lssolver->index_in_unsat_stack[clause];
	lssolver->unsat_stack[index] = last_unsat_clause;
	lssolver->index_in_unsat_stack[last_unsat_clause] = index;
	
	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v,last_unsat_var;
	for(lit* p=lssolver->clause_lit[clause]; (v=p->var_num)!=0; p++)
	{	
		lssolver->unsat_app_count[v]--;
		if(lssolver->unsat_app_count[v]==0)
		{
			last_unsat_var = pop(lssolver->unsatvar_stack);
			index = lssolver->index_in_unsatvar_stack[v];
			lssolver->unsatvar_stack[index] = last_unsat_var;
			lssolver->index_in_unsatvar_stack[last_unsat_var] = index;
		}
	}
}

//initiation of the algorithm
void init(HyWalk *lssolver,char *soln)
{
	int 		v,c;
	int			i,j;
	
  lssolver->local_times = 0;
 
	//Initialize edge weights
	for (c = 0; c<lssolver->num_clauses; c++){
    lssolver->clause_score[c] = 1;
    lssolver->selected_times[c] = 0;
		lssolver->clause_weight[c] = 1;
  }

	//init unsat_stack
	lssolver->unsat_stack_fill_pointer = 0;
	lssolver->unsatvar_stack_fill_pointer = 0;

	//init solution
	for (v = 1; v <= lssolver->num_vars; v++) {
        
        if(lssolver->fix[v]==0){
			if(soln==NULL){
				if(hywalk_rand(lssolver,2)==1) lssolver->cur_soln[v] = 1;
				else lssolver->cur_soln[v] = 0;
			}else{
				lssolver->cur_soln[v] = soln[v-1];
			}
      
      lssolver->selected[v] = 0;
			lssolver->time_stamp[v] = 0;
			lssolver->unsat_app_count[v] = 0;
			lssolver->cscc[v] = 1;
      lssolver->cscc2[v] = 0;
			lssolver->score_inc_flag[v]=0;
		}
		
		
	}

	/* figure out sat_count, and init unsat_stack */
	for (c=0; c<lssolver->num_clauses; ++c) 
	{
		if(lssolver->clause_delete[c]==1) continue;
		
		lssolver->sat_count[c] = 0;
		
		for(j=0; j<lssolver->clause_lit_count[c]; ++j)
		{
			if (lssolver->cur_soln[lssolver->clause_lit[c][j].var_num] == lssolver->clause_lit[c][j].sense)
			{
				lssolver->sat_count[c]++;
				lssolver->sat_var[c] = lssolver->clause_lit[c][j].var_num;	
			}
		}

		if (lssolver->sat_count[c] == 0) 
			unsat(lssolver,c);
	}

	/*figure out var score*/
	int lit_count;
	for (v=1; v<=lssolver->num_vars; v++) 
	{
		if(lssolver->fix[v]==1) 
		{
			lssolver->score[v] = -10000000;
			continue;
		}
		
		lssolver->score[v] = 0;

		lit_count = lssolver->var_lit_count[v];
		
		for(i=0; i<lit_count; ++i)
		{
			c = lssolver->var_lit[v][i].clause_num;
			if (lssolver->sat_count[c]==0) lssolver->score[v]++;
			else if (lssolver->sat_count[c]==1 && lssolver->var_lit[v][i].sense==lssolver->cur_soln[v]) lssolver->score[v]--;
		}
	}
	
		
	//init goodvars stack
	lssolver->goodvar_stack_fill_pointer = 0;
	for (v=1; v<=lssolver->num_vars; v++) 
	{
		if(lssolver->fix[v]==1)  continue;
		if(lssolver->score[v]>0)// && conf_change[v]==1)
		{
			lssolver->already_in_goodvar_stack[v] = 1;
			push(v,lssolver->goodvar_stack);
			
		}
		else lssolver->already_in_goodvar_stack[v] = 0;
	}
	
	//setting for the virtual var 0
	lssolver->time_stamp[0]=0;
	//pscore[0]=0;
}

void flip(HyWalk *lssolver, int flipvar)
{
	lssolver->cur_soln[flipvar] = 1 - lssolver->cur_soln[flipvar];
	
	lssolver->score_inc_count=0;
	
	int i;
	int v,c;

	lit* clause_c;
	
	int org_flipvar_score = lssolver->score[flipvar];
	
	//update related clauses and neighbor vars
	lssolver->mems_left-=lssolver->var_lit_count[flipvar];
	for(lit *q = lssolver->var_lit[flipvar]; (c=q->clause_num)>=0; q++)
	{
		clause_c = lssolver->clause_lit[c];
		if(lssolver->cur_soln[flipvar] == q->sense)
		{
			++lssolver->sat_count[c];
			
			if (lssolver->sat_count[c] == 2) //sat_count from 1 to 2
			{
				lssolver->score[lssolver->sat_var[c]] += lssolver->clause_weight[c];
				
				if(lssolver->score_inc_flag[lssolver->sat_var[c]]!=1)
				{
					lssolver->score_inc_vars[lssolver->score_inc_count++]=lssolver->sat_var[c];
					lssolver->score_inc_flag[lssolver->sat_var[c]]=1;
				}
			}
			else if (lssolver->sat_count[c] == 1) // sat_count from 0 to 1
			{
				lssolver->sat_var[c] = flipvar;//record the only true lit's var
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
				{
					lssolver->score[v] -= lssolver->clause_weight[c];
					lssolver->cscc[v] = 1;
				}
                
				sat(lssolver,c);
			}
		}
		else // cur_soln[flipvar] != cur_lit.sense
		{
			--lssolver->sat_count[c];
			if (lssolver->sat_count[c] == 1) //sat_count from 2 to 1
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
				{
					if(p->sense == lssolver->cur_soln[v] )
					{
						lssolver->score[v] -= lssolver->clause_weight[c];
						lssolver->sat_var[c] = v;
						break;
					}
				}
			}
			else if (lssolver->sat_count[c] == 0) //sat_count from 1 to 0
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
				{
					lssolver->score[v] += lssolver->clause_weight[c];
					lssolver->cscc[v] = 1;
					
					if(lssolver->score_inc_flag[v]!=1)
					{
					lssolver->score_inc_vars[lssolver->score_inc_count++]=v;
					lssolver->score_inc_flag[v]=1;
					}
				}
				unsat(lssolver,c);
			}//end else if
			
		}//end else
	}

	lssolver->score[flipvar] = -org_flipvar_score;
	
	lssolver->cscc[flipvar] = 0;
	
	/*update CCD */
	int index;
	
	for(index=lssolver->goodvar_stack_fill_pointer-1; index>=0; index--)
	{
		v = lssolver->goodvar_stack[index];
		if(lssolver->score[v]<=0 /*|| (lssolver->time_stamp[v] != 0 && lssolver->step - lssolver->time_stamp[v] <= lssolver->tabu_step)*/)
		{
			lssolver->goodvar_stack[index] = pop(lssolver->goodvar_stack);
			lssolver->already_in_goodvar_stack[v] = 0;
		}	
	}

	
	for (i=0; i<lssolver->score_inc_count; ++i)
	{
		v = lssolver->score_inc_vars[i];
		if(lssolver->score[v]>0 && lssolver->cscc[v]==1 && lssolver->already_in_goodvar_stack[v] == 0 /*&& (lssolver->time_stamp[v] == 0 || lssolver->step - lssolver->time_stamp[v] > lssolver->tabu_step)*/)
		{
			push(v,lssolver->goodvar_stack);
			lssolver->already_in_goodvar_stack[v] = 1;
		}
		lssolver->score_inc_flag[v]=0;
	}
}

void flip2(HyWalk *lssolver, int flipvar)
{
	lssolver->cur_soln[flipvar] = 1 - lssolver->cur_soln[flipvar];
	
	//lssolver->score_inc_count=0;
	
	int i;
	int v,c;

	lit* clause_c;
	
	int org_flipvar_score = lssolver->score[flipvar];
	
  //for (i = 0; i < var_neighbor_count[flipvar]; i++){
  //  score2[var_neighbor[flipvar][i]] = score[var_neighbor[flipvar][i]];
  //}
  int vtemp;
  int selected_during_flip_num = 0;
  
	//update related clauses and neighbor vars
	lssolver->mems_left-=lssolver->var_lit_count[flipvar];
	for(lit *q = lssolver->var_lit[flipvar]; (c=q->clause_num)>=0; q++)
	{
		clause_c = lssolver->clause_lit[c];
		if(lssolver->cur_soln[flipvar] == q->sense)
		{
			//++lssolver->sat_count[c];
			int sc = lssolver->sat_count[c] + 1;
      
			if (sc == 2) //sat_count from 1 to 2
			{
        vtemp = lssolver->sat_var[c];
        if (lssolver->selected[vtemp]){
          lssolver->score2[vtemp] += lssolver->clause_weight[c];
        }
        else{
          lssolver->selected[vtemp] = 1;
          lssolver->selected_during_flip[selected_during_flip_num] = vtemp;
          selected_during_flip_num++;
          lssolver->score2[vtemp] = lssolver->score[vtemp];
          lssolver->score2[vtemp] += lssolver->clause_weight[c];
        }
				//lssolver->score[lssolver->sat_var[c]] += lssolver->clause_weight[c];
				/*
				if(lssolver->score_inc_flag[lssolver->sat_var[c]]!=1)
				{
					lssolver->score_inc_vars[lssolver->score_inc_count++]=lssolver->sat_var[c];
					lssolver->score_inc_flag[lssolver->sat_var[c]]=1;
				}
        */
			}
			else if (sc == 1) // sat_count from 0 to 1
			{
				//lssolver->sat_var[c] = flipvar;//record the only true lit's var
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
				{
          vtemp = v;
          if (lssolver->selected[vtemp]){
            lssolver->score2[vtemp] -= lssolver->clause_weight[c];
          }
          else{
            lssolver->selected[vtemp] = 1;
            lssolver->selected_during_flip[selected_during_flip_num] = vtemp;
            selected_during_flip_num++;
            lssolver->score2[vtemp] = lssolver->score[vtemp];
            lssolver->score2[vtemp] -= lssolver->clause_weight[c];
          }
					//lssolver->score[v] -= lssolver->clause_weight[c];
					lssolver->cscc2[vtemp] = 1;
				}
                
				//sat(lssolver,c);
			}
		}
		else // cur_soln[flipvar] != cur_lit.sense
		{
			//--lssolver->sat_count[c];
      int sc = lssolver->sat_count[c] - 1;
			if (sc == 1) //sat_count from 2 to 1
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
				{
					if(p->sense == lssolver->cur_soln[v] )
					{
            vtemp = v;
            if (lssolver->selected[vtemp]){
              lssolver->score2[vtemp] -= lssolver->clause_weight[c];
            }
            else{
              lssolver->selected[vtemp] = 1;
              lssolver->selected_during_flip[selected_during_flip_num] = vtemp;
              selected_during_flip_num++;
              lssolver->score2[vtemp] = lssolver->score[vtemp];
              lssolver->score2[vtemp] -= lssolver->clause_weight[c];
            }
						//lssolver->score[v] -= lssolver->clause_weight[c];
						//lssolver->sat_var[c] = v;
						break;
					}
				}
			}
			else if (sc == 0) //sat_count from 1 to 0
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
				{
          vtemp = v;
          if (lssolver->selected[vtemp]){
            lssolver->score2[vtemp] += lssolver->clause_weight[c];
          }
          else{
            lssolver->selected[vtemp] = 1;
            lssolver->selected_during_flip[selected_during_flip_num] = vtemp;
            selected_during_flip_num++;
            lssolver->score2[vtemp] = lssolver->score[vtemp];
            lssolver->score2[vtemp] += lssolver->clause_weight[c];
          }
					//lssolver->score[v] += lssolver->clause_weight[c];
					lssolver->cscc2[vtemp] = 1;
					/*
					if(lssolver->score_inc_flag[v]!=1)
					{
					lssolver->score_inc_vars[lssolver->score_inc_count++]=v;
					lssolver->score_inc_flag[v]=1;
					}*/
				}
				//unsat(lssolver,c);
			}//end else if
			
		}//end else
	}
  
  lssolver->cur_soln[flipvar] = 1 - lssolver->cur_soln[flipvar];
	lssolver->score2[flipvar] = -org_flipvar_score;
	
	//lssolver->cscc[flipvar] = 0;
	
	/*update CCD */
 
  lssolver->goodvar_stack2_num = 0;
	//remove the vars no longer goodvar in goodvar stack
	//add goodvar
	for (int i = 0; i < selected_during_flip_num; ++i)
	{
		v = lssolver->selected_during_flip[i];
    if (v == flipvar){
      lssolver->selected[v] = 0;
      lssolver->cscc2[v] = 0;
      continue;
    }
		if (lssolver->score2[v] > 0 && (lssolver->cscc[v] == 1 || lssolver->cscc2[v] == 1) /*&& (lssolver->time_stamp[v] == 0 || lssolver->step - lssolver->time_stamp[v] > lssolver->tabu_step)*/)
		{
			lssolver->goodvar_stack2[lssolver->goodvar_stack2_num] = v;
      lssolver->goodvar_stack2_num++;
		}
    lssolver->selected[v] = 0;
    lssolver->cscc2[v] = 0;
	}
 
  /*
	int index;
	
	for(index=lssolver->goodvar_stack_fill_pointer-1; index>=0; index--)
	{
		v = lssolver->goodvar_stack[index];
		if(lssolver->score[v]<=0 || (lssolver->time_stamp[v] != 0 && lssolver->step - lssolver->time_stamp[v] <= lssolver->tabu_step))
		{
			lssolver->goodvar_stack[index] = pop(lssolver->goodvar_stack);
			lssolver->already_in_goodvar_stack[v] = 0;
		}	
	}

	
	for (i=0; i<lssolver->score_inc_count; ++i)
	{
		v = lssolver->score_inc_vars[i];
		if(lssolver->score[v]>0 && lssolver->cscc[v]==1 && lssolver->already_in_goodvar_stack[v] == 0 && (lssolver->time_stamp[v] == 0 || lssolver->step - lssolver->time_stamp[v] > lssolver->tabu_step))
		{
			push(v,lssolver->goodvar_stack);
			lssolver->already_in_goodvar_stack[v] = 1;
		}
		//lssolver->score_inc_flag[v]=0;
	}
 */
}

void update_after_build(HyWalk *lssolver){
	int i,c,v;
	lssolver->avg_clause_len = (double)(lssolver->formula_len+0.0)/lssolver->num_clauses;
	
	//creat var literal arrays
	for (v=1; v<=lssolver->num_vars; ++v)
	{
		lssolver->var_lit[v] = (lit*)malloc(sizeof(lit)*(lssolver->var_lit_count[v]+1));
		lssolver->var_lit_count[v] = 0;	//reset to 0, for build up the array
	}
	//scan all clauses to build up var literal arrays
	for (c = 0; c < lssolver->num_clauses; ++c) 
	{
		for(i=0; i<lssolver->clause_lit_count[c]; ++i)
		{
			v = lssolver->clause_lit[c][i].var_num;
			lssolver->var_lit[v][lssolver->var_lit_count[v]] = lssolver->clause_lit[c][i];
			++lssolver->var_lit_count[v];
		}
	}
	for (v=1; v<=lssolver->num_vars; ++v) //set boundary
		lssolver->var_lit[v][lssolver->var_lit_count[v]].clause_num=-1;
	
	if(lssolver->unitclause_queue_end_pointer>0) preprocess(lssolver);

}



void smooth_clause_weights(HyWalk *lssolver)
{
	int j,c,v;
	int new_total_weight=0;

	for (v=1; v<=lssolver->num_vars; ++v) 
		lssolver->score[v] = 0;
	
	//smooth clause score and update score of variables
	for (c = 0; c<lssolver->num_clauses; ++c)
	{
		if (lssolver->clause_delete[c]==1) continue;
		
		lssolver->clause_weight[c] = lssolver->clause_weight[c]*lssolver->p_scale+lssolver->scale_ave;
		if(lssolver->clause_weight[c]<1) lssolver->clause_weight[c] = 1;
		
		new_total_weight+=lssolver->clause_weight[c];
		
		//update score of variables in this clause 
		if (lssolver->sat_count[c]==0) 
		{
			for(j=0; j<lssolver->clause_lit_count[c]; ++j)
			{
				lssolver->score[lssolver->clause_lit[c][j].var_num] += lssolver->clause_weight[c];
			}
		}
		else  if(lssolver->sat_count[c]==1)
			lssolver->score[lssolver->sat_var[c]]-=lssolver->clause_weight[c];
	}
	
	lssolver->ave_weight=new_total_weight/lssolver->num_clauses;
}

void update_clause_weights(HyWalk *lssolver)
{
	int i,v;
	lssolver->mems_left -= lssolver->unsat_stack_fill_pointer;
	for(i=0; i < lssolver->unsat_stack_fill_pointer; ++i)
		lssolver->clause_weight[lssolver->unsat_stack[i]]++;
	
	for(i=0; i<lssolver->unsatvar_stack_fill_pointer; ++i)
	{
		v = lssolver->unsatvar_stack[i];
		lssolver->score[v] += lssolver->unsat_app_count[v];
		if(lssolver->score[v]>0 &&  lssolver->cscc[v]==1 && lssolver->already_in_goodvar_stack[v] ==0)
		{
			push(v,lssolver->goodvar_stack);
			lssolver->already_in_goodvar_stack[v] =1;
		}
	}
	
	lssolver->delta_total_weight+=lssolver->unsat_stack_fill_pointer;
	if(lssolver->delta_total_weight>=lssolver->num_clauses)
	{
		lssolver->ave_weight+=1;
		lssolver->delta_total_weight -= lssolver->num_clauses;
		
		//smooth weights
		if(lssolver->ave_weight>lssolver->threshold)
			smooth_clause_weights(lssolver);
	}
}

void set_clause_weighting(HyWalk *lssolver)
{	
	lssolver->threshold=300;
	lssolver->p_scale=0.3;
	if(lssolver->q_init==0)
	{
		if(lssolver->ratio<=15) lssolver->q_scale=0;
		else lssolver->q_scale=0.7;
	}
	else 
	{
		if(lssolver->q_scale<0.5)  //0
			lssolver->q_scale = 0.7;
		else
			lssolver->q_scale = 0;
	}
	
	lssolver->scale_ave=(lssolver->threshold+1)*lssolver->q_scale;
	lssolver->q_init = 1;
}

//preprocess
void unit_propagation(HyWalk *lssolver)
{
    lit uc_lit;
    int uc_clause;
    int uc_var;
    bool uc_sense;
    
    int c;
    int i,j;
    lit cur;
    
    
    for(lssolver->unitclause_queue_beg_pointer=0; lssolver->unitclause_queue_beg_pointer < lssolver->unitclause_queue_end_pointer; lssolver->unitclause_queue_beg_pointer++)
    {
        uc_lit = lssolver->unitclause_queue[lssolver->unitclause_queue_beg_pointer];
        
        uc_var = uc_lit.var_num;
        uc_sense = uc_lit.sense;
        
        if(lssolver->fix[uc_var]==1) {if(uc_sense!=lssolver->cur_soln[uc_var])printf("c wants to fix a variable twice, forbid\n");continue;}
     
        lssolver->cur_soln[uc_var] = uc_sense;//fix the variable in unit clause
        lssolver->fix[uc_var] = 1;
        
        for(i = 0; i<lssolver->var_lit_count[uc_var]; ++i)
        {
            cur = lssolver->var_lit[uc_var][i];
            c = cur.clause_num;
            
            if(lssolver->clause_delete[c]==1) continue;
            
            if(cur.sense == uc_sense)//then remove the clause from var's var_lit[] array
            {
                lssolver->clause_delete[c]=1;
            }
            else
            {
                if(lssolver->clause_lit_count[c]==2)
                {
                    if(lssolver->clause_lit[c][0].var_num == uc_var)
                    {
                        lssolver->unitclause_queue[lssolver->unitclause_queue_end_pointer++] = lssolver->clause_lit[c][1];
                    }
                    else
                    {
                        lssolver->unitclause_queue[lssolver->unitclause_queue_end_pointer++] = lssolver->clause_lit[c][0];
                    }
                    
                    lssolver->clause_delete[c]=1;
                }
                else
                {
                    for(j=0; j<lssolver->clause_lit_count[c]; ++j)
                    {
                        if(lssolver->clause_lit[c][j].var_num == uc_var)
                        {
                            lssolver->clause_lit[c][j]=lssolver->clause_lit[c][lssolver->clause_lit_count[c]-1];
    
                            lssolver->clause_lit_count[c]--;
                            
                            break;
                        }
                    }
                }
            }   
        }   
    }
    
}

void preprocess(HyWalk *lssolver)
{
    int c,v,i;
    int delete_clause_count=0;
    int fix_var_count=0;
    
    unit_propagation(lssolver);
    
    //rescan all clauses to build up var literal arrays
    for (v=1; v<=lssolver->num_vars; ++v) 
        lssolver->var_lit_count[v] = 0;
    
    lssolver->max_clause_len = 0;
	lssolver->min_clause_len = lssolver->num_vars;
    int    formula_len=0;
    
    for (c = 0; c < lssolver->num_clauses; ++c) 
    {
        if(lssolver->clause_delete[c]==1) {
            delete_clause_count++;
            continue;
        }
        
        for(i=0; i<lssolver->clause_lit_count[c]; ++i)
        {
            v = lssolver->clause_lit[c][i].var_num;
            lssolver->var_lit[v][lssolver->var_lit_count[v]] = lssolver->clause_lit[c][i];
            ++lssolver->var_lit_count[v];
        }
        lssolver->clause_lit[c][i].var_num=0; //new clause boundary
        lssolver->clause_lit[c][i].clause_num = -1;
        
        //about clause length
        formula_len += lssolver->clause_lit_count[c];
        
        if(lssolver->clause_lit_count[c] > lssolver->max_clause_len)
            lssolver->max_clause_len = lssolver->clause_lit_count[c];
        else if(lssolver->clause_lit_count[c] < lssolver->min_clause_len)
            lssolver->min_clause_len = lssolver->clause_lit_count[c];
    }
    
    lssolver->avg_clause_len = (double)(formula_len+0.0)/lssolver->num_clauses;
    
    for (v=1; v<=lssolver->num_vars; ++v) 
    {
    	if(lssolver->fix[v]==1)
    	{
    		fix_var_count++;
    	}
        lssolver->var_lit[v][lssolver->var_lit_count[v]].clause_num=-1;//new var_lit boundary
    }
	lssolver->fix_var_ct = fix_var_count;
	lssolver->del_cls_ct = delete_clause_count;
    // printf("c unit propagation fixes %d variables, and deletes %d clauses\n",fix_var_count,delete_clause_count);
    
}



void hywalk_merseene_init(HyWalk* lssolver, int seed){
	hywalk_Mersenne_init_with_seed(&(lssolver->randgen),seed);
}

int hywalk_rand(HyWalk* lssolver,int bound){
	return hywalk_Mersenne_next(&(lssolver->randgen),bound);
}


void hywalk_Mersenne_init_with_seed(hywalk_randgen* randgen, int seed){
	unsigned int s = ((unsigned int) (seed << 1)) + 1;
	randgen->mt[0] = s & 0xffffffffUL;
	for(randgen->mti = 1; randgen->mti < hywalk_Mersenne_N; randgen->mti++) {
		randgen->mt[randgen->mti] = (1812433253UL * (randgen->mt[randgen->mti - 1] ^ (randgen->mt[randgen->mti - 1] >> 30)) + randgen->mti);
		randgen->mt[randgen->mti] &= 0xffffffffUL;
	}
}

int hywalk_Mersenne_next31(hywalk_randgen* randgen){
	unsigned int y;
	static unsigned int mag01[2] = {0x0UL, hywalk_Mersenne_MATRIX_A};
	if(randgen->mti >= hywalk_Mersenne_N) {
		int kk;
		for(kk = 0; kk < hywalk_Mersenne_N - hywalk_Mersenne_M; kk++) {
		y = (randgen->mt[kk] & hywalk_Mersenne_UPPER_MASK) | (randgen->mt[kk + 1] & hywalk_Mersenne_LOWER_MASK);
		randgen->mt[kk] = randgen->mt[kk + hywalk_Mersenne_M] ^ (y >> 1) ^ mag01[y & 0x1UL];
		}
		for(; kk < hywalk_Mersenne_N - 1; kk++) {
		y = (randgen->mt[kk] & hywalk_Mersenne_UPPER_MASK) | (randgen->mt[kk + 1] & hywalk_Mersenne_LOWER_MASK);
		randgen->mt[kk] = randgen->mt[kk + (hywalk_Mersenne_M - hywalk_Mersenne_N)] ^ (y >> 1) ^ mag01[y & 0x1UL];
		}
		y = (randgen->mt[hywalk_Mersenne_N - 1] & hywalk_Mersenne_UPPER_MASK) | (randgen->mt[0] & hywalk_Mersenne_LOWER_MASK);
		randgen->mt[hywalk_Mersenne_N - 1] = randgen->mt[hywalk_Mersenne_M - 1] ^ (y >> 1) ^ mag01[y & 0x1UL];
		randgen->mti = 0;
	}
	y = randgen->mt[randgen->mti++];
	y ^= (y >> 11);
	y ^= (y << 7) & 0x9d2c5680UL;
	y ^= (y << 15) & 0xefc60000UL;
	y ^= (y >> 18);
	return  (int) (y>>1);
}

int hywalk_Mersenne_next(hywalk_randgen* randgen, int bound){
	unsigned int value;
	do {
		value = hywalk_Mersenne_next31(randgen);
	} while(value + (unsigned int) bound >= 0x80000000UL);
	return (int) (value % bound);
}


void init_HyWalk(HyWalk* lssolver){
	int seed = 1;
	hywalk_merseene_init(lssolver,seed);
	default_initialize(lssolver);
}

void reinit_HyWalk(HyWalk *lssolver){
	free_memory(lssolver);
	init_HyWalk(lssolver);
}

void confl_trans(HyWalk* lssolver){
	lssolver->in_conflict_sz = 0;
	if(lssolver->step==0) return;
	for(int i=1;i<=lssolver->num_vars;++i){
		lssolver->conflict_ct[i] = lssolver->conflict_ct[i]*100/lssolver->step;
		if(lssolver->conflict_ct[i]>0){
			lssolver->in_conflict[lssolver->in_conflict_sz++] = i;
		}
	}
}

void update_clause_scores(HyWalk* lssolver, int s) 
{
    int i;
    
    double stemp;

    stemp = ((double) s) / ((double) (lssolver->pre_unsat_nb + 1));
    
    lssolver->if_exceed = 0;
    
    double discount;
    if (lssolver->local_times < 21){
        for (i = 0; i < lssolver->local_times; i++){
            discount = pow(0.9, lssolver->local_times - 1- i);
            lssolver->clause_score[lssolver->selected_clauses[i]] += (discount * ((double) stemp));
            if (abs(lssolver->clause_score[lssolver->selected_clauses[i]]) > lssolver->max_clause_score)
                lssolver->if_exceed = 1;
        }
    }
    else{
        for (i = 0; i < 21; i++){
            if (i == lssolver->local_times % 21)
                continue;
            if (i < lssolver->local_times % 21)
                discount = pow(0.9, lssolver->local_times % 21 - 1 - i);
            else
                discount = pow(0.9, lssolver->local_times % 21 + 21 - 1 - i);
            lssolver->clause_score[lssolver->selected_clauses[i]] += (discount * ((double) stemp));
            if (abs(lssolver->clause_score[lssolver->selected_clauses[i]]) > lssolver->max_clause_score)
                lssolver->if_exceed = 1;
        }
    }
    if (lssolver->if_exceed){
        for (i = 0; i < lssolver->num_clauses; i++){
            lssolver->clause_score[i] = lssolver->clause_score[i] / 2.0;
        }
        lssolver->if_exceed = 0;
    }
}

int select_strategy_by_decision_tree(HyWalk* lssolver, int NVARS, int NCLS, double CLS_TO_VAR, int MIN_LEN, double AVG_LEN, int MAX_LEN) {
    if (NCLS <= 34294.5) {
        if (MAX_LEN <= 51.5) {
            if (CLS_TO_VAR <= 17.988) {
                if (MAX_LEN <= 15) {
                    if (CLS_TO_VAR <= 3.597) {
                        if (CLS_TO_VAR <= 2.124) {
                            if (NVARS <= 17417.5)
                                return 6;
                            return 4;
                        }
                        else if (MAX_LEN <= 3.5)
                            return 6;
                        else if (AVG_LEN <= 3.2857) {
                            if (CLS_TO_VAR <= 2.262)
                                return 1;
                            else if (NVARS <= 3833) {
                                if (AVG_LEN <= 3.278)
                                    return 2;
                                else if (CLS_TO_VAR <= 3.432)
                                    return 2;
                                return 1;
                            }
                            else if (NCLS <= 11087.5) {
                                if (AVG_LEN <= 3.072)
                                    return 6;
                                return 2;
                            }
                            return 3;
                        }
                        else if (MAX_LEN <= 4.5)
                            return 6;
                        return 1;
                    }
                    else if (AVG_LEN <= 3.685)
                        return 5;
                    else if (AVG_LEN <= 4.811)
                        return 3;
                    else if (MAX_LEN <= 7.5)
                        return 6;
                    else if (AVG_LEN <= 5.725)
                        return 3;
                    return 2;
                }
                else if (CLS_TO_VAR <= 17.429) {
                    if (CLS_TO_VAR <= 4.675) {
                        if (MAX_LEN <= 23.5) {
                            if (NCLS <= 30489.5) {
                                if (AVG_LEN <= 2.346)
                                    return 2;
                                else if (NCLS <= 26663.5) {
                                    if (NCLS <= 25008.5)
                                        return 1;
                                    return 4;
                                }
                                return 1;
                            }
                            return 6;
                        }
                        else if (NCLS <= 22490)
                            return 3;
                        return 2;
                    }
                    else if (MAX_LEN <= 18.5)
                        return 4;
                    return 2;
                }
                return 1;
            }
            return 2;
        }
        return 3;
    }
    else if (NVARS <= 26550) {
        if (CLS_TO_VAR <= 17.297) {
            if (MAX_LEN <= 6.5) {
                if (NCLS <= 53587)
                    return 2;
                else if (CLS_TO_VAR <= 12.145)
                    return 1;
                return 5;
            }
            else if (CLS_TO_VAR <= 6.061) {
                if (MAX_LEN <= 9.5)
                    return 5;
                else if (AVG_LEN <= 5.055) {
                    if (MAX_LEN <= 19)
                        return 3;
                    else if (AVG_LEN <= 2.875)
                        return 3;
                    return 1;
                }
                return 5;
            }
            return 3;
        }
        else if (NVARS <= 3261) {
            if (CLS_TO_VAR <= 85.302)
                return 2;
            return 3;
        }
        else if (AVG_LEN <= 18.03)
            return 6;
        return 1;
    }
    else if (MAX_LEN <= 4188.5) {
        if (NCLS <= 2519373) {
            if (CLS_TO_VAR <= 6.962) {
                if (MAX_LEN <= 156.5) {
                    if (AVG_LEN <= 5.793) {
                        if (CLS_TO_VAR <= 2.306) {
                            if (NVARS <= 49712)
                                return 2;
                            else if (MAX_LEN <= 55) {
                                if (NCLS <= 386142) {
                                    if (NCLS <= 229757.5)
                                        return 1;
                                    return 4;
                                }
                                return 1;
                            }
                            return 3;
                        }
                        else if (AVG_LEN <= 3.404) {
                            if (NVARS <= 34024.5)
                                return 4;
                            return 2;
                        }
                        else if (AVG_LEN <= 3.808) {
                            if (NCLS <= 1818564.5)
                                return 3;
                            return 6;
                        }
                        else if (NVARS <= 59688) {
                            if (NVARS <= 31797.5)
                                return 3;
                            return 6;
                        }
                        else if (MAX_LEN <= 36)
                            return 2;
                        return 5;
                    }
                    return 4;
                }
                return 5;
            }
            else if (AVG_LEN <= 2.226)
                return 4;
            else if (MAX_LEN <= 265) {
                if (CLS_TO_VAR <= 18.838)
                    return 1;
                return 3;
            }
            return 6;
        }
        else if (CLS_TO_VAR <= 3.455) {
            if (NCLS <= 9393795.5)
                return 2;
            return 3;
        }
        else if (CLS_TO_VAR <= 5.837)
            return 5;
        else if (AVG_LEN <= 3.583) {
            if (MAX_LEN <= 14.5)
                return 5;
            else if (CLS_TO_VAR <= 10.73) {
                if (MAX_LEN <= 461.5)
                    return 2;
                return 5;
            }
            else if (MAX_LEN <= 206.5) {
                if (NVARS <= 54292.5)
                    return 6;
                else if (NCLS <= 3788694)
                    return 5;
                return 1;
            }
            return 4;
        }
        return 4;
    }
    return 6;
}