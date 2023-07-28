#include "ccanr.h"


//-------------------

void ccanr_Mersenne_init_with_seed(ccanr_randgen* randgen, int seed){
	unsigned int s = ((unsigned int) (seed << 1)) + 1;
	randgen->mt[0] = s & 0xffffffffUL;
	for(randgen->mti = 1; randgen->mti < ccanr_Mersenne_N; randgen->mti++) {
		randgen->mt[randgen->mti] = (1812433253UL * (randgen->mt[randgen->mti - 1] ^ (randgen->mt[randgen->mti - 1] >> 30)) + randgen->mti);
		randgen->mt[randgen->mti] &= 0xffffffffUL;
	}
}

int ccanr_Mersenne_next31(ccanr_randgen* randgen){
	unsigned int y;
	static unsigned int mag01[2] = {0x0UL, ccanr_Mersenne_MATRIX_A};
	if(randgen->mti >= ccanr_Mersenne_N) {
		int kk;
		for(kk = 0; kk < ccanr_Mersenne_N - ccanr_Mersenne_M; kk++) {
		y = (randgen->mt[kk] & ccanr_Mersenne_UPPER_MASK) | (randgen->mt[kk + 1] & ccanr_Mersenne_LOWER_MASK);
		randgen->mt[kk] = randgen->mt[kk + ccanr_Mersenne_M] ^ (y >> 1) ^ mag01[y & 0x1UL];
		}
		for(; kk < ccanr_Mersenne_N - 1; kk++) {
		y = (randgen->mt[kk] & ccanr_Mersenne_UPPER_MASK) | (randgen->mt[kk + 1] & ccanr_Mersenne_LOWER_MASK);
		randgen->mt[kk] = randgen->mt[kk + (ccanr_Mersenne_M - ccanr_Mersenne_N)] ^ (y >> 1) ^ mag01[y & 0x1UL];
		}
		y = (randgen->mt[ccanr_Mersenne_N - 1] & ccanr_Mersenne_UPPER_MASK) | (randgen->mt[0] & ccanr_Mersenne_LOWER_MASK);
		randgen->mt[ccanr_Mersenne_N - 1] = randgen->mt[ccanr_Mersenne_M - 1] ^ (y >> 1) ^ mag01[y & 0x1UL];
		randgen->mti = 0;
	}
	y = randgen->mt[randgen->mti++];
	y ^= (y >> 11);
	y ^= (y << 7) & 0x9d2c5680UL;
	y ^= (y << 15) & 0xefc60000UL;
	y ^= (y >> 18);
	return  (int) (y>>1);
}

int ccanr_Mersenne_next(ccanr_randgen* randgen, int bound){
	unsigned int value;
	do {
		value = ccanr_Mersenne_next31(randgen);
	} while(value + (unsigned int) bound >= 0x80000000UL);
	return (int) (value % bound);
}



void ccanr_lit_init(ccanr_lit *tmp_lit,int the_lit, int the_clause){
	tmp_lit->var_idx = abs(the_lit);
	tmp_lit->clause_idx = the_clause;
	tmp_lit->sense = (the_lit>0 ? 1: 0);
}
bool ccanr_lit_is_equal(ccanr_lit *lit1, ccanr_lit *lit2){
	return lit1->sense == lit2->sense && lit1->clause_idx == lit2->clause_idx && lit1->var_idx == lit2->var_idx;
}

ccanr_lit ccanr_minus_lit(ccanr_lit *lit){
	ccanr_lit res;
	res.sense = 1-lit->sense;
	res.clause_idx = lit->clause_idx;
	res.var_idx = lit->var_idx;
	return res;
}

int ccanr_lit_to_dimacs(ccanr_lit *lit){
	int res = lit->var_idx;
	if(lit->sense == 0) res = -res;
	return res;
}


static void read_until_new_line (FILE * input) {
  	int ch; 
	while ((ch = getc (input)) != '\n')
    if (ch == EOF) { 
		printf ("parse error: unexpected EOF"); 
		exit (1); 
	} 
}

void ccanr_alloc(ccanr_solver *s){
	s->_additional_lens = 2;
	if(s->_num_clauses==0 || s->_num_vars==0) {printf("Zero CNF\n");exit(0);}
	int var_nums = s->_num_vars + s->_additional_lens;
	int cls_nums = s->_num_clauses + s->_additional_lens;
	s->_vars 			= (ccanr_var*)malloc(sizeof(ccanr_var)*var_nums);
	s->_clauses 		= (ccanr_cls*)malloc(sizeof(ccanr_cls)*cls_nums);
	s->_solution 		= (char*)malloc(sizeof(int)*var_nums);
	s->_best_solution 	= (char*)malloc(sizeof(int)*var_nums);
	s->_idx_in_unsat_clauses 	= (int*)malloc(sizeof(int)*cls_nums);
	s->_idx_in_unsat_vars		= (int*)malloc(sizeof(int)*var_nums);
	s->_unsat_clauses 	= (int*)malloc(sizeof(int)*cls_nums);
	s->_unsat_vars		= (int*)malloc(sizeof(int)*var_nums);
	s->_ccd_vars		= (int*)malloc(sizeof(int)*var_nums);
}

void ccanr_solver_release(ccanr_solver *s){
	for(int var_idx=1;var_idx<=s->_num_vars;++var_idx){
		free(s->_vars[var_idx].literals);
		free(s->_vars[var_idx].neighbor_var);
	}
	for(int cls_idx=0;cls_idx<s->_num_clauses;++cls_idx){
		free(s->_clauses[cls_idx].literals);
	}
	free(s->_vars);
	free(s->_clauses);
	free(s->_solution);
	free(s->_best_solution);
	free(s->_idx_in_unsat_clauses);
	free(s->_idx_in_unsat_vars);
	free(s->_unsat_clauses);
	free(s->_unsat_vars);
	free(s->_ccd_vars);
}

bool ccanr_build(ccanr_solver *s, char *filename){
	int tmp;
	FILE *fin = fopen(filename,"r");
	if(!fin) return false;
	while((tmp = getc(fin)) == 'c') read_until_new_line(fin);
	ungetc(tmp, fin);
	do{
		tmp = fscanf(fin, " p cnf %i %i \n", &s->_num_vars, &s->_num_clauses);
		if(tmp > 0 && tmp != EOF) break;
		tmp = fscanf(fin, "%*s\n");
	}while(tmp!=2 && tmp !=EOF);
	ccanr_alloc(s);
	int *cls_buffer = (int*)malloc(sizeof(int) * (s->_num_vars+s->_additional_lens) );
	int size = 0;
	for(int ct=0;ct<s->_num_clauses;){
		int ch = getc(fin);
		if (ch == ' ' || ch == '\n') continue;
    	if (ch == 'c') { read_until_new_line (fin); continue; }
		ungetc(ch,fin);
		int lit = 0;
		tmp = fscanf(fin," %i ", &lit);
		if(!lit){
			bool should_add = true;
			for(int i=1;i<size;++i){
				for(int j=0;j<i;++j){
					if(cls_buffer[i] == cls_buffer[j]){
						cls_buffer[i] = cls_buffer[--size];
						i--;
						break;
					}else if(cls_buffer[i] == -cls_buffer[j]){
						s->_num_clauses--;
						should_add = false;
						break;
					}
				}if(!should_add) break;
			}
			if(should_add){
				s->_clauses[ct].literals = (ccanr_lit*)malloc(sizeof(ccanr_lit)*size);
				for(int i=0;i<size;++i){
					ccanr_lit_init(&(s->_clauses[ct].literals[i]),cls_buffer[i],ct);
				}
				s->_clauses[ct].literals_sz = size;
				++ct;
			}
			size = 0;
		}else {
			cls_buffer[size++] = lit;
		}
	}
	
	fclose(fin);
	ccanr_build_after_read(s);
	free(cls_buffer);
	return true;
}

void ccanr_build_after_read(ccanr_solver *s){
	// deal with var
	for(int var_idx=1;var_idx<=s->_num_vars;++var_idx) s->_vars[var_idx].literals_sz = 0;
	for(int cls_idx=0;cls_idx<s->_num_clauses;++cls_idx){
		int size = s->_clauses[cls_idx].literals_sz;
		for(int l_idx=0;l_idx<size;++l_idx){
			int var_idx = s->_clauses[cls_idx].literals[l_idx].var_idx;
			s->_vars[var_idx].literals_sz ++;
		}
	}
	for(int var_idx=1;var_idx<=s->_num_vars;++var_idx){
		s->_vars[var_idx].literals = (ccanr_lit*)malloc(sizeof(ccanr_lit)*(s->_vars[var_idx].literals_sz));
		s->_vars[var_idx].literals_sz = 0;
	}
	for(int cls_idx=0;cls_idx<s->_num_clauses;++cls_idx){
		int size = s->_clauses[cls_idx].literals_sz;
		for(int l_idx=0;l_idx<size;++l_idx){
			ccanr_lit tmp_lit = s->_clauses[cls_idx].literals[l_idx];
			int var_idx = tmp_lit.var_idx;
			s->_vars[var_idx].literals[s->_vars[var_idx].literals_sz++] = tmp_lit;
		}
	}

	// build neighborhood
	char *neighbor_flag = (char*)malloc(sizeof(char) * (s->_num_vars+s->_additional_lens));
	int  *neighbor_buffer = (int*)malloc(sizeof(int) * (s->_num_vars+s->_additional_lens));
	int neighbor_sz;
	memset(neighbor_flag,0,s->_num_vars+s->_additional_lens);
	for(int var=1;var<=s->_num_vars;++var){
		ccanr_var *this_var = &(s->_vars[var]);
		neighbor_sz = 0;
		int this_var_lits_sz = this_var->literals_sz;
		for(int l_idx=0;l_idx<this_var_lits_sz;++l_idx){
			int cls_idx = this_var->literals[l_idx].clause_idx;
			int cls_sz = s->_clauses[cls_idx].literals_sz;
			for(int cls_v_idx=0;cls_v_idx<cls_sz;cls_v_idx++){ 
				int cls_var = s->_clauses[cls_idx].literals[cls_v_idx].var_idx;
				if(cls_var != var){
					if(neighbor_flag[cls_var]==0){
						neighbor_buffer[neighbor_sz++] = cls_var;
						neighbor_flag[cls_var] = 1;
					}
				}	
			}
		}
		
		this_var->neighbor_var = (int*)malloc(sizeof(int)*neighbor_sz);
		this_var->neighbor_var_sz = neighbor_sz;
		for(int neighbor_v_idx=0;neighbor_v_idx<neighbor_sz;neighbor_v_idx++){
			int neighbor_v = neighbor_buffer[neighbor_v_idx];
			this_var->neighbor_var[neighbor_v_idx] = neighbor_v;
			neighbor_flag[neighbor_v] = 0;
		}
	}

	free(neighbor_flag);free(neighbor_buffer);

	ccanr_set_paprameter(s);
}


void ccanr_sat_a_clause(ccanr_solver *s, int the_clause)
{
	int index, last_item;
	last_item = s->_unsat_clauses[--s->_unsat_cls_num];
	index = s->_idx_in_unsat_clauses[the_clause];
	s->_unsat_clauses[index] = last_item;
	s->_idx_in_unsat_clauses[last_item] = index;
	int cls_sz = s->_clauses[the_clause].literals_sz;
	for(int l_idx=0;l_idx<cls_sz;++l_idx){
		ccanr_lit *l = &(s->_clauses[the_clause].literals[l_idx]);
		if(--s->_vars[l->var_idx].unsat_appear == 0){
			last_item = s->_unsat_vars[--s->_unsat_var_num];	
			index = s->_idx_in_unsat_vars[l->var_idx];
			s->_unsat_vars[index] = last_item;
			s->_idx_in_unsat_vars[last_item] = index;
		}
	}
}
void ccanr_unsat_a_clause(ccanr_solver *s, int the_clause)
{
	s->_idx_in_unsat_clauses[the_clause] = s->_unsat_cls_num;
	s->_unsat_clauses[s->_unsat_cls_num++] = the_clause;	
	int cls_sz = s->_clauses[the_clause].literals_sz;
	for(int l_idx=0;l_idx<cls_sz;++l_idx){
		ccanr_lit *l = &(s->_clauses[the_clause].literals[l_idx]);
		if (++s->_vars[l->var_idx].unsat_appear == 1)
		{
			s->_idx_in_unsat_vars[l->var_idx] = s->_unsat_var_num;
			s->_unsat_vars[s->_unsat_var_num++] = l->var_idx;
		}
	}
}

void ccanr_set_paprameter(ccanr_solver  *s){
	s->_max_mems 	= 100*1000*1000;
	s->_swt_threshold = 50;
	s->_swt_p 		= 0.3;
	s->_swt_q 		= 0.7;
	s->_aspiration_active = true;
	s->_prob_p		= 0.001;
	ccanr_Mersenne_init_with_seed(&(s->randgen),1);
	
	//initialize some basical information
	s->_mems		= 0;
	s->_steps		= 0;
	
	// clear previous data
	s->_unsat_cls_num 	= 0;
	s->_ccd_var_num   	= 0;
	s->_unsat_var_num	= 0;
}


void ccanr_set_init_soln(ccanr_solver  *s, char *init_solution){
	if(init_solution == NULL){
		for(int v=1; v <= s->_num_vars; v++)
			s->_best_solution[v] = s->_solution[v] = ccanr_Mersenne_next(&(s->randgen),2);
	}else{
		for(int v=1; v <= s->_num_vars; v++){
			s->_best_solution[v] = s->_solution[v] = init_solution[v];
		}
	}
}

void ccanr_initilize(ccanr_solver  *s){
	s->_best_found_cost = s->_num_clauses;	

	for(int v=1; v <= s->_num_vars; v++)
		s->_vars[v].unsat_appear = 0;
	for(int c=0; c<s->_num_clauses; c++){
		s->_clauses[c].sat_count = 0;
		s->_clauses[c].sat_var 	 = -1;
		s->_clauses[c].weight 	 = 1;
		ccanr_lit * this_cls = s->_clauses[c].literals;
		int this_cls_sz = s->_clauses[c].literals_sz;
		for(int l_idx=0;l_idx<this_cls_sz;++l_idx){
			ccanr_lit l = this_cls[l_idx];
			if(s->_solution[l.var_idx] == l.sense){
				s->_clauses[c].sat_count++;
				s->_clauses[c].sat_var = l.var_idx;
			}
		}	
		if (s->_clauses[c].sat_count == 0) ccanr_unsat_a_clause(s,c);
		
	}

	s->_avg_clause_weight = 1;
	s->_delta_total_clause_weight = 0;	
	
	// initialize variable scores and related data structures
	for(int var_idx=1;var_idx<=s->_num_vars;++var_idx){
		ccanr_var *this_var = &(s->_vars[var_idx]);
		this_var->score = 0;
		this_var->is_in_ccd_vars = 0;
		int l_sz = this_var->literals_sz;
		for(int l_idx=0;l_idx<l_sz;++l_idx){
			ccanr_lit *this_lit = &(this_var->literals[l_idx]);
			int cls_idx = this_lit->clause_idx;
			int sat_ct  = s->_clauses[cls_idx].sat_count;
			if(sat_ct == 0) 
				this_var->score += s->_clauses[cls_idx].weight;
			else if(sat_ct == 1 && this_lit->sense == s->_solution[var_idx]) 
				this_var->score -= s->_clauses[cls_idx].weight;
		}

		this_var->last_flip_step = 0;
		this_var->cc_value = 1;
		if(this_var->score > 0){
			this_var->is_in_ccd_vars = 1;
			s->_ccd_vars[s->_ccd_var_num++] = var_idx;
		}
	}
	// check_ccanr(s);
}

void ccanr_smooth_cls_weight(ccanr_solver *s){
	for(int v=1; v <= s->_num_vars; v++) 
		s->_vars[v].score=0;
	int	scale_avg = s->_avg_clause_weight * s->_swt_q;
	s->_avg_clause_weight = 0;
	s->_delta_total_clause_weight=0;

	for (int cls_idx=0; cls_idx < s->_num_clauses; ++cls_idx){
		ccanr_cls *this_cls = &(s->_clauses[cls_idx]);
		this_cls->weight = this_cls->weight * s->_swt_p + scale_avg;
		if (this_cls->weight<1) this_cls->weight=1;
		s->_delta_total_clause_weight += this_cls->weight;
		if (s->_delta_total_clause_weight >= s->_num_clauses){
			s->_avg_clause_weight += 1;
			s->_delta_total_clause_weight -= s->_num_clauses;
		}
		if (this_cls->sat_count==0)
			for(int l_idx=0;l_idx<this_cls->literals_sz;++l_idx){
				ccanr_lit *this_lit = &(this_cls->literals[l_idx]);
				s->_vars[this_lit->var_idx].score += this_cls->weight;
			}
		else if (this_cls->sat_count==1) 
			s->_vars[this_cls->sat_var].score -= this_cls->weight;
		
	}
	//reset ccd_vars
	s->_ccd_var_num = 0;
	for(int v=1; v <= s->_num_vars; v++){
		ccanr_var *this_var = &(s->_vars[v]);
		if (this_var->score>0 && this_var->cc_value==1){
			s->_ccd_vars[s->_ccd_var_num++] = v;
			this_var->is_in_ccd_vars = 1;
		}else this_var->is_in_ccd_vars = 0;
	}
}

void ccanr_updata_cls_weight(ccanr_solver *s){
	for(int idx=0;idx<s->_unsat_cls_num;++idx)
		s->_clauses[s->_unsat_clauses[idx]].weight++;
	s->_mems += s->_unsat_var_num;
	for(int idx=0;idx<s->_unsat_var_num;++idx){
		int var = s->_unsat_vars[idx];
		s->_vars[var].score += s->_vars[var].unsat_appear;
		if(s->_vars[var].score>0 && s->_vars[var].cc_value==1 && !s->_vars[var].is_in_ccd_vars){
			s->_ccd_vars[s->_ccd_var_num++] = var;
			s->_vars[var].is_in_ccd_vars = 1;
		}
	}
	s->_delta_total_clause_weight += s->_unsat_cls_num;
	if(s->_delta_total_clause_weight >= s->_num_clauses){
		s->_avg_clause_weight += 1;
		s->_delta_total_clause_weight -= s->_num_clauses;
		if(s->_avg_clause_weight > s->_swt_threshold)
			ccanr_smooth_cls_weight(s);
	}

}


int ccanr_pick_var(ccanr_solver *s){
	int best_var = 0;
	int best_score;

	int ccd_var_num = s->_ccd_var_num;
	if(ccd_var_num>0){
		s->_mems += ccd_var_num;
		best_var = s->_ccd_vars[0];
		best_score = s->_vars[best_var].score;
		for(int ccd_idx=1; ccd_idx<ccd_var_num; ++ccd_idx){
			int var = s->_ccd_vars[ccd_idx];
			int var_score = s->_vars[var].score;
			if( (var_score > best_score) ||
				(var_score == best_score && s->_vars[best_var].last_flip_step > s->_vars[var].last_flip_step)
			){
				best_var = var;
				best_score = var_score;
			}
		}
		return best_var;
	}

	if(s->_aspiration_active){
		s->_aspiration_score = s->_avg_clause_weight;
		int idx;
		for(idx=0;idx<s->_unsat_var_num;++idx){
			int var = s->_unsat_vars[idx];
			if(s->_vars[var].score > s->_aspiration_score)
			{
				best_var = var;
				best_score = s->_vars[best_var].score;
				break;
			}
		}
		for(++idx;idx<s->_unsat_var_num;++idx){
			int var = s->_unsat_vars[idx];
			int var_score = s->_vars[var].score;
			if( (var_score > best_score) ||
				(var_score == best_score && s->_vars[best_var].last_flip_step > s->_vars[var].last_flip_step)
			){
				best_var = var;
				best_score = var_score;
			}
		}
		if(best_var > 0) return best_var;
	}

	ccanr_updata_cls_weight(s);

	int cls = s->_unsat_clauses[ccanr_Mersenne_next(&(s->randgen),s->_unsat_cls_num)];
	ccanr_lit *cls_lits = s->_clauses[cls].literals;
	int cls_sz = s->_clauses[cls].literals_sz;
	best_var = cls_lits[0].var_idx;
	best_score = s->_vars[best_var].score;
	for(int v_idx=1;v_idx<cls_sz;++v_idx){
		int var = cls_lits[v_idx].var_idx;
		int var_score = s->_vars[var].score;
		if( (var_score > best_score) ||
			(var_score == best_score && s->_vars[best_var].last_flip_step > s->_vars[var].last_flip_step)
		){
			best_var = var;
			best_score = var_score;
		}
	}
	return best_var;

}

void ccanr_flip(ccanr_solver *s, int fvar){
	s->_solution[fvar] = 1-s->_solution[fvar];
	int org_fvar_score = s->_vars[fvar].score;
	int l_sz = s->_vars[fvar].literals_sz;
	s->_mems += l_sz;
	for(int l_idx=0;l_idx<l_sz;++l_idx){
		ccanr_lit *this_lit = &(s->_vars[fvar].literals[l_idx]);
		int cls_idx = this_lit->clause_idx;
		int cls_sz = s->_clauses[cls_idx].literals_sz;
		ccanr_cls *this_cls = &(s->_clauses[cls_idx]);
		if(s->_solution[fvar] == this_lit->sense){
			this_cls->sat_count++;
			if(this_cls->sat_count==1){
				ccanr_sat_a_clause(s,cls_idx);
				this_cls->sat_var = fvar;
				for(int inner_l_idx=0;inner_l_idx<cls_sz;++inner_l_idx){
					ccanr_lit *cls_lit = &(s->_clauses[cls_idx].literals[inner_l_idx]);
					s->_vars[cls_lit->var_idx].score -= this_cls->weight;
				}
			}else if(this_cls->sat_count==2){
				s->_vars[this_cls->sat_var].score += this_cls->weight;
			}
		}else{
			this_cls->sat_count--;
			if(this_cls->sat_count==0){
				ccanr_unsat_a_clause(s,cls_idx);
				for(int inner_l_idx=0;inner_l_idx<cls_sz;++inner_l_idx){
					ccanr_lit *cls_lit = &(s->_clauses[cls_idx].literals[inner_l_idx]);
					s->_vars[cls_lit->var_idx].score += this_cls->weight;
				}
			}else if(this_cls->sat_count==1){
				for(int inner_l_idx=0;inner_l_idx<cls_sz;++inner_l_idx){
					ccanr_lit *cls_lit = &(s->_clauses[cls_idx].literals[inner_l_idx]);
					if(s->_solution[cls_lit->var_idx] == cls_lit->sense){
						s->_vars[cls_lit->var_idx].score -= this_cls->weight;
						this_cls->sat_var = cls_lit->var_idx;
						break;
					}
				}
			}
		}
	}
	s->_vars[fvar].score = -org_fvar_score;
	s->_vars[fvar].last_flip_step = s->_steps;

	ccanr_var *this_var = &(s->_vars[fvar]);
	this_var->cc_value = 0;
	for(int idx=s->_ccd_var_num-1;idx>=0;--idx){
		int var = s->_ccd_vars[idx];
		if(s->_vars[var].score <= 0){
			int last_item = s->_ccd_vars[--s->_ccd_var_num];
			s->_ccd_vars[idx] = last_item;
			s->_vars[var].is_in_ccd_vars = 0;
			s->_mems++;
		}
	}
	int n_sz = s->_vars[fvar].neighbor_var_sz;
	for(int n_idx=0;n_idx<n_sz;n_idx++){
		int n_var = s->_vars[fvar].neighbor_var[n_idx];
		s->_vars[n_var].cc_value = 1;
		if(s->_vars[n_var].score>0 && !s->_vars[n_var].is_in_ccd_vars){
			s->_ccd_vars[s->_ccd_var_num++] = n_var;
			s->_vars[n_var].is_in_ccd_vars = 1;
			s->_mems++;
		}
	}

}



bool ccanr_doLS(ccanr_solver  *s){
	ccanr_initilize(s);
	if(s->_unsat_cls_num == 0 ) return true;
	while(true){
		if(s->_mems > s->_max_mems) break;
		int flip_var = ccanr_pick_var(s);
		ccanr_flip(s,flip_var);
		if(s->_unsat_cls_num < s->_best_found_cost){
			s->_best_found_cost = s->_unsat_cls_num;
			for(int v_idx=1;v_idx<=s->_num_vars;++v_idx) 
				s->_best_solution[v_idx] = s->_solution[v_idx];
		}
		if(s->_unsat_cls_num == 0 ) return true;
		s->_steps++;
	}
	return false;
}

