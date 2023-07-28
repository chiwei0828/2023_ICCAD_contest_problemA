#include "ccnradapter.h"

#include <string.h>

#include "allocate.h"
#include "ccnr.h"
#include "decide.h"
#include "dense.h"
#include "inline.h"
#include "inlineheap.h"
#include "internal.h"
#include "phases.h"
#include "print.h"
#include "rephase.h"
#include "report.h"
#include "terminate.h"

// for UP
#define PROPAGATION_TYPE "none"
#include "trail.h"
#include "fastassign.h"
#include "proplit.h"

static void set_var_info(kissat * solver, CCAnr *lssolver, lit *lit, unsigned kis_lit, unsigned cls_num)
{
  lit->clause_num = cls_num;
  lit->var_num = IDX(kis_lit) + 1;
  lit->sense = NEGATED(kis_lit) ? 0 : 1;
  lssolver->var_lit_count[lit->var_num] ++;
  (void) solver;
}

// static void set_unit_cls_info(kissat * solver, CCAnr *lssolver , unsigned unit_lit)
// {
//   int cls_ct = lssolver->cls_ct;
//   lssolver->min_clause_len = 1;
//   lssolver->max_clause_len = MAX(lssolver->max_clause_len, 1);
//   lssolver->clause_lit_count[cls_ct] = 1;
//   lssolver->clause_lit[cls_ct] = (lit *)malloc(sizeof(lit) * (2));
//   set_var_info(solver, lssolver, &lssolver->clause_lit[cls_ct][0], unit_lit, cls_ct);
//   lssolver->clause_lit[cls_ct][1].var_num = 0;
//   lssolver->clause_lit[cls_ct][1].clause_num = -1;
//   lssolver->unitclause_queue[lssolver->unitclause_queue_end_pointer++] =
//     lssolver->clause_lit[cls_ct][0];
//   lssolver->clause_delete[cls_ct] = 1;
//   lssolver->formula_len += 1;
//   lssolver->cls_ct ++;
// }

static void set_binary_cls_info(kissat * solver, CCAnr *lssolver , unsigned lit0, unsigned lit1)
{
  int cls_ct = lssolver->cls_ct;
  lssolver->min_clause_len = MIN(lssolver->min_clause_len, 2);
  lssolver->max_clause_len = MAX(lssolver->max_clause_len, 2);
  lssolver->clause_lit_count[cls_ct] = 2;
  lssolver->clause_lit[cls_ct] = (lit *)malloc(sizeof(lit) * 3);
  set_var_info(solver, lssolver, &lssolver->clause_lit[cls_ct][0], lit0, cls_ct);
  set_var_info(solver, lssolver, &lssolver->clause_lit[cls_ct][1], lit1, cls_ct);
  lssolver->clause_lit[cls_ct][2].var_num = 0;
  lssolver->clause_lit[cls_ct][2].clause_num = -1;
  lssolver->formula_len += 2;
  lssolver->cls_ct ++;
}

static void set_large_cls_info(kissat * solver, CCAnr *lssolver , clause * c)
{
  int cls_ct = lssolver->cls_ct;

  lssolver->clause_lit[cls_ct] = (lit *)malloc(sizeof(lit) * (c->size+1));

  int size = 0;
  for (all_literals_in_clause(l, c)) {
    if (lssolver->tmp_up_build_soln[IDX(l)] == -1)
      continue;
    set_var_info(solver, lssolver, &lssolver->clause_lit[cls_ct][size], l, cls_ct);
    size++;
  }

  assert(size > 1);
  if (size <= 1) {
    printf("c ERROR!\n");
  }

  lssolver->clause_lit[cls_ct][size].var_num = 0;
  lssolver->clause_lit[cls_ct][size].clause_num = -1;

  lssolver->clause_lit_count[cls_ct] = size;
  lssolver->min_clause_len = MIN(lssolver->min_clause_len, lssolver->clause_lit_count[cls_ct]);
  lssolver->max_clause_len = MAX(lssolver->max_clause_len, lssolver->clause_lit_count[cls_ct]);
  lssolver->formula_len += size;
  lssolver->cls_ct ++;
}

static
void build_soln_with_phase(kissat * solver, CCAnr * lssolver)
{
  char * tmp_up_build_soln = lssolver->tmp_up_build_soln;
  flags * flags = solver->flags;
  for (all_variables(idx)) {
    if (!flags[idx].active)
    {
      tmp_up_build_soln[idx] = -1;
      lssolver->fix[idx+1] = 1;
      continue;
    }
    value value = 0;
    // value = VALUE(LIT(idx));
    if (solver->stable)
      value = solver->phases.target[idx];
    if (!value)
      value = solver->phases.saved[idx];
    if (!value)
      value = INITIAL_PHASE;
    tmp_up_build_soln[idx] = value > 0 ? 1 : 0;
  }
}

void load_ls_data(kissat *solver, CCAnr *lssolver)
{

  lssolver->mems_left = 5e8;
  lssolver->ratio = (lssolver->num_clauses + 0.0) / lssolver->num_vars;

  for (int c = 0; c < lssolver->num_clauses; c++)
    lssolver->clause_lit_count[c] = lssolver->clause_delete[c] = 0;
  for (int v = 1; v <= lssolver->num_vars; ++v)
    lssolver->var_lit_count[v] = lssolver->fix[v] = 0;
  lssolver->max_clause_len = 0;
  lssolver->min_clause_len = lssolver->num_vars;

  lssolver->cls_ct = 0;

  // unsigned un = 0;
  // unit clause
  // for (all_variables(idx)) {
  //   if (VALUE (LIT(idx))) {
  //     un ++ ;
  //     set_unit_cls_info(solver,lssolver,LIT(idx));
  //   }
  // }
  // printf("unit size: %u\n", un);
  // printf("trail size: %u\n", SIZE_ARRAY (solver->trail));
  // // binary clause
  // printf("bin size1: %u\n", SIZE_STACK (*solver->binary));

  // unsigned cc = 0;
  litpair * lp = BEGIN_STACK(*solver->binary);
  unsigned lp_size = SIZE_STACK (*solver->binary);
  for (unsigned i = 0; i < lp_size; i++) {
    const litpair *const p = lp + i;
    unsigned lit0 = p->lits[0];
    unsigned lit1 = p->lits[1];
    if (lssolver->tmp_up_build_soln[IDX(lit0)] == -1 ||
        lssolver->tmp_up_build_soln[IDX(lit1)] == -1)
      continue;
    set_binary_cls_info(solver, lssolver, lit0, lit1);
    // cc ++;
  }
  // for (all_stack(litpair, lp , *solver->binary)) {
  //   // printf("2");
  //   set_binary_cls_info(solver, lssolver, lp.lits[0], lp.lits[1]);
  //   cc ++ ;
  // }
  // printf("cc : %u\n", cc);
  // printf("bin size2: %u\n", SIZE_STACK (*solver->redundant));

  // litwatch * lw = BEGIN_STACK(*solver->redundant);
  // unsigned lw_size = SIZE_STACK (*solver->redundant);
  // for (int i =0;i<lw_size;i++) {
  //   const litwatch * const p = lw + i;
  //   set_binary_cls_info(solver, lssolver, p->lit, p->watch.binary.lit);
  //   // cc ++;
  // }
  // for (all_stack(litwatch, lw, *solver->redundant)) {
  //   // printf("3");
  //   assert(lw.watch.type.binary);
  //   printf("lw: %u %u \n", lw.lit, lw.watch.binary.lit);
  //   set_binary_cls_info(solver, lssolver, lw.lit, lw.watch.binary.lit);
  // }

  // large clause
  clause *last_irredundant = kissat_last_irredundant_clause (solver);
  // int tt = 0;
  // printf("all size: %u", SIZE_STACK (*solver->clause));
  for (all_clauses(c))
  {
    if (last_irredundant && c > last_irredundant)
      break;
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    // printf("4");
    // tt ++ ;
    set_large_cls_info(solver, lssolver, c);
  }

  // printf("tt : %u \n", tt);
  // printf("sum:%u \n", tt+cc+SIZE_STACK (*solver->redundant));
  update_after_build(lssolver);
}

static inline void
shrink_undef_vars(kissat *solver, unsigned def_var)
{
  // printf("def var: %u\n", def_var);
  unsigned *undef_vars = solver->undef_vars;
  unsigned *undef_vars_idx = solver->undef_vars_idx;
  assert(undef_vars_idx[def_var] < solver->undef_vars_num);
  unsigned ori_end_var = undef_vars[--solver->undef_vars_num];
  unsigned new_ori_end_var_idx = undef_vars_idx[def_var];
  undef_vars[new_ori_end_var_idx] = ori_end_var;
  undef_vars_idx[ori_end_var] = new_ori_end_var_idx;
}

static void
propagate_literal_without_conflict(kissat *solver, unsigned lit)
{
  assert(solver->watching);
  // unsigned lit = PEEK_ARRAY(solver->trail, propagated);
  assert(solver->values[lit] > 0);
  
  watches *const all_watches = solver->watches;
  ward *const arena = BEGIN_STACK (solver->arena);
  value *const values = solver->values;
  const unsigned not_lit = NOT (lit);
  assert (not_lit < LITS);
  watches *watches = all_watches + not_lit;
  watch *const begin_watches = BEGIN_WATCHES (*watches);
  const watch *const end_watches = END_WATCHES (*watches);
  watch *q = begin_watches;
  const watch *p = q;
  assert (EMPTY_STACK (solver->delayed));
  unsigneds *const delayed = &solver->delayed;

  while (p != end_watches) {
    const watch head = *q++ = *p++;
    const unsigned blocking = head.blocking.lit;
    assert (VALID_INTERNAL_LITERAL (blocking));
    const value blocking_value = values[blocking];

    if (head.type.binary) {
      if (blocking_value > 0)
        continue;
      else if (blocking_value == 0) {
        PUSH_ARRAY(solver->trail, blocking);
        unsigned not_blocking = NOT (blocking);
        values[blocking] = 1;
        assert(values[not_blocking] == 0);
        values[not_blocking] = -1;
        shrink_undef_vars(solver, IDX(blocking));
      }
      // blocking_value < 0 conflict : ignore
    } else {
      const watch tail = *q++ = *p++;
      if (blocking_value > 0)
        continue;
      const reference ref = tail.raw;
	    assert (ref < SIZE_STACK (solver->arena));
	    clause *const c = (clause *) (arena + ref);
      if (c->garbage) {
        q -= 2;
        continue;
      }
      unsigned *const lits = BEGIN_LITS (c);
      const unsigned other = lits[0] ^ lits[1] ^ not_lit;
      assert (lits[0] != lits[1]);
      assert (VALID_INTERNAL_LITERAL (other));
      assert (not_lit != other);
      assert (lit != other);
      const value other_value = values[other];
      if (other_value > 0) {
        q[-2].blocking.lit = other;
      } else {
        const unsigned *const end_lits = lits + c->size;
	      unsigned *const searched = lits + c->searched;
	      assert (c->lits + 2 <= searched);
	      assert (searched < end_lits);
	      unsigned *r, replacement = INVALID_LIT;
	      value replacement_value = -1;

        for (r = searched; r != end_lits; r++) {
          replacement = *r;
          assert (VALID_INTERNAL_LITERAL (replacement));
          replacement_value = values[replacement];
          if (replacement_value >= 0)
            break;
        }
        if (replacement_value < 0) {
          for (r = lits + 2; r != searched; r++) {
              replacement = *r;
              assert (VALID_INTERNAL_LITERAL (replacement));
              replacement_value = values[replacement];
              if (replacement_value >= 0)
                break;
          }
        }
        if (replacement_value >= 0)
		      c->searched = r - lits;

	      if (replacement_value > 0) {
          assert (replacement != INVALID_LIT);
          q[-2].blocking.lit = replacement;
        }
	      else if (replacement_value == 0) {
          assert (replacement != INVALID_LIT);
          LOGREF (ref, "unwatching %s in", LOGLIT (not_lit));
          q -= 2;
          lits[0] = other;
          lits[1] = replacement;
          assert (lits[0] != lits[1]);
          *r = not_lit;
          kissat_delay_watching_large (solver, delayed,
                    replacement, other, ref);
        }
	      else if (other_value) {
          assert (replacement_value < 0);
          assert (blocking_value < 0);
          assert (other_value < 0);
          // conflict : ignore
          // break;
        } else {
          assert (!other_value);
          assert (replacement_value < 0);
          unsigned not_other = NOT (other);
          values[other] = 1;
          assert (values[not_other] == 0);
          values[not_other] = -1;
          shrink_undef_vars(solver, IDX(other));
        }
      }
    }
    if (solver->undef_vars_num == 0)
      break;
  }
  // useless
  while (p != end_watches)
    *q++ = *p++;
  SET_END_OF_WATCHES (*watches, q);
  kissat_watch_large_delayed (solver, all_watches, delayed);

}

static inline value
get_decision_value(kissat *solver, unsigned idx)
{
  value value = 0;
  if (solver->stable)
    value = solver->phases.target[idx];
  if (!value)
    value = solver->phases.saved[idx];
  if (!value)
    value = INITIAL_PHASE;
  assert(value);
  return value;
}

static void
propagate_without_conflict(kissat *solver, CCAnr *lssolver)
{
  assert(EMPTY_ARRAY(solver->trail));
  value * saved = solver->values;
  solver->values = kissat_calloc (solver, LITS, 1);
  value * values = solver->values;
  unsigned * undef_vars = kissat_calloc(solver, VARS, 4);
  unsigned * undef_vars_idx = kissat_calloc(solver, VARS, 4);
  solver->undef_vars = undef_vars;
  solver->undef_vars_idx = undef_vars_idx;
  solver->undef_vars_num = 0;
  unsigned undef_vars_num = 0;
  for (unsigned i = 0; i < LITS; i++) {
    values[i] = saved[i];
    if (saved[i] > 0) {
      PUSH_ARRAY(solver->trail, i);
      // lssolver->tmp_up_build_soln[IDX(i)] = NEGATED(i) ? 0 : 1;
    }
    else if (saved[i] == 0 && !NEGATED(i)) {
      undef_vars[undef_vars_num] = IDX(i);
      undef_vars_idx[IDX(i)] = undef_vars_num;
      undef_vars_num++;
      // lssolver->tmp_up_build_soln[IDX(i)] = -1;
    }
  }
  solver->undef_vars_num = undef_vars_num;
  // printf("undef num : %u\n", solver->undef_vars_num);
  kissat_reset_propagate(solver);
  unsigned *propagate = solver->propagate;
  // undef_vars_num = undef_vars_num >> 1;
  while (solver->undef_vars_num > 0) {
    if (propagate == END_ARRAY(solver->trail)) {
      unsigned add_var = undef_vars[kissat_pick_random (&solver->random, 0, solver->undef_vars_num - 1)];
      unsigned add_lit = LIT (add_var);
      assert(values[add_lit] == 0);
      value v = get_decision_value(solver, IDX(add_lit));
      unsigned not_lit = NOT (add_lit);
      assert(values[not_lit] == 0);
      if (v > 0) {
        values[add_lit] = 1;
        values[not_lit] = -1;
        PUSH_ARRAY(solver->trail, add_lit);
      } else {
        assert(v < 0);
        values[add_lit] = -1;
        values[not_lit] = 1;
        PUSH_ARRAY(solver->trail, not_lit);
      }
      shrink_undef_vars(solver, add_var);
      if (solver->undef_vars_num == 0)
        break;
    }
    propagate_literal_without_conflict(solver, *propagate++);
  }

  for (all_variables(idx))
    lssolver->tmp_up_build_soln[idx] = values[LIT(idx)] > 0 ? 1 : 0;

  kissat_free (solver, solver->values, LITS);
  solver->values = saved;
  kissat_free (solver, undef_vars, VARS * 4);
  kissat_free (solver, undef_vars_idx, VARS * 4);
  // kissat_flush_trail(solver);
  CLEAR_ARRAY (solver->trail);
  kissat_reset_propagate (solver);
  solver->undef_vars = NULL;
  solver->undef_vars_idx = NULL;
  solver->undef_vars_num = 0;
}

static
void save_ls_phase(kissat * solver, CCAnr * lssolver)
{
  solver->statistics.walk_steps = lssolver->limit_step;
  if (lssolver->ls_best_unsat_num >= lssolver->initial)
    return;
  assert(solver->stable);
  value *saved = solver->phases.saved;
  heap *scores = &solver->scores;
  flags *flags = solver->flags;
  for (all_variables(idx)) {
    if (!flags[idx].active)
      continue;
    saved[idx] = lssolver->ls_mediation_soln[idx] ? 1 : -1;
  }
  for (int i = 0; i < lssolver->in_conflict_sz; ++i) {
    int v = lssolver->in_conflict[i];
    if (!flags[v-1].active)
      continue;
    double old_score = kissat_get_heap_score(scores, v-1);
    double new_score = old_score + solver->scinc * lssolver->conflict_ct[v];
    kissat_update_heap (solver, scores, v-1, new_score);
  }
}

static
void init_CCAnr_limit(kissat * solver, CCAnr * lssolver)
{
  lssolver->limit_step = solver->statistics.walk_steps;
  SET_EFFORT_LIMIT (limit, walk, walk_steps, 2 * CLAUSES);
  lssolver->limit = limit;
  lssolver->initial = lssolver->unsat_stack_fill_pointer;
}

bool call_ls(kissat * solver, CCAnr * lssolver)
{
  lssolver->old_num_vars = lssolver->num_vars;
  lssolver->num_vars = VARS;
  lssolver->old_num_clauses = lssolver->num_clauses;
  lssolver->num_clauses = IRREDUNDANT_CLAUSES;
  if (lssolver->ccanr_has_constructed)
    reinit_CCAnr(lssolver);
  else
    init_CCAnr(lssolver), lssolver->ccanr_has_constructed = true;
  // ---kissat---
  if (GET_OPTION (walkup))
    propagate_without_conflict(solver, lssolver);
  else
    build_soln_with_phase(solver, lssolver);
  litpairs irredundant;
  litwatches redundant;
  INIT_STACK (irredundant);
  INIT_STACK (redundant);
  kissat_enter_dense_mode (solver, &irredundant, &redundant);
  solver->binary = &irredundant;
  solver->redundant = &redundant;
  // ------------
  load_ls_data(solver, lssolver);
  bool res = false;

  settings(lssolver, lssolver->tmp_up_build_soln);
  init_CCAnr_limit(solver, lssolver);
  res = local_search(lssolver);
  confl_trans(lssolver);
  // ---kissat---
  kissat_resume_sparse_mode(solver, false, &irredundant, &redundant);
  RELEASE_STACK (irredundant);
  RELEASE_STACK (redundant);
  // ------------
  int ls_var_nums = lssolver->num_vars;
  for (int i = 0; i < ls_var_nums; ++i)
    lssolver->ls_mediation_soln[i] = lssolver->best_soln[i + 1];
  if (lssolver->best_cost <= lssolver->ls_best_unsat_num) {
    lssolver->restarts_gap -= lssolver->restarts_basic;
    if (lssolver->restarts_gap < lssolver->restarts_basic)
      lssolver->restarts_gap = lssolver->restarts_basic;
    lssolver->ls_best_unsat_num = lssolver->best_cost;
    for (int i = 0; i < ls_var_nums; ++i)
      lssolver->ls_best_soln[i] = lssolver->ls_mediation_soln[i];
  } else {
    lssolver->restarts_gap += lssolver->restarts_basic;
  }
  lssolver->freeze_ls_restart_num = lssolver->restarts_gap;
  lssolver->max_trail = lssolver->max_trail * 0.9;
  if (res == true) {
    lssolver->solved_by_ls = true;
    printf("c Solved by Local Search\n");
  }
  save_ls_phase(solver, lssolver);
  return res;
}
