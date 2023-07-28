#include "analyze.h"
#include "backtrack.h"
#include "inline.h"
#include "propsearch.h"
#include "report.h"
#include "trail.h"

#include "bump.c"

#define MAX_SCORE 1e150

static inline void
unassign (kissat * solver, value * values, unsigned lit)
{
  LOG ("unassign %s", LOGLIT (lit));
  assert (values[lit] > 0);
  const unsigned not_lit = NOT (lit);
  values[lit] = values[not_lit] = 0;
  assert (solver->unassigned < VARS);
  solver->unassigned++;
}

static inline void
add_unassigned_variable_back_to_queue (kissat * solver,
				       links * links, unsigned lit)
{
  assert (!solver->stable);
  const unsigned idx = IDX (lit);
  if (links[idx].stamp > solver->queue.search.stamp)
    kissat_update_queue (solver, links, idx);
}

static inline void
add_unassigned_variable_back_to_heap (kissat * solver,
				      heap * scores, unsigned lit)
{
  assert (solver->stable);
  const unsigned idx = IDX (lit);
  if (!kissat_heap_contains (scores, idx))
    kissat_push_heap (solver, scores, idx);
}

static void
update_phases (kissat * solver)
{
  const char type = solver->rephased.type;
  const bool reset = (type && CONFLICTS > solver->rephased.last);

  if (!solver->probing)
    {
      if (reset)
	kissat_reset_target_assigned (solver);

      if (solver->target_assigned < solver->consistently_assigned)
	{
	  LOG ("updating target assigned from %u to %u",
	       solver->target_assigned, solver->consistently_assigned);
	  solver->target_assigned = solver->consistently_assigned;
	  kissat_save_target_phases (solver);
	}

      if (solver->best_assigned < solver->consistently_assigned)
	{
	  LOG ("updating best assigned from %u to %u",
	       solver->best_assigned, solver->consistently_assigned);
	  solver->best_assigned = solver->consistently_assigned;
	  kissat_save_best_phases (solver);
	}

      kissat_reset_consistently_assigned (solver);
    }

  if (reset)
    {
      REPORT (0, type);
      solver->rephased.type = 0;
    }
}

void
bump_glue_vars_chb (kissat *solver, unsigned v)
{
  solver->is_glue_var_chb[v]=false;
  heap *scores = &solver->scores_chb;
  solver->gbumped_chb++;
  const double old_score = kissat_get_heap_score (scores, v);
  double bf = (double) solver->in_glue_chb[v] / (double) solver->total_in_glue_chb; //(double) solver->stable_g_chb;//(double) solver->total_in_glue_chb; //(double) solver->stable_g;
  const double new_score = old_score + old_score*bf;
  //printf("CHB ====> %d %f %f %f\n",v, bf, old_score, new_score);
  
  kissat_update_heap (solver, scores, v, new_score);
  if (new_score > MAX_SCORE)
    rescale_scores (solver, scores);
}

void
bump_glue_vars_vsids (kissat *solver, unsigned v)
{
  solver->is_glue_var_vsids[v]=0;
  heap *scores = &solver->scores;
  solver->gbumped_vsids++;
  const double old_score = kissat_get_heap_score (scores, v);
  double bf = (double) solver->in_glue_vsids[v] / (double) solver->total_in_glue_vsids; /// (double) solver->stable_g_vsids; //(double) solver->total_in_glue_vsids; //(double) solver->stable_g;
  const double new_score = old_score + old_score*bf;
  //printf("VSIDS ====>%d %f %f %f %d %d\n",v, bf, old_score, new_score, solver->stable_g_vsids, solver->in_glue_vsids[v]);
  
  kissat_update_heap (solver, scores, v, new_score);
  if (new_score > MAX_SCORE)
    rescale_scores (solver, scores);
}

void
kissat_backtrack (kissat * solver, unsigned new_level)
{
  assert (solver->level >= new_level);
  if (solver->level == new_level)
    return;

  update_phases (solver);
  LOG ("backtracking to decision level %u", new_level);

  frame *new_frame = &FRAME (new_level + 1);
  const unsigned new_size = new_frame->trail;
  SET_END_OF_STACK (solver->frames, new_frame);

  value *values = solver->values;
  unsigned *trail = BEGIN_STACK (solver->trail);
  assigned *assigned = solver->assigned;

  const unsigned old_size = SIZE_STACK (solver->trail);
  unsigned unassigned = 0, reassigned = 0;

  unsigned j = new_size;
  if (solver->stable)
    {
      heap *scores = solver->heuristic==0?&solver->scores:&solver->scores_chb;
      for (unsigned i = j; i != old_size; i++)
	{
	  const unsigned lit = trail[i];
	  const unsigned idx = IDX (lit);
	  assert (idx < VARS);
	  const unsigned level = assigned[idx].level;
	  if (level <= new_level)
	    {
	      trail[j++] = lit;
	      LOG ("reassign %s", LOGLIT (lit));
	      reassigned++;
	    }
	  else
	    {
        if(solver->heuristic == 0)
         {
           if (solver->is_glue_var_vsids [IDX(lit)])
              bump_glue_vars_vsids (solver, IDX(lit));
         }
         else
         {
            if (solver->is_glue_var_chb [IDX(lit)])
              bump_glue_vars_chb (solver, IDX(lit));
         }
	      unassign (solver, values, lit);
	      add_unassigned_variable_back_to_heap (solver, scores, lit);
	      unassigned++;
	    }
	}
    }
  else
    {
      links *links = solver->links;
      for (unsigned i = j; i != old_size; i++)
	{
	  const unsigned lit = trail[i];
	  const unsigned idx = IDX (lit);
	  assert (idx < VARS);
	  const unsigned level = assigned[idx].level;
	  if (level <= new_level)
	    {
	      trail[j++] = lit;
	      LOG ("reassign %s", LOGLIT (lit));
	      reassigned++;
	    }
	  else
	    {
	      unassign (solver, values, lit);
	      add_unassigned_variable_back_to_queue (solver, links, lit);
	      unassigned++;
	    }
	}
    }
  RESIZE_STACK (solver->trail, j);

  solver->level = new_level;
  LOG ("unassigned %u literals", unassigned);
  LOG ("reassigned %u literals", reassigned);
  (void) unassigned, (void) reassigned;

  assert (new_size <= SIZE_STACK (solver->trail));
  LOG ("propagation will resume at trail position %u", new_size);
  solver->propagated = new_size;

  assert (!solver->extended);
}

void
kissat_backtrack_propagate_and_flush_trail (kissat * solver)
{
  if (solver->level)
    {
      assert (solver->watching);
      assert (solver->level > 0);
      kissat_backtrack (solver, 0);
#ifndef NDEBUG
      clause *conflict =
#endif
	kissat_search_propagate (solver);
      assert (!conflict);
    }
  else
    assert (kissat_propagated (solver));
  if (solver->unflushed)
    kissat_flush_trail (solver);
}
