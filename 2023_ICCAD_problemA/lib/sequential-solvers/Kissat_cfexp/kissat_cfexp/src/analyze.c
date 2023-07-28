#include "analyze.h"
#include "backtrack.h"
#include "bump.h"
#include "deduce.h"
#include "inline.h"
#include "learn.h"
#include "minimize.h"

#include <inttypes.h>

#define INVALID_LEVEL UINT_MAX

static bool
one_literal_on_conflict_level (kissat * solver,
			       clause * conflict,
			       unsigned *conflict_level_ptr)
{
  assert (conflict);
  assert (conflict->size > 1);
  unsigned conflict_level = INVALID_LEVEL;
  unsigned literals_on_conflict_level = 0;
  unsigned forced_lit = INVALID_LIT;

  assigned *all_assigned = solver->assigned;
//    //printf("analyze.c 26: !!!\n");
  unsigned *lits = conflict->lits;
//    //printf("analyze.c 27: !!!\n");
  const unsigned conflict_size = conflict->size;
//    //printf("analyze.c 29: !!!\n");
  const unsigned *end_of_lits = lits + conflict_size;
//    //printf("analyze.c 31: !!!\n");
  for (const unsigned *p = lits; p != end_of_lits; p++)
    {
      const unsigned lit = *p;
      assert (VALUE (lit) < 0);
      const unsigned idx = IDX (lit);
      const unsigned level = all_assigned[idx].level;
      if (conflict_level == level)
	{
	  if (++literals_on_conflict_level > 1 && level == solver->level)
	    break;
	}
      else if (conflict_level == INVALID_LEVEL || conflict_level < level)
	{
	  forced_lit = lit;
	  conflict_level = level;
	  literals_on_conflict_level = 1;
	}
    }
  assert (conflict_level != INVALID_LEVEL);
  assert (literals_on_conflict_level);
    //printf("analyze.c 51: !!!\n");
  LOG ("found %u literals on conflict level %u",
       literals_on_conflict_level, conflict_level);
  *conflict_level_ptr = conflict_level;

  if (!conflict_level)
    {
      solver->inconsistent = true;
      LOG ("learned empty clause from conflict at conflict level zero");
      CHECK_AND_ADD_EMPTY ();
      ADD_EMPTY_TO_PROOF ();
      return false;
    }

  if (conflict_level < solver->level)
    {
      LOG ("forced backtracking due to conflict level %u < level %u",
	   conflict_level, solver->level);
      kissat_backtrack (solver, conflict_level);
    }
//    //printf("analyze.c 71: !!!\n");
  if (conflict_size > 2)
    {
      for (unsigned i = 0; i < 2; i++)
	{
	  const unsigned lit = lits[i];
	  const unsigned lit_idx = IDX (lit);
	  unsigned highest_position = i;
	  unsigned highest_literal = lit;
	  unsigned highest_level = all_assigned[lit_idx].level;
	  for (unsigned j = i + 1; j < conflict_size; j++)
	    {
	      const unsigned other = lits[j];
	      const unsigned other_idx = IDX (other);
	      const unsigned level = all_assigned[other_idx].level;
	      if (highest_level >= level)
		continue;
	      highest_literal = other;
	      highest_position = j;
	      highest_level = level;
	      if (highest_level == conflict_level)
		break;
	    }
	  if (highest_position == i)
	    continue;
	  reference ref = INVALID_REF;
	  if (highest_position > 1)
	    {
	      ref = kissat_reference_clause (solver, conflict);
	      kissat_unwatch_blocking (solver, lit, ref);
	    }
	  lits[highest_position] = lit;
	  lits[i] = highest_literal;
	  if (highest_position > 1)
	    kissat_watch_blocking (solver, lits[i], lits[!i], ref);
	}
    }
//    //printf("analyze.c 108: !!!\n");
  if (literals_on_conflict_level > 1) {
//      //printf("analyze.c 110: !!!\n");
      return false;
  }
  assert (literals_on_conflict_level == 1);
  assert (forced_lit != INVALID_LIT);

  LOG ("reusing conflict as driving clause of %s", LOGLIT (forced_lit));
  kissat_backtrack (solver, solver->level - 1);
  if (conflict_size == 2)
    {
      assert (conflict == &solver->conflict);
      const unsigned other = lits[0] ^ lits[1] ^ forced_lit;
      kissat_assign_binary (solver, conflict->redundant, forced_lit, other);
    }
  else
    {
      const reference ref = kissat_reference_clause (solver, conflict);
      kissat_assign_reference (solver, forced_lit, ref, conflict);
    }
//    //printf("analyze.c 128: !!!\n");
  return true;
}

static void
mark_literal_as_analyzed (kissat * solver, assigned * all_assigned,
			  unsigned lit, const char *type)
{
  const unsigned idx = IDX (lit);
  assigned *a = all_assigned + idx;
  if (a->analyzed == ANALYZED)
    return;
  a->analyzed = ANALYZED;
  LOG ("marking %s literal %s as analyzed", type, LOGLIT (lit));
  PUSH_STACK (solver->analyzed, idx);
  (void) type;
}

static inline void
analyze_reason_side_literals (kissat * solver)
{
  assert (!solver->probing);
  if (!GET_OPTION (bumpreasons))
    return;
  assigned *all_assigned = solver->assigned;
  for (all_stack (unsigned, lit, solver->clause.lits))
      all_assigned[IDX (lit)].analyzed = ANALYZED;
  word *arena = BEGIN_STACK (solver->arena);
  for (all_stack (unsigned, lit, solver->clause.lits))
    {
      const unsigned idx = IDX (lit);
      assigned *a = all_assigned + idx;
      assert (a->level > 0);
      assert (a->reason != UNIT);
      if (a->reason == DECISION)
	continue;
      if (a->binary)
	mark_literal_as_analyzed (solver, all_assigned, a->reason,
				  "reason side");
      else
	{
	  assert (a->reason < SIZE_STACK (solver->arena));
	  clause *c = (clause *) (arena + a->reason);
	  for (all_literals_in_clause (lit, c))
	    if (IDX (lit) != idx)
	      mark_literal_as_analyzed (solver, all_assigned, lit,
					"reason side");
	}
    }
}

static void
reset_levels (kissat * solver)
{
  LOG ("reset %zu marked levels", SIZE_STACK (solver->levels));
  frame *frames = BEGIN_STACK (solver->frames);
  for (all_stack (unsigned, level, solver->levels))
    {
      assert (level < SIZE_STACK (solver->frames));
      frame *f = frames + level;
      assert (f->used > 0);
      f->used = 0;
    }
  CLEAR_STACK (solver->levels);
}

static void
reset_markings (kissat * solver)
{
  LOG ("unmarking %zu analyzed variables", SIZE_STACK (solver->analyzed));
  assigned *all_assigned = solver->assigned;
  for (all_stack (unsigned, idx, solver->analyzed))
      all_assigned[idx].analyzed = 0;
}

static void
reset_analyze (kissat * solver)
{
  LOG ("reset %zu analyzed variables", SIZE_STACK (solver->analyzed));
  CLEAR_STACK (solver->analyzed);

  LOG ("reset %zu learned literals", SIZE_STACK (solver->clause.lits));
  CLEAR_STACK (solver->clause.lits);
}

static void
update_trail_average (kissat * solver)
{
  assert (!solver->probing);
  const unsigned size = SIZE_STACK (solver->trail);
  const unsigned assigned = size - solver->unflushed;
  const unsigned active = solver->active;
  const double filled = kissat_percent (assigned, active);
  LOG ("trail filled %.0f%% (size %u, unflushed %u, active %u)",
       filled, size, solver->unflushed, active);
  UPDATE (trail, filled);
}

int
kissat_analyze (kissat * solver, clause * conflict)
{
  assert (!solver->inconsistent);
  START (analyze);
  //printf("analyze.c 231: !!!\n");
  if (!solver->probing)
    {
      update_trail_average (solver);
      UPDATE (level, solver->level);
    }
  int res;
//    //printf("analyze.c 238: !!!\n");
  do
    {
        //printf("analyze.c 242: !!!\n");
      LOGCLS (conflict, "analyzing conflict %" PRIu64, CONFLICTS);
      unsigned conflict_level;
      if (one_literal_on_conflict_level (solver, conflict, &conflict_level)){
	res = 1;}
      else if (!conflict_level)
	res = -1;
      else if ((conflict = kissat_deduce_first_uip_clause (solver, conflict)))
	{
        //printf("analyze.c 249: !!!\n");
	  reset_markings (solver);
//        //printf("analyze.c 251: !!!\n");
	  reset_analyze (solver);
//        //printf("analyze.c 253: !!!\n");
	  reset_levels (solver);
//        //printf("analyze.c 255: !!!\n");
	  res = 0;
	}
      else
	{
        //printf("analyze.c 256: !!!\n");
	  kissat_minimize_clause (solver);
	  if (!solver->probing)
	    analyze_reason_side_literals (solver);
	  reset_markings (solver);
//        //printf("analyze.c 261: !!!\n");
	  kissat_learn_clause (solver);
//        //printf("analyze.c 263: !!!\n");
	  if (!solver->probing)
	    kissat_bump_variables (solver);
//        //printf("analyze.c 266: !!!\n");
	  reset_analyze (solver);
	  reset_levels (solver);
//        //printf("analyze.c 269: !!!\n");
	  res = 1;
	}
    }
  while (!res);
  STOP (analyze);
    //printf("analyze.c 280: !!!\n");
  return res > 0 ? 0 : 20;
}

static bool
one_literal_on_conflict_level_exp (kissat * solver,
                               clause * conflict,
                               unsigned *conflict_level_ptr)
{
    assert (conflict);
    assert (conflict->size > 1);
    unsigned conflict_level = INVALID_LEVEL;
    unsigned literals_on_conflict_level = 0;
    unsigned forced_lit = INVALID_LIT;

    assigned *all_assigned = solver->assigned;
//    //printf("analyze.c 26: !!!\n");
    unsigned *lits = conflict->lits;
//    //printf("analyze.c 27: !!!\n");
    const unsigned conflict_size = conflict->size;
//    //printf("analyze.c 29: !!!\n");
    const unsigned *end_of_lits = lits + conflict_size;
//    //printf("analyze.c 31: !!!\n");
    for (const unsigned *p = lits; p != end_of_lits; p++)
    {
        const unsigned lit = *p;
        assert (VALUE (lit) < 0);
        const unsigned idx = IDX (lit);
        const unsigned level = all_assigned[idx].level;
        if (conflict_level == level)
        {
            if (++literals_on_conflict_level > 1 && level == solver->level)
                break;
        }
        else if (conflict_level == INVALID_LEVEL || conflict_level < level)
        {
            forced_lit = lit;
            conflict_level = level;
            literals_on_conflict_level = 1;
        }
    }
    assert (conflict_level != INVALID_LEVEL);
    assert (literals_on_conflict_level);
    //printf("analyze.c 51: !!!\n");
    LOG ("found %u literals on conflict level %u",
         literals_on_conflict_level, conflict_level);
    *conflict_level_ptr = conflict_level;

    if (!conflict_level)
    {
        solver->inconsistent = true;
        LOG ("learned empty clause from conflict at conflict level zero");
        CHECK_AND_ADD_EMPTY ();
        ADD_EMPTY_TO_PROOF ();
        return false;
    }

//    if (conflict_level < solver->level)
//    {
//        LOG ("forced backtracking due to conflict level %u < level %u",
//             conflict_level, solver->level);
//        kissat_backtrack (solver, conflict_level);
//    }
    //printf("analyze.c 71: !!!\n");

    if (conflict_size > 2)
    {
        for (unsigned i = 0; i < 2; i++)
        {
            const unsigned lit = lits[i];
            const unsigned lit_idx = IDX (lit);
            unsigned highest_position = i;
            unsigned highest_literal = lit;
            unsigned highest_level = all_assigned[lit_idx].level;
            for (unsigned j = i + 1; j < conflict_size; j++)
            {
                const unsigned other = lits[j];
                const unsigned other_idx = IDX (other);
                const unsigned level = all_assigned[other_idx].level;
                if (highest_level >= level)
                    continue;
                highest_literal = other;
                highest_position = j;
                highest_level = level;
                if (highest_level == conflict_level)
                    break;
            }
            if (highest_position == i)
                continue;
            reference ref = INVALID_REF;
//            if (highest_position > 1)
//            {
//                ref = kissat_reference_clause (solver, conflict);
//                kissat_unwatch_blocking (solver, lit, ref);
//            }
            lits[highest_position] = lit;
            lits[i] = highest_literal;
//            if (highest_position > 1)
//                kissat_watch_blocking (solver, lits[i], lits[!i], ref);
        }
    }
//    //printf("analyze.c 108: !!!\n");
    if (literals_on_conflict_level > 1) {
//      //printf("analyze.c 110: !!!\n");
        return false;
    }
//    assert (literals_on_conflict_level == 1);
//    assert (forced_lit != INVALID_LIT);
//
//    LOG ("reusing conflict as driving clause of %s", LOGLIT (forced_lit));
//    kissat_backtrack (solver, solver->level - 1);
//    if (conflict_size == 2)
//    {
//        assert (conflict == &solver->conflict);
//        const unsigned other = lits[0] ^ lits[1] ^ forced_lit;
//        kissat_assign_binary (solver, conflict->redundant, forced_lit, other);
//    }
//    else
//    {
//        const reference ref = kissat_reference_clause (solver, conflict);
//        kissat_assign_reference (solver, forced_lit, ref, conflict);
//    }
//    //printf("analyze.c 128: !!!\n");
    return true;
}

int
kissat_analyze_exp (kissat * solver, clause * conflict)
{
    assert (!solver->inconsistent);
    START (analyze);
    //printf("analyze.c 291: !!!\n");
    if (!solver->probing)
    {
        update_trail_average (solver);
        UPDATE (level, solver->level);
    }
    int res;
//    //printf("analyze.c 238: !!!\n");
    do
    {
        //printf("analyze.c 301: !!!\n");
        LOGCLS (conflict, "analyzing conflict %" PRIu64, CONFLICTS);
        unsigned conflict_level;
        if (one_literal_on_conflict_level_exp (solver, conflict, &conflict_level)){
            res = 1;}
        else if (!conflict_level)
            res = -1;
        else if ((conflict = kissat_deduce_first_uip_clause (solver, conflict)))
        {
            //printf("analyze.c 310: !!!\n");
            reset_markings (solver);
//        //printf("analyze.c 251: !!!\n");
            reset_analyze (solver);
//        //printf("analyze.c 253: !!!\n");
            reset_levels (solver);
//        //printf("analyze.c 255: !!!\n");
            res = 0;
        }
        else
        {
            //printf("analyze.c 321: !!!\n");
            kissat_minimize_clause (solver);
            if (!solver->probing)
                analyze_reason_side_literals (solver);
            reset_markings (solver);
//        //printf("analyze.c 261: !!!\n");
            kissat_learn_clause_exp (solver);
//        //printf("analyze.c 263: !!!\n");
            if (!solver->probing)
                kissat_bump_variables (solver);
//        //printf("analyze.c 266: !!!\n");
            reset_analyze (solver);
            reset_levels (solver);
//        //printf("analyze.c 269: !!!\n");
            res = 1;
        }
    }
    while (!res);
    STOP (analyze);
    //printf("analyze.c 340: !!!\n");
    return res > 0 ? 0 : 20;
}