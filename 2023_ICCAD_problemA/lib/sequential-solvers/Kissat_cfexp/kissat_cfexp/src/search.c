#include "analyze.h"
#include "decide.h"
#include "eliminate.h"
#include "internal.h"
#include "logging.h"
#include "print.h"
#include "probe.h"
#include "propsearch.h"
#include "search.h"
#include "reduce.h"
#include "reluctant.h"
#include "report.h"
#include "restart.h"
#include "terminate.h"
#include "trail.h"
#include "walk.h"
#include "bump.h"
#include "relaxed.h"
#include "expscore.h"
#include <inttypes.h>

static void
start_search (kissat * solver)
{
  START (search);
  INC (searches);

  REPORT (0, '*');

  bool stable = (GET_OPTION (stable) == 2);

  solver->stable = stable;
  kissat_phase (solver, "search", GET (searches),
		"initializing %s search after %" PRIu64 " conflicts",
		(stable ? "stable" : "focus"), CONFLICTS);

  kissat_init_averages (solver, &AVERAGES);

  if (solver->stable)
    kissat_init_reluctant (solver);

  kissat_init_limits (solver);

  unsigned seed = GET_OPTION (seed);
  solver->random = seed;
  LOG ("initialized random number generator with seed %u", seed);

  kissat_reset_rephased (solver);

  const unsigned eagersubsume = GET_OPTION (eagersubsume);
  if (eagersubsume && !solver->clueue.elements)
    kissat_init_clueue (solver, &solver->clueue, eagersubsume);
#ifndef QUIET
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  if (!limited->conflicts && !limited->decisions)
    kissat_very_verbose (solver, "starting unlimited search");
  else if (limited->conflicts && !limited->decisions)
    kissat_very_verbose (solver,
			 "starting search with conflicts limited to %" PRIu64,
			 limits->conflicts);
  else if (!limited->conflicts && limited->decisions)
    kissat_very_verbose (solver,
			 "starting search with decisions limited to %" PRIu64,
			 limits->decisions);
  else
    kissat_very_verbose (solver,
			 "starting search with decisions limited to %" PRIu64
			 " and conflicts limited to %" PRIu64,
			 limits->decisions, limits->conflicts);
  if (stable)
    {
      START (stable);
      REPORT (0, '[');
    }
  else
    {
      START (focused);
      REPORT (0, '{');
    }
#endif
}

static void
stop_search (kissat * solver, int res)
{
  if (solver->limited.conflicts)
    {
      LOG ("reset conflict limit");
      solver->limited.conflicts = false;
    }

  if (solver->limited.decisions)
    {
      LOG ("reset decision limit");
      solver->limited.decisions = false;
    }

  if (solver->terminate)
    {
      kissat_very_verbose (solver, "termination forced externally");
      solver->terminate = 0;
    }

#ifndef QUIET
  LOG ("search result %d", res);
  if (solver->stable)
    {
      REPORT (0, ']');
      STOP (stable);
      solver->stable = false;
    }
  else
    {
      REPORT (0, '}');
      STOP (focused);
    }
  char type = (res == 10 ? '1' : res == 20 ? '0' : '?');
  REPORT (0, type);
#else
  (void) res;
#endif

  STOP (search);
}

static void
iterate (kissat * solver)
{
  assert (solver->iterating);
  solver->iterating = false;
  REPORT (0, 'i');
}

static bool
conflict_limit_hit (kissat * solver)
{
  if (!solver->limited.conflicts)
    return false;
  if (solver->limits.conflicts > solver->statistics.conflicts)
    return false;
  kissat_very_verbose (solver, "conflict limit %" PRIu64
		       " hit after %" PRIu64 " conflicts",
		       solver->limits.conflicts,
		       solver->statistics.conflicts);
  return true;
}

static bool
decision_limit_hit (kissat * solver)
{
  if (!solver->limited.decisions)
    return false;
  if (solver->limits.decisions > solver->statistics.decisions)
    return false;
  kissat_very_verbose (solver, "decision limit %" PRIu64
		       " hit after %" PRIu64 " decisions",
		       solver->limits.decisions,
		       solver->statistics.decisions);
  return true;
}

int
kissat_search (kissat * solver)
{
  start_search (solver);
  initialize_relaxed_parameters();
  solver->freeze_ils_gap  = 0;
  solver->freeze_bump_gap = 0;

  solver->lastDecisionHadConflicts = false;
  solver->successiveDecisionsWithoutConfs = 0;
  solver->decisionsWithConflicts = 0;
  solver->decisionsWithoutConflicts = 0;
  solver->CDPhaseCount = 0;

  solver->cur_bump_bounus = 1.0;
  solver->new_clause_lbd = 0;
  solver->clause_num = 0;
  solver->mW = solver->options.mW;
  solver->mS = solver->options.mS;
  solver->prTh = 2;
  solver->exp_ct = 0;
  solver->para_expScore = (double)solver->options.para_expScore;

  int restart_ct = 0;
  infols_initialize(solver);
  expscore_init(solver);
  int res = kissat_walk_initially (solver);
  while (!res)
    {
      clause *conflict = kissat_search_propagate (solver);
      if (conflict){
          solver->lastDecisionHadConflicts = true;
          res = kissat_analyze(solver, conflict);
      }
      else if (solver->iterating)
	iterate (solver);
      else if (!solver->unassigned)
	res = 10;
      else if (TERMINATED (11))
	break;
      else if (conflict_limit_hit (solver))
	break;
      else if (kissat_reducing (solver))
	res = kissat_reduce (solver);
      else if (kissat_restarting (solver))
	{
    kissat_restart(solver);
    if(restart_ct++ % solver->options.aa_freeze_bump == 0){
      infols_bump_update(solver);
    }
  }
      else if (kissat_rephasing (solver))
	kissat_rephase (solver);
      else if (kissat_eliminating (solver))
	res = kissat_eliminate (solver);
      else if (kissat_probing (solver))
	res = kissat_probe (solver);
      else if (!solver->level && solver->unflushed)
	kissat_flush_trail (solver);
      else if (decision_limit_hit (solver))
	break;
      else
	kissat_decide (solver);
    }

  stop_search (solver, res);

  infols_free(solver);
  expscore_free(solver);
  return res;
}