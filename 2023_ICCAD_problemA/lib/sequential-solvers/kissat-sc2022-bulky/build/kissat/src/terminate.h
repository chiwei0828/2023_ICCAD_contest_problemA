#ifndef _terminate_h_INCLUDED
#define _terminate_h_INCLUDED

#include "internal.h"

#ifndef QUIET
void kissat_report_termination (kissat *, const char *name,
				const char *file, long lineno,
				const char *fun);
#endif

static inline bool
kissat_terminated (kissat * solver, int bit, const char *name,
		   const char *file, long lineno, const char *fun)
{
  assert (0 <= bit), assert (bit < 64);
#ifdef COVERAGE
  const uint64_t mask = (uint64_t) 1 << bit;
  if (!(solver->termination.flagged & mask))
    return false;
  solver->termination.flagged = ~(uint64_t) 0;
#else
  if (!solver->termination.flagged)
    return false;
#endif
#ifndef QUIET
  kissat_report_termination (solver, name, file, lineno, fun);
#else
  (void) file;
  (void) fun;
  (void) lineno;
  (void) name;
#endif
#if !defined (COVERAGE) && defined(NDEBUG)
  (void) bit;
#endif
  return true;
}

#define TERMINATED(BIT) \
  kissat_terminated (solver, BIT, #BIT, __FILE__, __LINE__, __func__)

#define autarky_terminated_1 0
#define autarky_terminated_2 1
#define autarky_terminated_3 2
#define autarky_terminated_4 3
#define backbone_terminated_1 4
#define backbone_terminated_2 5
#define backbone_terminated_3 6
#define backward_terminated_1 7
#define eliminate_terminated_1 8
#define eliminate_terminated_2 9
#define failed_terminated_1 10
#define failed_terminated_2 11
#define forward_terminated_1 12
#define kitten_terminated_1 13
#define rephase_terminated_1 14
#define rephase_terminated_2 15
#define rephase_terminated_3 16
#define search_terminated_1 17
#define substitute_terminated_1 18
#define sweep_terminated_1 19
#define sweep_terminated_2 20
#define sweep_terminated_3 21
#define sweep_terminated_4 22
#define sweep_terminated_5 23
#define sweep_terminated_6 24
#define sweep_terminated_7 25
#define ternary_terminated_1 26
#define ternary_terminated_2 27
#define ternary_terminated_3 28
#define transitive_terminated_1 29
#define transitive_terminated_2 30
#define transitive_terminated_3 31
#define vivify_terminated_1 32
#define vivify_terminated_2 33
#define vivify_terminated_3 34
#define vivify_terminated_4 35
#define walk_terminated_1 36
#define walk_terminated_2 37
#define warmup_terminated_1 38
#define xors_terminated_1 39

#endif
