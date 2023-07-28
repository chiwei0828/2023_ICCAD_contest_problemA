#ifndef _internal_h_INCLUDED
#define _internal_h_INCLUDED

#include "arena.h"
#include "assign.h"
#include "averages.h"
#include "check.h"
#include "clause.h"
#include "clueue.h"
#include "cover.h"
#include "extend.h"
#include "smooth.h"
#include "flags.h"
#include "format.h"
#include "frames.h"
#include "heap.h"
#include "kissat.h"
#include "limits.h"
#include "literal.h"
#include "mode.h"
#include "options.h"
#include "phases.h"
#include "profile.h"
#include "proof.h"
#include "queue.h"
#include "random.h"
#include "reluctant.h"
#include "rephase.h"
#include "stack.h"
#include "statistics.h"
#include "literal.h"
#include "value.h"
#include "vector.h"
#include "watch.h"

typedef struct temporary temporary;

struct temporary
{
  bool satisfied;
  bool shrink;
  bool trivial;
  unsigneds lits;
};

typedef struct idxrank idxrank;

struct idxrank
{
  unsigned idx;
  unsigned rank;
};

typedef struct import import;

struct import
{
  unsigned lit:30;
  bool imported:1;
  bool eliminated:1;
};

// *INDENT-OFF*

typedef STACK (value) eliminated;
typedef STACK (import) imports;
typedef STACK (idxrank) idxranks;
typedef STACK (watch) statches;
typedef STACK (watch *) patches;

// *INDENT-ON*

struct kissat
{
#ifdef LOGGING
  bool compacting;
#endif
  bool extended;
  bool inconsistent;
  bool iterating;
  bool probing;
#ifndef QUIET
  bool sectioned;
#endif
  bool stable;
  bool watching;
#ifdef COVERAGE
  volatile unsigned terminate;
#else
  volatile bool terminate;
#endif

  unsigned vars;
  unsigned size;
  unsigned active;

  ints export;
  ints units;
  imports import;
  extensions extend;
  unsigneds witness;

  assigned *assigned;
  flags *flags;

  mark *marks;

  value *values;
  phase *phases;

  eliminated eliminated;
  unsigneds etrail;

  links *links;
  queue queue;

  rephased rephased;

  heap scores;
  double scinc;

// CHB 
  heap scores_chb;
  unsigned *conflicted_chb;
  double step_chb;
  double step_dec_chb;
  double step_min_chb;

// MAB
  unsigned heuristic;
  bool mab;
  double mabc;
  double mab_reward[2];
  unsigned mab_select[2];
  unsigned mab_heuristics;
  double mab_decisions;
  unsigned *mab_chosen;
  unsigned mab_chosen_tot;

  heap schedule;

  unsigned level;
  frames frames;

  unsigneds trail;
  unsigned propagated;

  unsigned best_assigned;
  unsigned consistently_assigned;
  unsigned target_assigned;
  unsigned unflushed;
  unsigned unassigned;

  unsigneds delayed;

#if defined(LOGGING) || !defined(NDEBUG)
  unsigneds resolvent_lits;
#endif
  unsigned resolvent_size;
  unsigned antecedent_size;

  unsigned transitive;

  unsigneds analyzed;
  idxranks bump;
  unsigneds levels;
  unsigneds minimize;
  unsigneds poisoned;
  unsigneds promote;
  unsigneds removable;

  clause conflict;

  temporary clause;

  arena arena;
  clueue clueue;
  vectors vectors;
  reference first_reducible;
  reference last_irredundant;
  watches *watches;

  sizes sorter;

  generator random;
  averages averages[2];
  reluctant reluctant;

  bounds bounds;
  delays delays;
  enabled enabled;
  limited limited;
  limits limits;
  waiting waiting;

  statistics statistics;
  mode mode;

  uint64_t ticks;

  format format;

  statches antecedents[2];
  statches gates[2];
  patches xorted[2];
  unsigneds resolvents;
  bool resolve_gate;

#ifndef NMETRICS
  uint64_t *gate_eliminated;
#else
  bool gate_eliminated;
#endif

#if !defined(NDEBUG) || !defined(NPROOFS)
  unsigneds added;
  unsigneds removed;
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  ints original;
  size_t offset_of_last_original_clause;
#endif

#ifndef QUIET
  profiles profiles;
#endif

#ifndef NOPTIONS
  options options;
#endif

#ifndef NDEBUG
  checker *checker;
#endif

#ifndef NPROOFS
  proof *proof;
#endif

unsigned total_glue, total_size, total_learnt;
unsigned rand_selection;
struct cdata
{
  unsigned succ_no_confs; 
  unsigned confs_last_decision; 
  unsigned total_cdp_len;
  unsigned num_cdp;
  unsigned decisions_with_confs;
  unsigned decisions_without_confs;
  bool substantial_cd_phase, backtrack_at_substantial_cd_phase;
  unsigned start_dlevel_current_cd_phase;
  unsigned confs_since_restart;
  unsigneds cd_phase_decisions;
  unsigned action_applied_amid_cd;
  unsigned last_decision;
  int decide_rand;
  unsigned rand_select_start;
  int exploration_depth_bound;
  unsigned rand_dec_confs;
  unsigned rand_dec_learn_glue;
  unsigned rand_dec_learn_size;
  unsigned decide_rand_success;
  unsigned decide_rand_success_tries;

  } cdata;

  // glue bumping method
int * is_glue_var_chb, *is_glue_var_vsids, * is_decision_chb, *is_decision_vsids;
unsigned * in_glue_chb, *in_glue_vsids;
unsigned total_in_glue_chb, total_in_glue_vsids;
double max_bf;
int gbumped_chb, gbumped_vsids;
int stable_g_chb, stable_g_vsids;

};

#define VARS (solver->vars)
#define LITS (2*solver->vars)

static inline unsigned
kissat_assigned (kissat * solver)
{
  assert (VARS >= solver->unassigned);
  return VARS - solver->unassigned;
}

#define all_variables(IDX) \
  unsigned IDX = 0, IDX_END = solver->vars; IDX != IDX_END; ++IDX

#define all_literals(LIT) \
  unsigned LIT = 0, LIT_END = LITS; LIT != LIT_END; ++LIT

#define all_clauses(C) \
  clause * C     = (clause*) BEGIN_STACK (solver->arena), \
         * C_END = (clause*) END_STACK (solver->arena), \
	 * C_NEXT; \
  C != C_END && (C_NEXT = kissat_next_clause (C), true); \
  C = C_NEXT

#endif
