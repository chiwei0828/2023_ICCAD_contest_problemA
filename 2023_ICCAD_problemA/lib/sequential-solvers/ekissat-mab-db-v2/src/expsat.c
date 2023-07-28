/*#include "internal.h"

void reset_exp_structures (kissat * solver)
{
   if (solver->cdata.exp.occurence_in_episode)
   {
    free (solver->cdata.exp.occurence_in_episode);
    solver->cdata.exp.occurence_in_episode = calloc (solver->vars+1, sizeof (unsigned));
   }
}

void reset_conflict_structures_exp (kissat * solver)
{
    reset_conflict_structures (solver);
}

unsigned pick_at_random (kissat * solver)
{
    kissat_decide (solver);
    return solver->cdata.last_decision;
}



int trigger_exp_episode (kissat  * solver)
{
    //printf ("\n here %d %d",solver->cdata.exp.max_walks,solver->cdata.exp.max_steps);
    solver->cdata.exp.exploring = 1;
    reset_exp_structures (solver);
    int solver_level = solver->level;
    for (int i=0; i<solver->cdata.exp.max_walks; i++)
    {
        CLEAR_STACK (solver->cdata.exp.walk_vars);
        int conflict_step = -1;
        for (int j=0; j<solver->cdata.exp.max_steps; j++)
        {
            if (solver->unassigned == 0)
                return 10;
            unsigned idx = pick_at_random (solver);
            if (idx)
            {
                clause * conflict = kissat_search_propagate_exp (solver);
                if (conflict)
                {
                    //kissat_analyze (solver, conflict);
                    conflict_step = j+1;
                    break;
                }
            }
        }
        kissat_backtrack (solver, solver_level);
        printf ("\nB. %d", solver->level);

    }
    solver->cdata.exp.exploring = 0;
    return 0;
}

// clause *
// kissat_search_propagate_exp (kissat * solver)
// {
// //   assert (!solver->probing);
// //   assert (solver->watching);
// //   assert (!solver->inconsistent);

//   //START (propagate);

//   solver->ticks = 0;
//   const unsigned propagated = solver->propagated;
//   clause *res = 0;
//   while (!res && solver->propagated < SIZE_STACK (solver->trail))
//     {
//       const unsigned lit = PEEK_STACK (solver->trail, solver->propagated);
//       res = search_propagate_literal (solver, lit);
//     }
//   //update_search_propagation_statistics (solver, propagated);
//   //update_consistently_assigned (solver);
//   return res;
// }

// clause *
// search_propagate_exp (kissat * solver)
// {
//   clause *res = 0;
//   while (!res && solver->propagated < SIZE_STACK (solver->trail))
//     {
//       const unsigned lit = PEEK_STACK (solver->trail, solver->propagated);
//       res = search_propagate_literal (solver, lit);
//     }
//   return res;
// }

// void assign_random_step (kissat * solver, unsigned idx)
// {
//  solver->level++;
//  const value value = decide_phase_exp (solver, idx);
//  unsigned lit = LIT (idx);
//   if (value < 0)
//     lit = NOT (lit);
//   kissat_push_frame (solver, lit);
//   assert (solver->level < SIZE_STACK (solver->frames));
//   kissat_assign_decision (solver, lit);
// }

*/