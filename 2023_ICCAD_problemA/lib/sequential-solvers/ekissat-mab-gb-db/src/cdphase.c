#include "internal.h"

void track_cdcbphase (kissat * solver)
{
    if(solver->cdata.confs_last_decision==0)
    {
        solver->cdata.decisions_without_confs++;
        solver->cdata.succ_no_confs++;
        int substantial_cd_factor = GET_OPTION (substantialcdfactor);
        double threshold = 
                   ((double) solver->cdata.decisions_without_confs /
                    (double) solver->cdata.decisions_with_confs ) * (double) substantial_cd_factor;
       
        solver->cdata.substantial_cd_phase = solver->cdata.confs_since_restart && 
                    ((double) solver->cdata.succ_no_confs >  threshold) ;
    }
    else
    {
        solver->cdata.decisions_with_confs++;
        solver->cdata.start_dlevel_current_cd_phase = solver->level;
        if(solver->cdata.succ_no_confs)
        {
            solver->cdata.total_cdp_len +=  solver->cdata.succ_no_confs;
            solver->cdata.num_cdp++;
            solver->cdata.succ_no_confs=0;  
        } 
        if (solver->cdata.decide_rand)
        {
            solver->cdata.decide_rand_success++;
            solver->cdata.decide_rand_success_tries += (solver->statistics.decisions - solver->cdata.rand_select_start);
        }
        reset_after_cdpahse (solver);
    }
    if (solver->cdata.substantial_cd_phase && solver->cdata.confs_since_restart) // apply action if in a substantial CD phase and we have seen at least a conflict after the current restart.
    {   
        action_cdphase_depth_bounded_random_selection (solver);
        solver->cdata.action_applied_amid_cd++;
    }
    solver->cdata.confs_last_decision = 0;
}


void action_cdphase_depth_bounded_random_selection (kissat * solver)
{
    if (!solver->cdata.decide_rand)
    {
        solver->cdata.decide_rand = 1;
        solver->cdata.rand_select_start = solver->statistics.decisions;
    }
    else 
    {
        unsigned rand_selections = solver->statistics.decisions - solver->cdata.rand_select_start;
        if (rand_selections == solver->cdata.exploration_depth_bound)
            reset_after_no_luck (solver);
    }
}


void reset_after_cdpahse (kissat * solver)
{
    solver->cdata.substantial_cd_phase = false;
    solver->cdata.succ_no_confs = 0;
    solver->cdata.backtrack_at_substantial_cd_phase = false;
    solver->cdata.start_dlevel_current_cd_phase = 0;

    solver->cdata.decide_rand = 0;
    solver->cdata.rand_select_start = 0;
}

void reset_after_no_luck (kissat * solver)
{
    solver->cdata.total_cdp_len +=  solver->cdata.succ_no_confs;
    reset_after_cdpahse (solver);
}

void cdphase_at_restart (kissat * solver)
{
     solver->cdata.confs_since_restart = 0;  
     solver->cdata.start_dlevel_current_cd_phase = 0;
}