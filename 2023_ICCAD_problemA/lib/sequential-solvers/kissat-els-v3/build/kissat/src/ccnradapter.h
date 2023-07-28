#ifndef _ccnr_adapter_h_INCLUDED
#define _ccnr_adapter_h_INCLUDED

#include "ccnr.h"
#include "internal.h"

struct kissat;
struct CCAnr;

// void load_ls_data(kissat * solver, CCAnr * lssolver);
bool call_ls(kissat * solver, CCAnr * lssolver);
// void build_soln_with_UP(kissat * solver, CCAnr * lssolver);
// void build_soln_with_phase(kissat * solver, CCAnr * lssolver);
// void save_ls_phase(kissat * solver, CCAnr * lssolver);
#endif