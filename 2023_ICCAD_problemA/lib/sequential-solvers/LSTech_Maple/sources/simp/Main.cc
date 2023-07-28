/*****************************************************************************************[Main.cc]
Relaxed, lstech -- Copyright (c) 2019-2022, Shaowei Cai, Xindi Zhang, Zhihan Chen: using local search called CCAnr to improve CDCL.
Reference: Shaowei Cai and Xindi Zhang. "Deep Cooperation of CDCL and Local Search for SAT." In SAT 2021, pp 64-81. "best paper award"

Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007,      Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh
 
Maple_LCM, Based on MapleCOMSPS_DRUP -- Copyright (c) 2017, Mao Luo, Chu-Min LI, Fan Xiao: implementing a learnt clause minimisation approach
Reference: M. Luo, C.-M. Li, F. Xiao, F. Manya, and Z. L. , “An effective learnt clause minimization approach for cdcl sat solvers,” in IJCAI-2017, 2017, pp. to–appear.

Maple_LCM_Dist, Based on Maple_LCM -- Copyright (c) 2017, Fan Xiao, Chu-Min LI, Mao Luo: using a new branching heuristic called Distance at the beginning of search

MapleLCMDistChronoBT, based on Maple_LCM_Dist -- Copyright (c), Alexander Nadel, Vadim Ryvchin: "Chronological Backtracking" in SAT-2018, pp. 111-121.

MapleLCMDistChronoBT-DL, based on MapleLCMDistChronoBT -- Copyright (c), Stepan Kochemazov, Oleg Zaikin, Victor Kondratiev, Alexander Semenov: The solver was augmented with heuristic that moves duplicate learnt clauses into the core/tier2 tiers depending on a number of parameters.
 
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>

#include <signal.h>
#include <zlib.h>
#include <sys/resource.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "simp/SimpSolver.h"

using namespace Minisat;

//=================================================================================================


void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("c restarts              : %"PRIu64"\n", solver.starts);
    printf("c duplicate learnts_cnf : %"PRIu64"\n", solver.duplicates_added_conflicts);
    printf("c duplicate learnts_min : %"PRIu64"\n", solver.duplicates_added_minimization);
    printf("c conflicts             : %-12"PRIu64"   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
    printf("c decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
    printf("c propagations          : %-12"PRIu64"   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
    printf("c conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    printf("c backtracks            : %-12"PRIu64"   (NCB %0.f%% , CB %0.f%%)\n", solver.non_chrono_backtrack + solver.chrono_backtrack, (solver.non_chrono_backtrack * 100) / (double)(solver.non_chrono_backtrack + solver.chrono_backtrack), (solver.chrono_backtrack * 100) / (double)(solver.non_chrono_backtrack + solver.chrono_backtrack));
    if (mem_used != 0) printf("c Memory used           : %.2f MB\n", mem_used);
    printf("c CPU time              : %g s\n", cpu_time);
}


static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("c *** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        printStats(*solver);
        printf("\n"); printf("c *** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:

int main(int argc, char** argv)
{
    try {
        setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        printf("c This is MapleLCMDistChronoBT-DL.\n");
        
#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);
        StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        BoolOption   drup   ("MAIN", "drup",   "Generate DRUP UNSAT proof.", false);
        StringOption drup_file("MAIN", "drup-file", "DRUP UNSAT proof ouput file.", "");

        parseOptions(argc, argv, true);
        
        SimpSolver  S;
        double      initial_time = cpuTime(), simp_time, parsed_time, simplified_time;

        if (!pre) S.eliminate(true);

        S.parsing = true;
        S.verbosity = verb;
		S.drup_file = NULL;
        if (drup || strlen(drup_file)){
            S.drup_file = strlen(drup_file) ? fopen(drup_file, "wb") : stdout;
            if (S.drup_file == NULL){
                S.drup_file = stdout;
                printf("c Error opening %s for write.\n", (const char*) drup_file); }
            printf("c DRUP proof generation: %s\n", S.drup_file == stdout ? "stdout" : drup_file);
        }

        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: Virtual memory.\n");
            } }
        
        if (argc == 1)
            printf("c Reading from standard input... Use '--help' for help.\n");

        // gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        // if (in == NULL)
        //     printf("c ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;
        if (S.verbosity > 0){
            printf("c ============================[ Problem Statistics ]=============================\n");
            printf("c |                                                                             |\n"); }
        
        vec<Lit> lits;
        simplify Simp;
        Simp.readfile(argv[1]);

        S.mapidx.growTo(Simp.vars + 1, 0);
        for (int i = 1; i <= Simp.vars; i++) S.mapidx[i] = i;
        printf("c Var num: %d\nc Clause num: %d\n", Simp.vars, Simp.clauses);
        Simp.simplify_init();
        int simpres = Simp.simplify_easy_clause();
        if (S.drup_file){
            for (int i = 1; i <= Simp.drups; i++) {
                int l = Simp.drup_clause[i].size();
                lits.clear();
                for (int j = 0; j < l; j++) {
                    lits.push(Simp.drup_clause[i][j] > 0 ? mkLit(abs(Simp.drup_clause[i][j]) - 1) : ~mkLit(abs(Simp.drup_clause[i][j]) - 1));
                }
                S.adddrup(lits);
            }
        }
        Simp.drup_clause.clear(true);
        if (!simpres) {
            Simp.release();
            delete []Simp.mapto;
            delete []Simp.mapval;
            goto Solve;
        }
        simpres = Simp.simplify_resolution();
        if (!simpres) {
            Simp.release();
            delete []Simp.mapto;
            delete []Simp.mapval;
            Simp.res_clause.clear(true);
            Simp.resolution.clear(true);
            goto Solve;
        }

        if (Simp.clauses <= 15000000)
            simpres = Simp.simplify_binary();
        else {
            for (int i = 1; i <= Simp.orivars; i++)
                Simp.seen[i] = 1;
        } 
        if (S.drup_file){
            for (int i = 1; i <= Simp.drups; i++) {
                int l = Simp.drup_clause[i].size();
                lits.clear();
                for (int j = 0; j < l; j++) {
                    lits.push(Simp.drup_clause[i][j] > 0 ? mkLit(abs(Simp.drup_clause[i][j]) - 1) : ~mkLit(abs(Simp.drup_clause[i][j]) - 1));
                }
                S.adddrup(lits);
            }
        }
        if (!simpres) {
            Simp.release();
            delete []Simp.mapto;
            delete []Simp.mapval;
            Simp.res_clause.clear(true);
            Simp.resolution.clear(true);
            goto Solve;
        }
       
        S.mapidx.clear(true);
        S.mapidx.growTo(Simp.vars + 1, 0);
        for (int i = 1; i <= Simp.orivars; i++) {
            if (Simp.mapto[i]) {
                if (Simp.seen[i] == 1 && Simp.mapto[i] < 0) printf("c wrong mapidx\n");
                if (Simp.seen[i] == 1 && S.mapidx[Simp.mapto[i]] != 0) printf("c wrong mapidx\n");
                if (Simp.seen[i] == 1)
                    S.mapidx[Simp.mapto[i]] = i;
            }
        }

        simp_time = cpuTime();
        printf("c Finish Simplify, use %.2lf seconds\nc ============================[ Solve ]=============================", simp_time - initial_time);
        
        while (Simp.vars > S.nVars()) S.newVar();
        for (int i = 1; i <= Simp.clauses; i++) {
            int l = Simp.clause[i].size();
            lits.clear();
            for (int j = 0; j < l; j++) {
                lits.push(Simp.clause[i][j] > 0 ? mkLit(abs(Simp.clause[i][j]) - 1) : ~mkLit(abs(Simp.clause[i][j]) - 1));
            }
            S.addClause_(lits);
        }
        Simp.release();

        // parse_DIMACS(in, S);
        // gzclose(in);
        
        if (S.verbosity > 0){
            printf("c |  Number of variables:  %12d                                         |\n", S.nVars());
            printf("c |  Number of clauses:    %12d                                         |\n", S.nClauses()); }
        
        parsed_time = cpuTime();
        if (S.verbosity > 0)
            printf("c |  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        signal(SIGINT, SIGINT_interrupt);
        signal(SIGXCPU,SIGINT_interrupt);

        S.parsing = false;
        S.eliminate(true);
        simplified_time = cpuTime();
        if (S.verbosity > 0){
            printf("c |  Simplification time:  %12.2f s                                       |\n", simplified_time - parsed_time);
            printf("c |                                                                             |\n"); }

Solve:
        if (!S.okay() || simpres == 0){
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (S.verbosity > 0){
                printf("c ===============================================================================\n");
                printf("c Solved by simplification\n");
                printStats(S);
                printf("\n"); }
            printf("s UNSATISFIABLE\n");
            if (S.drup_file){
#ifdef BIN_DRUP
                fputc('a', S.drup_file); fputc(0, S.drup_file);
#else
                fprintf(S.drup_file, "0\n");
#endif
            }
            if (S.drup_file && S.drup_file != stdout) fclose(S.drup_file);
            exit(20);
        }

        if (dimacs){
            if (S.verbosity > 0)
                printf("c ==============================[ Writing DIMACS ]===============================\n");
            S.toDimacs((const char*)dimacs);
            if (S.verbosity > 0)
                printStats(S);
            exit(0);
        }

        vec<Lit> dummy;
        lbool ret = S.solveLimited(dummy);
        
        if (S.verbosity > 0){
            printStats(S);
            printf("\n"); }
        printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s UNKNOWN\n");
        if (ret == l_True){
            // check_solution_DIMACS(in, S);
            // printf("%d",S.nVars());
            printf("v ");
            for (int i = 1; i <= Simp.orivars; i++) 
                if (Simp.mapto[i]) {
                    Simp.mapval[i] = (S.model[abs(Simp.mapto[i]) - 1] == l_True ? 1 : -1) * (Simp.mapto[i] > 0 ? 1 : -1);
                }
            
            Simp.print_complete_model();
            
            for (int i = 1; i <= Simp.orivars; i++) {
                printf("%s%d", (i==1)?"":" ", i * Simp.mapval[i]);
            }
            printf(" 0\n");
        }



        if (S.drup_file && ret == l_False){
#ifdef BIN_DRUP
            fputc('a', S.drup_file); fputc(0, S.drup_file);
#else
            fprintf(S.drup_file, "0\n");
#endif
        }
        if (S.drup_file && S.drup_file != stdout) fclose(S.drup_file);

        if (res != NULL){
            if (ret == l_True){
                fprintf(res, "SAT\n");
                
                for (int i = 1; i <= Simp.orivars; i++) {
                    fprintf(res, "%s%d", (i==1)?"":" ", i * Simp.mapval[i]);
                }
                fprintf(res, " 0\n");
            }else if (ret == l_False)
                fprintf(res, "UNSAT\n");
            else
                fprintf(res, "INDET\n");
            fclose(res);
        }
        
        delete []Simp.mapto;
        delete []Simp.mapval;
#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
        printf("c ===============================================================================\n");
        printf("c Out of memory\n");
        printf("s UNKNOWN\n");
        exit(0);
    }
}
