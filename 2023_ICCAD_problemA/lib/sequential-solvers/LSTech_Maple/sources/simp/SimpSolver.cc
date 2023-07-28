/***********************************************************************************[SimpSolver.cc]
Relaxed, lstech -- Copyright (c) 2019-2022, Shaowei Cai, Xindi Zhang, Zhihan Chen: using local search called CCAnr to improve CDCL.
Reference: Shaowei Cai and Xindi Zhang. "Deep Cooperation of CDCL and Local Search for SAT." In SAT 2021, pp 64-81. "best paper award"

MiniSat -- Copyright (c) 2006,      Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010, Niklas Sorensson

Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh
 
Maple_LCM, Based on MapleCOMSPS_DRUP -- Copyright (c) 2017, Mao Luo, Chu-Min LI, Fan Xiao: implementing a learnt clause minimisation approach
Reference: M. Luo, C.-M. Li, F. Xiao, F. Manya, and Z. L. , “An effective learnt clause minimization approach for cdcl sat solvers,” in IJCAI-2017, 2017, pp. to–appear.
 
Maple_LCM_Dist, Based on Maple_LCM -- Copyright (c) 2017, Fan Xiao, Chu-Min LI, Mao Luo: using a new branching heuristic called Distance at the beginning of search
 
 
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

#include "mtl/Sort.h"
#include "simp/SimpSolver.h"
#include "utils/System.h"
#include <cstdio>
#include <cstring>
#include <fstream>

#define TOLIT(x) ((x) > 0 ? (x) : ((-x) + vars))
#define NEG(x) ((x) > vars ? ((x) - vars) : ((x) + vars))
using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "SIMP";

static BoolOption   opt_use_asymm        (_cat, "asymm",        "Shrink clauses by asymmetric branching.", false);
static BoolOption   opt_use_rcheck       (_cat, "rcheck",       "Check if a clause is already implied. (costly)", false);
static BoolOption   opt_use_elim         (_cat, "elim",         "Perform variable elimination.", true);
static IntOption    opt_grow             (_cat, "grow",         "Allow a variable elimination step to grow by a number of clauses.", 0);
static IntOption    opt_clause_lim       (_cat, "cl-lim",       "Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit", 20,   IntRange(-1, INT32_MAX));
static IntOption    opt_subsumption_lim  (_cat, "sub-lim",      "Do not check if subsumption against a clause larger than this. -1 means no limit.", 1000, IntRange(-1, INT32_MAX));
static DoubleOption opt_simp_garbage_frac(_cat, "simp-gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered during simplification.",  0.5, DoubleRange(0, false, HUGE_VAL, false));


//=================================================================================================
// Constructor/Destructor:


SimpSolver::SimpSolver() :
    parsing            (false)
  , grow               (opt_grow)
  , clause_lim         (opt_clause_lim)
  , subsumption_lim    (opt_subsumption_lim)
  , simp_garbage_frac  (opt_simp_garbage_frac)
  , use_asymm          (opt_use_asymm)
  , use_rcheck         (opt_use_rcheck)
  , use_elim           (opt_use_elim)
  , merges             (0)
  , asymm_lits         (0)
  , eliminated_vars    (0)
  , elimorder          (1)
  , use_simplification (true)
  , occurs             (ClauseDeleted(ca))
  , elim_heap          (ElimLt(n_occ))
  , bwdsub_assigns     (0)
  , n_touched          (0)
{
    vec<Lit> dummy(1,lit_Undef);
    ca.extra_clause_field = true; // NOTE: must happen before allocating the dummy clause below.
    bwdsub_tmpunit        = ca.alloc(dummy);
    remove_satisfied      = false;
}


SimpSolver::~SimpSolver()
{
}

simplify::simplify():
  vars                  (0),
  clauses               (0)
{}

char *read_whitespace(char *p) {
    while ((*p >= 9 && *p <= 13) || *p == 32)
        ++p;
    return p;
}
char *read_until_new_line(char *p)
{
    while (*p != '\n')
    {
        if (*p == '\0')
        {
            printf("c parse error: unexpected EOF");
            exit(0);
        }
        ++p;
    }
    return ++p;
}

char *read_int(char *p, int *i)
{
    *i = 0;
    bool sym = true;
    p = read_whitespace(p);
    if (*p == '-')
        sym = false, ++p;
    while (*p >= '0' && *p <= '9')
    {
        if (*p == '\0')
            return p;
        *i = *i * 10 + *p - '0';
        ++p;
    }
    if (!sym)
        *i = -(*i);
    return p;
}

void simplify::readfile(const char *file) {
    std::string infile(file);
	std::ifstream fin(infile);
    fin.seekg(0, fin.end);
	size_t file_len = fin.tellg();
	fin.seekg(0, fin.beg);
	char *data = new char[file_len + 1];
	fin.read(data, file_len);
	fin.close();
	data[file_len] = '\0';
    char *p = data;
    clause.push();
    clause.push();
    int num_clauses = 1;
    while (*p != '\0')
    {   
        p = read_whitespace(p);
        if (*p == '\0')
            break;
        if (*p == 'c')
            p = read_until_new_line(p);
        else if (*p == 'p')
        {
            p += 5;
            p = read_int(p, &vars);
            p = read_int(p, &clauses);
            orivars = vars;
            oriclauses = clauses;  
        }
        else
        {
            int32_t dimacs_lit;
            p = read_int(p, &dimacs_lit);
            if (*p == '\0' && dimacs_lit != 0)
            {
                printf("c PARSE ERROR! Unexpected EOF\n");
                exit(0);
            }
            if (dimacs_lit == 0)
                num_clauses += 1, clause.push();
            else
                clause[num_clauses].push(dimacs_lit);
        }
    }
    if (num_clauses != clauses + 1) {
        printf("c parse warning: clauses: %d, real clauses: %d\n", clauses, num_clauses - 1);
        clauses = num_clauses - 1;
    }
    delete []data;
}

inline int pnsign(int x) {
    return (x > 0 ? 1 : -1);
}
inline int litsign(int x) {
    return x % 2 == 1 ? -1 : 1;
}
inline int tolit(int x) {
    if (x > 0) return x * 2;
    else return (-x) * 2 + 1;
}
inline int toidx(int x) {
    return (x & 1 ? -(x >> 1) : (x >> 1));
}
inline int reverse(int x) {
    if (x % 2 == 1) return x - 1;
    else return x + 1;
}
inline ll simplify::mapv(int a, int b) {
    return 1ll * a * nlit + (ll)b;
}

int simplify::find(int x) {
    if (f[x] == x) return x;
    int fa = f[x];
    f[x] = find(fa);
    val[x] = val[fa] * val[x];
    return f[x];
}

void simplify::simplify_init() {
    f = new int[vars + 10];
    val = new int[vars + 10];
    color = new int[vars + 10];
    varval = new int[vars + 10];
    q = new int[vars + 10];
    clean = new int[vars + 10];
    seen = new int[(vars << 1) + 10];
    clause_delete.growTo(clauses+1, 0);
    nxtc.growTo(clauses+1, 0);
    occurp = new vec<int>[vars + 1];
    occurn = new vec<int>[vars + 1];    
    resseen = new int[(vars << 1) + 10];
    mapval = new int[vars + 10];
    mapto = new int[vars + 10];
    for (int i = 1; i <= vars; i++) mapto[i] = i, mapval[i] = 0;
    for (int i = 1; i <= clauses; i++) {
        int l = clause[i].size();
        if (l > maxlen) maxlen = l;
    }
    a = new int[maxlen + 1];
}

void simplify::release() {
    delete []f;
    delete []val;
    delete []color;
    delete []varval;
    delete []q;
    delete []clean;
    delete []seen;
    clause_delete.clear(true);
    nxtc.clear(true);
    delete []resseen;
    delete []a;
    delete []mapfrom; 
    for (int i = 0; i <= vars; i++)
        occurp[i].clear(true), occurn[i].clear(true);
    delete []occurp;
    delete []occurn;
    clause.clear(true);
}


bool simplify::res_is_empty(int x) {
    int op = occurp[x].size(), on = occurn[x].size();
    for (int i = 0; i < op; i++) {
        int o1 = occurp[x][i], l1 = clause[o1].size();
        if (clause_delete[o1]) continue;
        for (int j = 0; j < l1; j++)
            if (abs(clause[o1][j]) != x) resseen[abs(clause[o1][j])] = pnsign(clause[o1][j]);
        for (int j = 0; j < on; j++) {
            int o2 = occurn[x][j], l2 = clause[o2].size(), flag = 0;
            if (clause_delete[o2]) continue;
            for (int k = 0; k < l2; k++)
                if (abs(clause[o2][k]) != x && resseen[abs(clause[o2][k])] == -pnsign(clause[o2][k])) {
                    flag = 1; break;
                }
            if (!flag) {
                for (int j = 0; j < l1; j++)
                    resseen[abs(clause[o1][j])] = 0;
                return false;
            }
        }
        for (int j = 0; j < l1; j++)
            resseen[abs(clause[o1][j])] = 0;
    }
    return true; 
}

bool simplify::simplify_resolution() {
    for (int i = 1; i <= vars; i++) {
        occurn[i].clear();
        occurp[i].clear();
        resseen[i] = resseen[i + vars] = clean[i] = seen[i] = 0;
    }
    for (int i = 1; i <= clauses; i++) {
        int l = clause[i].size();
        clause_delete[i] = 0;
        for (int j = 0; j < l; j++)
            if (clause[i][j] > 0) occurp[abs(clause[i][j])].push(i);
            else occurn[abs(clause[i][j])].push(i);
    }
    for (int i = 1; i <= vars; i++)
        if (occurn[i].size() == 0 && occurp[i].size() == 0) clean[i] = 1;  

    int l = 1, r = 0;         
    for (int i = 1; i <= vars; i++) {
        int op = occurp[i].size(), on = occurn[i].size();
        if (op * on > op + on || clean[i]) continue;
        if (res_is_empty(i)) {
            q[++r] = i, clean[i] = 1;
        }
    }

    int now_turn = 0, seen_flag = 0;
    vec<int> vars;
    while (l <= r) {
        ++now_turn;
        for (int j = l; j <= r; j++) {
            int i = q[j];
            int op = occurp[i].size(), on = occurn[i].size();
            for (int j = 0; j < op; j++) clause_delete[occurp[i][j]] = 1;
            for (int j = 0; j < on; j++) clause_delete[occurn[i][j]] = 1;
        }
        int ll = l; l = r + 1;
        
        vars.clear();
        ++seen_flag;
        for (int u = ll; u <= r; u++) {
            int i = q[u];
            int op = occurp[i].size(), on = occurn[i].size();
            for (int j = 0; j < op; j++) {
                int o = occurp[i][j], l = clause[o].size();
                for (int k = 0; k < l; k++) {
                    int v = abs(clause[o][k]);
                    if (!clean[v] && seen[v] != seen_flag)
                        vars.push(v), seen[v] = seen_flag;
                }
            }
            for (int j = 0; j < on; j++) {
                int o = occurn[i][j], l = clause[o].size();
                for (int k = 0; k < l; k++) {
                    int v = abs(clause[o][k]);
                    if (!clean[v] && seen[v] != seen_flag)
                        vars.push(v), seen[v] = seen_flag;
                }
            }
        }
        for (int u = 0; u < vars.size(); u++) {
            int i = vars[u];
            int op = 0, on = 0;
            for (int j = 0; j < occurp[i].size(); j++) op += 1 - clause_delete[occurp[i][j]];
            for (int j = 0; j < occurn[i].size(); j++) on += 1 - clause_delete[occurn[i][j]];
            if (op * on > op + on) continue;
            if (res_is_empty(i)) {
                q[++r] = i, clean[i] = 1;
            }
        }
    }
    vars.clear(true);
    if (!r) return true;
    res_clauses = 0;
    res_clause.push();
    for (int i = 1; i <= clauses; i++) {
        if (!clause_delete[i]) continue;
        ++res_clauses;
        res_clause.push();
        int l = clause[i].size();
        for (int j = 0; j < l; j++) {
            res_clause[res_clauses].push(pnsign(clause[i][j]) * mapfrom[abs(clause[i][j])]);
        }
    }
    resolutions = r;
    resolution.push();
    for (int i = 1; i <= r; i++) {
        int v = mapfrom[q[i]];
        resolution.push(v);
        if (!v) puts("c wrong mapfrom");
        mapto[v] = 0, mapval[v] = -10;
    }
    update_var_clause_label();
    for (int i = 1; i <= orivars; i++) {
        if (mapto[i]) {
            if (!color[mapto[i]]) puts("c wrong color");
            mapto[i] = color[mapto[i]];
            mapfrom[mapto[i]] = i;
        }
    }
    return true;
}

void simplify::update_var_clause_label() {
    int remain_var = 0;
    for (int i = 1; i <= vars; i++) color[i] = 0;
    for (int i = 1; i <= clauses; i++) {
        if (clause_delete[i]) continue;
        int l = clause[i].size();
        for (int j = 0; j < l; j++) {
            if (color[abs(clause[i][j])] == 0) color[abs(clause[i][j])] = ++remain_var;       
        }
    }

    int id = 0;
    for (int i = 1; i <= clauses; i++) {
        if (clause_delete[i]) {clause[i].setsize(0); continue;}
        ++id;
        int l = clause[i].size();
        if (i == id) {
            for (int j = 0; j < l; j++)
                clause[id][j] = color[abs(clause[i][j])] * pnsign(clause[i][j]);    
            continue;
        }
        clause[id].setsize(0);
        for (int j = 0; j < l; j++)
            clause[id].push(color[abs(clause[i][j])] * pnsign(clause[i][j]));
    }
    printf("c After simplify: vars: %d -> %d , clauses: %d -> %d ,\n", vars, remain_var, clauses, id);
    for (int i = id + 1; i <= clauses; i++) 
        clause[i].clear(true);
    for (int i = remain_var + 1; i <= vars; i++)
        occurp[i].clear(true), occurn[i].clear(true);
    clause.setsize(id + 1);
    vars = remain_var, clauses = id;
}

bool simplify::simplify_binary() {
    auto clk_st = std::chrono::high_resolution_clock::now();    
    for (int i = 1; i <= clauses; i++) {
        int l = clause[i].size();
        for (int j = 0; j < l; j++)
            clause[i][j] = tolit(clause[i][j]);
    }
    nlit = 2 * vars + 2;
    int simplify = 1, turn = 0;
    for (int i = 1; i <= vars; i++) f[i] = i, val[i] = 1, varval[i] = color[i] = 0;
    for (int i = 1; i <= clauses; i++) clause_delete[i] = 0;

    int len = 0;
    for (int i = 1; i <= clauses; i++) {
        if (clause[i].size() != 2) continue;
        nxtc[++len] = i;
        ll id1 = mapv(clause[i][0], clause[i][1]),
           id2 = mapv(clause[i][1], clause[i][0]);
        C.insert(id1, i);
        C.insert(id2, i);
    }

    drups = 0;
    drup_clause.push();
    while (simplify) {
        simplify = 0;
        ++turn;        
        for (int k = 1; k <= len; k++) {
            int i = nxtc[k];
            if (clause[i].size() != 2 || clause_delete[i]) continue;
            ll id1 = mapv(reverse(clause[i][0]), reverse(clause[i][1])),
               id2 = mapv(clause[i][0], reverse(clause[i][1])),
               id3 = mapv(reverse(clause[i][0]), clause[i][1]);
            int r = C.get(id1, 0);
            if (r) {
                simplify = 1;
                clause_delete[r] = clause_delete[i] = 1;
                int fa = find(clause[i][0] >> 1), fb = find(clause[i][1] >> 1);
                int sig = litsign(clause[i][0]) * litsign(clause[i][1]) * (-1);
                //sig == 1 : a = b   -1 : a = -b
                if (fa != fb) {
                    if (fa < fb) {
                        f[fa] = fb;
                        val[fa] = sig / (val[clause[i][0] >> 1] * val[clause[i][1] >> 1]);
                        if (varval[fa])
                            varval[fb] = val[fa] * varval[fa];
                    }
                    else if (fa > fb) {
                        f[fb] = fa;
                        val[fb] = sig / (val[clause[i][0] >> 1] * val[clause[i][1] >> 1]);
                        if (varval[fb])
                            varval[fa] = val[fb] * varval[fb];
                    }
                }
                else {
                    if (sig != val[clause[i][0] >> 1] * val[clause[i][1] >> 1])
                        return false;
                }
            }
            int d1 = C.get(id2, 0);
            if (d1) {
                int v = clause[i][0] >> 1;
                if (varval[v] && varval[v] != litsign(clause[i][0])) {
                    return false;
                }
                clause_delete[d1] = clause_delete[i] = 1;
                simplify = 1;
                if (!varval[v]) {
                    varval[v] = litsign(clause[i][0]);
                    drup_clause.push();
                    drup_clause[++drups].push(mapfrom[v] * varval[v]);
                }
            }
            int d2 = C.get(id3, 0);
            if (d2) {
                int v = clause[i][1] >> 1;
                if (varval[v] && varval[v] != litsign(clause[i][1])) {
                    return false;
                }
                clause_delete[d2] = clause_delete[i] = 1;
                simplify = 1;
                if (!varval[v]) {
                    varval[v] = litsign(clause[i][1]);
                    drup_clause.push();
                    drup_clause[++drups].push(mapfrom[v] * varval[v]);
                }
            }
        }

        for (int i = 1; i <= vars; i++) {
            int x = find(i);
            if (varval[i] && x != i) {
                if (varval[x]) {
                    if (varval[x] != varval[i] * val[i])
                        return false;
                }
                else {
                    varval[x] = varval[i] * val[i];
                    drup_clause.push();
                    drup_clause[++drups].push(mapfrom[x] * varval[x]);
                }
            }
        }
        for (int i = 1; i <= vars; i++) 
            if (varval[f[i]]) {
                if (varval[i]) {
                    if (varval[f[i]] != varval[i] * val[i])
                        return false;
                }
                else {
                    varval[i] = varval[f[i]] * val[i];
                    drup_clause.push();
                    drup_clause[++drups].push(mapfrom[i] * varval[i]);
                }
            }

        len = 0;

        for (int i = 1; i <= clauses; i++) {
            if (clause_delete[i]) continue;
            int l = clause[i].size(), oril = l;
            for (int j = 0; j < l; j++) {
                int fa = f[clause[i][j] >> 1];
                a[j] = tolit(litsign(clause[i][j]) * val[clause[i][j] >> 1] * fa);
            }
            int t = 0;
            for (int j = 0; j < l; j++) {
                int x = varval[a[j] >> 1];
                if (x) {
                    int k = x * litsign(a[j]);
                    if (k == 1) {
                        if (!clause_delete[i]) simplify = 1;
                        clause_delete[i] = 1, a[t++] = a[j];
                    }
                }
                else a[t++] = a[j];
            }
            if (t == 0) return false;
            if (t != l) simplify = 1, l = t;
            t = 0;
            for (int j = 0; j < l; j++) {
                if (resseen[a[j]] == i) continue;
                resseen[a[j]] = i, a[t++] = a[j];
            }
            if (t != l) simplify = 1, l = t;
            for (int j = 0; j < l; j++)
                if (resseen[reverse(a[j])] == i && !clause_delete[i])
                    clause_delete[i] = 1, simplify = 1;
            
            for (int j = 0; j < l; j++) resseen[a[j]] = 0;
                
            if (l == 1) {
                if (litsign(a[0]) * varval[a[0] >> 1] == -1) return false;
                simplify = 1;
                varval[a[0] >> 1] = litsign(a[0]);
            }
            if (!clause_delete[i] && l == 2 && oril != 2) {
                nxtc[++len] = i;
                ll id1 = mapv(a[0], a[1]),
                   id2 = mapv(a[1], a[0]);
                C.insert(id1, i);
                C.insert(id2, i);
            }
            else if (!clause_delete[i] && l == 2 &&  oril == 2) {
                if (a[0] == clause[i][0] && a[1] == clause[i][1]) ;
                else if (a[1] == clause[i][0] && a[0] == clause[i][1]) ;
                else {
                    nxtc[++len] = i;
                    ll id1 = mapv(a[0], a[1]),
                       id2 = mapv(a[1], a[0]);
                    C.insert(id1, i);
                    C.insert(id2, i);
                }
            }
            int diff = clause[i].size() == l ? 0 : 1;
            if (!diff) {
                for (int j = 0; j < l; j++)
                    if (a[j] != clause[i][j]) {diff = 1; break;}
            }
            clause[i].clear();
            for (int j = 0; j < l; j++)
                clause[i].push(a[j]);
            if (!clause_delete[i] && diff) {
                drup_clause.push();
                ++drups;
                for (int j = 0; j < l; j++) {
                    int v = a[j] >> 1;
                    drup_clause[drups].push(mapfrom[v] * litsign(a[j]));
                }
            }
        }

        for (int i = 1; i <= vars; i++) {
            int x = find(i);
            if (varval[i] && x != i) {
                if (varval[x]) {
                    if (varval[x] != varval[i] * val[i])
                        return false;
                }
                else {
                    varval[x] = varval[i] * val[i];
                    drup_clause.push();
                    drup_clause[++drups].push(mapfrom[x] * varval[x]);
                }
            }
        }
        for (int i = 1; i <= vars; i++) 
            if (varval[f[i]]) {
                if (varval[i]) {
                    if (varval[f[i]] != varval[i] * val[i])
                        return false;
                }
                else {
                    varval[i] = varval[f[i]] * val[i];
                    drup_clause.push();
                    drup_clause[++drups].push(mapfrom[i] * varval[i]);
                }
            }
    }

    for (int i = 1; i <= clauses; i++) {
        if (clause_delete[i]) continue;
        int l = clause[i].size();
        for (int j = 0; j < l; j++) {
            clause[i][j] = litsign(clause[i][j]) * (clause[i][j] >> 1);
        }
    }
    update_var_clause_label();
    for (int i = 1; i <= orivars; i++) {
        if (mapval[i]) {
            if (mapto[i]) puts("c wrong mapto");
            continue; 
        }
        int v = mapto[i], fa = find(v);
        if (varval[v] || varval[fa]) {
            if (varval[v] * val[v] != varval[fa]) puts("c wrong varval equal");
            if (color[v]) puts("c wrong equal var colored");
            mapval[i] = varval[v];
            mapto[i] = 0;
        }
        else if (color[fa]) {
            if (fa == v) seen[i] = 1;
            else seen[i] = 0;
            mapto[i] = color[fa] * val[v];
        }
        else mapval[i] = val[v], mapto[i] = 0;
    }
    return true;
}

bool simplify::simplify_easy_clause() {
    for (int i = 1; i <= vars; i++) {
        varval[i] = 0;
        occurp[i].clear();
        occurn[i].clear();
        resseen[i] = resseen[i + vars] = 0;
    }
    drups = 0;
    drup_clause.push();
    for (int i = 1; i <= clauses; i++) clause_delete[i] = 0;
    int head = 1, tail = 0;
    for (int i = 1; i <= clauses; i++) {
        int l = clause[i].size(), t = 0;
        for (int j = 0; j < l; j++) {
            int lit = TOLIT(clause[i][j]);
            if (resseen[lit] == i) continue;
            if (resseen[NEG(lit)] == i) {clause_delete[i] = 1; break;}
            clause[i][t++] = clause[i][j];
            resseen[lit] = i;
        }
        if (clause_delete[i]) continue;
        clause[i].setsize(t);
        if (l != t) {
            drup_clause.push();
            drups++;
            for (int j = 0; j < t; j++)
                drup_clause[drups].push(clause[i][j]);
        }
        for (int j = 0; j < t; j++) 
            if (clause[i][j] > 0) occurp[clause[i][j]].push(i);
            else occurn[-clause[i][j]].push(i);
        if (t == 0) return false;
        if (t == 1) {
            int lit = clause[i][0];
            clause_delete[i] = 1;
            if (varval[abs(lit)]) {
                if (varval[abs(lit)] == pnsign(lit)) continue;
                else return false;
            }
            varval[abs(lit)] = pnsign(lit); 
            q[++tail] = abs(lit); 
        }
    }
    for (int i = 1; i <= vars + vars; i++) resseen[i] = 0;
    while (head <= tail) {
        int x = q[head++];
        if (varval[x] == 1) {
            for (int i = 0; i < occurp[x].size(); i++)
                clause_delete[occurp[x][i]] = 1;
            for (int i = 0; i < occurn[x].size(); i++) {
                int o = occurn[x][i], t = 0;
                int l = clause[o].size();
                if (clause_delete[o]) continue;
                for (int j = 0; j < l; j++) {
                    if (varval[abs(clause[o][j])] == pnsign(clause[o][j])) {
                        clause_delete[o] = 1; break;
                    }
                    if (varval[abs(clause[o][j])] == -pnsign(clause[o][j])) continue;
                    clause[o][t++] = clause[o][j];
                }
                if (clause_delete[o]) continue;
                if (l != t) {
                    drup_clause.push();
                    drups++;
                    for (int j = 0; j < t; j++)
                        drup_clause[drups].push(clause[o][j]);
                }
                clause[o].setsize(t);
                if (t == 0) return false;
                if (t == 1) {
                    int lit = clause[o][0];
                    clause_delete[o] = 1;
                    if (varval[abs(lit)]) {
                        if (varval[abs(lit)] == pnsign(lit)) continue;
                        else return false;
                    }
                    varval[abs(lit)] = pnsign(lit); 
                    q[++tail] = abs(lit); 
                }
            }
        }
        else {
            for (int i = 0; i < occurn[x].size(); i++)
                clause_delete[occurn[x][i]] = 1;
            for (int i = 0; i < occurp[x].size(); i++) {
                int o = occurp[x][i], t = 0;
                if (clause_delete[o]) continue;
                int l = clause[o].size();
                for (int j = 0; j < l; j++) {
                    if (varval[abs(clause[o][j])] == pnsign(clause[o][j])) {
                        clause_delete[o] = 1; break;
                    }
                    if (varval[abs(clause[o][j])] == -pnsign(clause[o][j])) continue;
                    clause[o][t++] = clause[o][j];
                }
                if (clause_delete[o]) continue;
                if (l != t) {
                    drup_clause.push();
                    drups++;
                    for (int j = 0; j < t; j++)
                        drup_clause[drups].push(clause[o][j]);
                }
                clause[o].setsize(t);
                if (t == 0) return false;
                if (t == 1) {
                    int lit = clause[o][0];
                    clause_delete[o] = 1;
                    if (varval[abs(lit)]) {
                        if (varval[abs(lit)] == pnsign(lit)) continue;
                        else return false;
                    }
                    varval[abs(lit)] = pnsign(lit); 
                    q[++tail] = abs(lit); 
                }
            }
        }
    }

    update_var_clause_label();
    for (int i = 1; i <= tail; i++) {
        int v = q[i];
        mapval[v] = varval[v];
        if (color[v]) puts("c wrong unit");
    }
    mapfrom = new int[vars + 1];
    for (int i = 1; i <= vars; i++) mapfrom[i] = 0;
    for (int i = 1; i <= orivars; i++) {
        if (color[i])
            mapto[i] = color[i], mapfrom[color[i]] = i;
        else if (!mapval[i]) // not in unit queue, then it is no use var
            mapto[i] = 0, mapval[i] = 1;
        else
            mapto[i] = 0;
    }
    return true;
}

void simplify::print_complete_model() {
    int r = 0;
    for (int i = 1; i <= orivars; i++) 
        if (!mapto[i]) {
            if (!mapval[i]) puts("c wrong empty val");
            else if (abs(mapval[i]) != 1) mapval[i] = 0, ++r;
        }
    if (r != resolutions) puts("c wrong resolution num");
    if (r) { 
        occurp = new vec<int>[orivars + 1];
        occurn = new vec<int>[orivars + 1];   
        for (int i = 1; i <= orivars; i++) {
            occurp[i].clear(), occurn[i].clear();
        }
        vec<int> clause_state;
        clause_state.growTo(res_clauses + 1, 0);
        for (int i = 1; i <= res_clauses; i++) {
            int satisify = 0;
            for (int j = 0; j < res_clause[i].size(); j++) {
                int v = res_clause[i][j];
                if (v > 0) occurp[v].push(i);
                else occurn[-v].push(i);
                if (pnsign(v) * mapval[abs(v)] == 1) satisify = 1;
                if (!mapval[abs(v)]) ++clause_state[i];
            }
            if (satisify) clause_state[i] = -1;
            if (!clause_state) puts("c wrong unsat clause");
        }
        for (int ii = resolutions; ii >= 1; ii--) {
            int v = resolution[ii];
            if (v > orivars || v <= 0) puts("c wrong idx");
            //attempt 1
            int assign = 1;
            for (int i = 0; i < occurn[v].size(); i++) {
                int o = occurn[v][i];
                if (clause_state[o] != -1 && clause_state[o] <= 1) {assign = 0; break;}
            }
            if (assign == 1) {
                mapval[v] = 1;
                for (int i = 0; i < occurn[v].size(); i++) {
                    int o = occurn[v][i];
                    if (clause_state[o] != -1) clause_state[o]--;
                } 
                for (int i = 0; i < occurp[v].size(); i++) 
                    clause_state[occurp[v][i]] = -1;
                continue;
            }
            //attempt -1
            assign = -1;
            for (int i = 0; i < occurp[v].size(); i++) {
                int o = occurp[v][i];
                if (clause_state[o] != -1 && clause_state[o] <= 1) {assign = 0; break;}
            }
            if (assign == -1) {
                mapval[v] = -1;
                for (int i = 0; i < occurp[v].size(); i++) {
                    int o = occurp[v][i];
                    if (clause_state[o] != -1) clause_state[o]--;
                } 
                for (int i = 0; i < occurn[v].size(); i++) 
                    clause_state[occurn[v][i]] = -1;
                continue;
            }
            printf("c wrong assign");
        }
        clause_state.clear(true);
        for (int i = 1; i <= orivars; i++) {
            occurp[i].clear(true), occurn[i].clear(true);
        }
        delete []occurp;
        delete []occurn;
        res_clause.clear(true);
        resolution.clear(true);
    }  
}

Var SimpSolver::newVar(bool sign, bool dvar) {
    Var v = Solver::newVar(sign, dvar);

    frozen    .push((char)false);
    eliminated.push((char)false);

    if (use_simplification){
        n_occ     .push(0);
        n_occ     .push(0);
        occurs    .init(v);
        touched   .push(0);
        elim_heap .insert(v);
    }
    return v; }



lbool SimpSolver::solve_(bool do_simp, bool turn_off_simp)
{
    vec<Var> extra_frozen;
    lbool    result = l_True;

    do_simp &= use_simplification;

    if (do_simp){
        // Assumptions must be temporarily frozen to run variable elimination:
        for (int i = 0; i < assumptions.size(); i++){
            Var v = var(assumptions[i]);

            // If an assumption has been eliminated, remember it.
            assert(!isEliminated(v));

            if (!frozen[v]){
                // Freeze and store.
                setFrozen(v, true);
                extra_frozen.push(v);
            } }

        result = lbool(eliminate(turn_off_simp));
    }

    if (result == l_True)
        result = Solver::solve_();
    else if (verbosity >= 1)
        printf("c ===============================================================================\n");

    if (result == l_True)
        extendModel();

    if (do_simp)
        // Unfreeze the assumptions that were frozen:
        for (int i = 0; i < extra_frozen.size(); i++)
            setFrozen(extra_frozen[i], false);

    return result;
}



bool SimpSolver::addClause_(vec<Lit>& ps)
{
#ifndef NDEBUG
    for (int i = 0; i < ps.size(); i++)
        assert(!isEliminated(var(ps[i])));
#endif

    int nclauses = clauses.size();

    if (use_rcheck && implied(ps))
        return true;

    if (!Solver::addClause_(ps))
        return false;

    if (!parsing && drup_file) {
#ifdef BIN_DRUP
        binDRUP(mapidx, 'a', ps, drup_file);
#else
        for (int i = 0; i < ps.size(); i++)
            fprintf(drup_file, "%i ", (var(ps[i]) + 1) * (-2 * sign(ps[i]) + 1));
        fprintf(drup_file, "0\n");
#endif
    }

    if (use_simplification && clauses.size() == nclauses + 1){
        CRef          cr = clauses.last();
        const Clause& c  = ca[cr];

        // NOTE: the clause is added to the queue immediately and then
        // again during 'gatherTouchedClauses()'. If nothing happens
        // in between, it will only be checked once. Otherwise, it may
        // be checked twice unnecessarily. This is an unfortunate
        // consequence of how backward subsumption is used to mimic
        // forward subsumption.
        subsumption_queue.insert(cr);
        for (int i = 0; i < c.size(); i++){
            occurs[var(c[i])].push(cr);
            n_occ[toInt(c[i])]++;
            touched[var(c[i])] = 1;
            n_touched++;
            if (elim_heap.inHeap(var(c[i])))
                elim_heap.increase(var(c[i]));
        }
    }

    return true;
}


void SimpSolver::removeClause(CRef cr)
{
    const Clause& c = ca[cr];

    if (use_simplification)
        for (int i = 0; i < c.size(); i++){
            n_occ[toInt(c[i])]--;
            updateElimHeap(var(c[i]));
            occurs.smudge(var(c[i]));
        }

    Solver::removeClause(cr);
}


bool SimpSolver::strengthenClause(CRef cr, Lit l)
{
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);
    assert(use_simplification);

    // FIX: this is too inefficient but would be nice to have (properly implemented)
    // if (!find(subsumption_queue, &c))
    subsumption_queue.insert(cr);

    if (drup_file){
#ifdef BIN_DRUP
        binDRUP_strengthen(mapidx, c, l, drup_file);
#else
        for (int i = 0; i < c.size(); i++)
            if (c[i] != l) fprintf(drup_file, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
        fprintf(drup_file, "0\n");
#endif
    }

    if (c.size() == 2){
        removeClause(cr);
        c.strengthen(l);
    }else{
        if (drup_file){
#ifdef BIN_DRUP
            binDRUP(mapidx, 'd', c, drup_file);
#else
            fprintf(drup_file, "d ");
            for (int i = 0; i < c.size(); i++)
                fprintf(drup_file, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
            fprintf(drup_file, "0\n");
#endif
        }

        detachClause(cr, true);
        c.strengthen(l);
        attachClause(cr);
        remove(occurs[var(l)], cr);
        n_occ[toInt(l)]--;
        updateElimHeap(var(l));
    }

    return c.size() == 1 ? enqueue(c[0]) && propagate() == CRef_Undef : true;
}


// Returns FALSE if clause is always satisfied ('out_clause' should not be used).
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause)
{
    merges++;
    out_clause.clear();

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps  =  ps_smallest ? _qs : _ps;
    const Clause& qs  =  ps_smallest ? _ps : _qs;

    for (int i = 0; i < qs.size(); i++){
        if (var(qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(ps[j]) == var(qs[i]))
                    if (ps[j] == ~qs[i])
                        return false;
                    else
                        goto next;
            out_clause.push(qs[i]);
        }
        next:;
    }

    for (int i = 0; i < ps.size(); i++)
        if (var(ps[i]) != v)
            out_clause.push(ps[i]);

    return true;
}


// Returns FALSE if clause is always satisfied.
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, int& size)
{
    merges++;

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps  =  ps_smallest ? _qs : _ps;
    const Clause& qs  =  ps_smallest ? _ps : _qs;
    const Lit*  __ps  = (const Lit*)ps;
    const Lit*  __qs  = (const Lit*)qs;

    size = ps.size()-1;

    for (int i = 0; i < qs.size(); i++){
        if (var(__qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(__ps[j]) == var(__qs[i]))
                    if (__ps[j] == ~__qs[i])
                        return false;
                    else
                        goto next;
            size++;
        }
        next:;
    }

    return true;
}


void SimpSolver::gatherTouchedClauses()
{
    if (n_touched == 0) return;

    int i,j;
    for (i = j = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 0)
            ca[subsumption_queue[i]].mark(2);

    for (i = 0; i < touched.size(); i++)
        if (touched[i]){
            const vec<CRef>& cs = occurs.lookup(i);
            for (j = 0; j < cs.size(); j++)
                if (ca[cs[j]].mark() == 0){
                    subsumption_queue.insert(cs[j]);
                    ca[cs[j]].mark(2);
                }
            touched[i] = 0;
        }

    for (i = 0; i < subsumption_queue.size(); i++)
        if (ca[subsumption_queue[i]].mark() == 2)
            ca[subsumption_queue[i]].mark(0);

    n_touched = 0;
}


bool SimpSolver::implied(const vec<Lit>& c)
{
    assert(decisionLevel() == 0);

    trail_lim.push(trail.size());
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True){
            cancelUntil(0);
            return true;
        }else if (value(c[i]) != l_False){
            assert(value(c[i]) == l_Undef);
            uncheckedEnqueue(~c[i]);
        }

    bool result = propagate() != CRef_Undef;
    cancelUntil(0);
    return result;
}


// Backward subsumption + backward subsumption resolution
bool SimpSolver::backwardSubsumptionCheck(bool verbose)
{
    int cnt = 0;
    int subsumed = 0;
    int deleted_literals = 0;
    assert(decisionLevel() == 0);

    while (subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()){

        // Empty subsumption queue and return immediately on user-interrupt:
        if (asynch_interrupt){
            subsumption_queue.clear();
            bwdsub_assigns = trail.size();
            break; }

        // Check top-level assignments by creating a dummy clause and placing it in the queue:
        if (subsumption_queue.size() == 0 && bwdsub_assigns < trail.size()){
            Lit l = trail[bwdsub_assigns++];
            ca[bwdsub_tmpunit][0] = l;
            ca[bwdsub_tmpunit].calcAbstraction();
            subsumption_queue.insert(bwdsub_tmpunit); }

        CRef    cr = subsumption_queue.peek(); subsumption_queue.pop();
        Clause& c  = ca[cr];

        if (c.mark()) continue;

        if (verbose && verbosity >= 2 && cnt++ % 1000 == 0)
            printf("c subsumption left: %10d (%10d subsumed, %10d deleted literals)\r", subsumption_queue.size(), subsumed, deleted_literals);

        assert(c.size() > 1 || value(c[0]) == l_True);    // Unit-clauses should have been propagated before this point.

        // Find best variable to scan:
        Var best = var(c[0]);
        for (int i = 1; i < c.size(); i++)
            if (occurs[var(c[i])].size() < occurs[best].size())
                best = var(c[i]);

        // Search all candidates:
        vec<CRef>& _cs = occurs.lookup(best);
        CRef*       cs = (CRef*)_cs;

        for (int j = 0; j < _cs.size(); j++)
            if (c.mark())
                break;
            else if (!ca[cs[j]].mark() &&  cs[j] != cr && (subsumption_lim == -1 || ca[cs[j]].size() < subsumption_lim)){
                Lit l = c.subsumes(ca[cs[j]]);

                if (l == lit_Undef)
                    subsumed++, removeClause(cs[j]);
                else if (l != lit_Error){
                    deleted_literals++;

                    if (!strengthenClause(cs[j], ~l))
                        return false;

                    // Did current candidate get deleted from cs? Then check candidate at index j again:
                    if (var(l) == best)
                        j--;
                }
            }
    }

    return true;
}


bool SimpSolver::asymm(Var v, CRef cr)
{
    Clause& c = ca[cr];
    assert(decisionLevel() == 0);

    if (c.mark() || satisfied(c)) return true;

    trail_lim.push(trail.size());
    Lit l = lit_Undef;
    for (int i = 0; i < c.size(); i++)
        if (var(c[i]) != v){
            if (value(c[i]) != l_False)
                uncheckedEnqueue(~c[i]);
        }else
            l = c[i];

    if (propagate() != CRef_Undef){
        cancelUntil(0);
        asymm_lits++;
        if (!strengthenClause(cr, l))
            return false;
    }else
        cancelUntil(0);

    return true;
}


bool SimpSolver::asymmVar(Var v)
{
    assert(use_simplification);

    const vec<CRef>& cls = occurs.lookup(v);

    if (value(v) != l_Undef || cls.size() == 0)
        return true;

    for (int i = 0; i < cls.size(); i++)
        if (!asymm(v, cls[i]))
            return false;

    return backwardSubsumptionCheck();
}


static void mkElimClause(vec<uint32_t>& elimclauses, Lit x)
{
    elimclauses.push(toInt(x));
    elimclauses.push(1);
}


static void mkElimClause(vec<uint32_t>& elimclauses, Var v, Clause& c)
{
    int first = elimclauses.size();
    int v_pos = -1;

    // Copy clause to elimclauses-vector. Remember position where the
    // variable 'v' occurs:
    for (int i = 0; i < c.size(); i++){
        elimclauses.push(toInt(c[i]));
        if (var(c[i]) == v)
            v_pos = i + first;
    }
    assert(v_pos != -1);

    // Swap the first literal with the 'v' literal, so that the literal
    // containing 'v' will occur first in the clause:
    uint32_t tmp = elimclauses[v_pos];
    elimclauses[v_pos] = elimclauses[first];
    elimclauses[first] = tmp;

    // Store the length of the clause last:
    elimclauses.push(c.size());
}



bool SimpSolver::eliminateVar(Var v)
{
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    // Split the occurrences into positive and negative:
    //
    const vec<CRef>& cls = occurs.lookup(v);
    vec<CRef>        pos, neg;
    for (int i = 0; i < cls.size(); i++)
        (find(ca[cls[i]], mkLit(v)) ? pos : neg).push(cls[i]);

    // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover, no
    // clause must exceed the limit on the maximal clause size (if it is set):
    //
    int cnt         = 0;
    int clause_size = 0;

    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, clause_size) && 
                (++cnt > cls.size() + grow || (clause_lim != -1 && clause_size > clause_lim)))
                return true;

    // Delete and store old clauses:
    eliminated[v] = true;
    setDecisionVar(v, false);
    eliminated_vars++;

    if (pos.size() > neg.size()){
        for (int i = 0; i < neg.size(); i++)
            mkElimClause(elimclauses, v, ca[neg[i]]);
        mkElimClause(elimclauses, mkLit(v));
    }else{
        for (int i = 0; i < pos.size(); i++)
            mkElimClause(elimclauses, v, ca[pos[i]]);
        mkElimClause(elimclauses, ~mkLit(v));
    }

    // Produce clauses in cross product:
    vec<Lit>& resolvent = add_tmp;
    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(ca[pos[i]], ca[neg[j]], v, resolvent) && !addClause_(resolvent))
                return false;

    for (int i = 0; i < cls.size(); i++)
        removeClause(cls[i]); 

    // Free occurs list for this variable:
    occurs[v].clear(true);
    
    // Free watchers lists for this variable, if possible:
    watches_bin[ mkLit(v)].clear(true);
    watches_bin[~mkLit(v)].clear(true);
    watches[ mkLit(v)].clear(true);
    watches[~mkLit(v)].clear(true);

    return backwardSubsumptionCheck();
}


bool SimpSolver::substitute(Var v, Lit x)
{
    assert(!frozen[v]);
    assert(!isEliminated(v));
    assert(value(v) == l_Undef);

    if (!ok) return false;

    eliminated[v] = true;
    setDecisionVar(v, false);
    const vec<CRef>& cls = occurs.lookup(v);
    
    vec<Lit>& subst_clause = add_tmp;
    for (int i = 0; i < cls.size(); i++){
        Clause& c = ca[cls[i]];

        subst_clause.clear();
        for (int j = 0; j < c.size(); j++){
            Lit p = c[j];
            subst_clause.push(var(p) == v ? x ^ sign(p) : p);
        }

        if (!addClause_(subst_clause))
            return ok = false;

        removeClause(cls[i]);
    }

    return true;
}


void SimpSolver::extendModel()
{
    int i, j;
    Lit x;

    for (i = elimclauses.size()-1; i > 0; i -= j){
        for (j = elimclauses[i--]; j > 1; j--, i--)
            if (modelValue(toLit(elimclauses[i])) != l_False)
                goto next;

        x = toLit(elimclauses[i]);
        model[var(x)] = lbool(!sign(x));
    next:;
    }
}

// Almost duplicate of Solver::removeSatisfied. Didn't want to make the base method 'virtual'.
void SimpSolver::removeSatisfied()
{
    int i, j;
    for (i = j = 0; i < clauses.size(); i++){
        const Clause& c = ca[clauses[i]];
        if (c.mark() == 0)
            if (satisfied(c))
                removeClause(clauses[i]);
            else
                clauses[j++] = clauses[i];
    }
    clauses.shrink(i - j);
}

// The technique and code are by the courtesy of the GlueMiniSat team. Thank you!
// It helps solving certain types of huge problems tremendously.
bool SimpSolver::eliminate(bool turn_off_elim)
{
    bool res = true;
    int iter = 0;
    int n_cls, n_cls_init, n_vars;

    if (nVars() == 0) goto cleanup; // User disabling preprocessing.

    // Get an initial number of clauses (more accurately).
    if (trail.size() != 0) removeSatisfied();
    n_cls_init = nClauses();

    res = eliminate_(); // The first, usual variable elimination of MiniSat.
    if (!res) goto cleanup;

    n_cls  = nClauses();
    n_vars = nFreeVars();

    printf("c Reduced to %d vars, %d cls (grow=%d)\n", n_vars, n_cls, grow);

    if ((double)n_cls / n_vars >= 10 || n_vars < 10000){
        printf("c No iterative elimination performed. (vars=%d, c/v ratio=%.1f)\n", n_vars, (double)n_cls / n_vars);
        goto cleanup; }

    grow = grow ? grow * 2 : 8;
    for (; grow < 10000; grow *= 2){
        // Rebuild elimination variable heap.
        for (int i = 0; i < clauses.size(); i++){
            const Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (!elim_heap.inHeap(var(c[j])))
                    elim_heap.insert(var(c[j]));
                else
                    elim_heap.update(var(c[j])); }

        int n_cls_last = nClauses();
        int n_vars_last = nFreeVars();

        res = eliminate_();
        if (!res || n_vars_last == nFreeVars()) break;
        iter++;

        int n_cls_now  = nClauses();
        int n_vars_now = nFreeVars();

        double cl_inc_rate  = (double)n_cls_now   / n_cls_last;
        double var_dec_rate = (double)n_vars_last / n_vars_now;

        printf("c Reduced to %d vars, %d cls (grow=%d)\n", n_vars_now, n_cls_now, grow);
        printf("c cl_inc_rate=%.3f, var_dec_rate=%.3f\n", cl_inc_rate, var_dec_rate);

        if (n_cls_now > n_cls_init || cl_inc_rate > var_dec_rate) break;
    }
    printf("c No. effective iterative eliminations: %d\n", iter);

cleanup:
    touched  .clear(true);
    occurs   .clear(true);
    n_occ    .clear(true);
    elim_heap.clear(true);
    subsumption_queue.clear(true);

    use_simplification    = false;
    remove_satisfied      = true;
    ca.extra_clause_field = false;

    // Force full cleanup (this is safe and desirable since it only happens once):
    rebuildOrderHeap();
    garbageCollect();

    return res;
}


bool SimpSolver::eliminate_()
{
    if (!simplify())
        return false;
    else if (!use_simplification)
        return true;

    int trail_size_last = trail.size();

    // Main simplification loop:
    //
    while (n_touched > 0 || bwdsub_assigns < trail.size() || elim_heap.size() > 0){

        gatherTouchedClauses();
        // printf("  ## (time = %6.2f s) BWD-SUB: queue = %d, trail = %d\n", cpuTime(), subsumption_queue.size(), trail.size() - bwdsub_assigns);
        if ((subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()) && 
            !backwardSubsumptionCheck(true)){
            ok = false; goto cleanup; }

        // Empty elim_heap and return immediately on user-interrupt:
        if (asynch_interrupt){
            assert(bwdsub_assigns == trail.size());
            assert(subsumption_queue.size() == 0);
            assert(n_touched == 0);
            elim_heap.clear();
            goto cleanup; }

        // printf("  ## (time = %6.2f s) ELIM: vars = %d\n", cpuTime(), elim_heap.size());
        for (int cnt = 0; !elim_heap.empty(); cnt++){
            Var elim = elim_heap.removeMin();
            
            if (asynch_interrupt) break;

            if (isEliminated(elim) || value(elim) != l_Undef) continue;

            if (verbosity >= 2 && cnt % 100 == 0)
                printf("c elimination left: %10d\r", elim_heap.size());

            if (use_asymm){
                // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                bool was_frozen = frozen[elim];
                frozen[elim] = true;
                if (!asymmVar(elim)){
                    ok = false; goto cleanup; }
                frozen[elim] = was_frozen; }

            // At this point, the variable may have been set by assymetric branching, so check it
            // again. Also, don't eliminate frozen variables:
            if (use_elim && value(elim) == l_Undef && !frozen[elim] && !eliminateVar(elim)){
                ok = false; goto cleanup; }

            checkGarbage(simp_garbage_frac);
        }

        assert(subsumption_queue.size() == 0);
    }
 cleanup:
    // To get an accurate number of clauses.
    if (trail_size_last != trail.size())
        removeSatisfied();
    else{
        int i,j;
        for (i = j = 0; i < clauses.size(); i++)
            if (ca[clauses[i]].mark() == 0)
                clauses[j++] = clauses[i];
        clauses.shrink(i - j);
    }
    checkGarbage();

    if (verbosity >= 1 && elimclauses.size() > 0)
        printf("c |  Eliminated clauses:     %10.2f Mb                                      |\n", 
               double(elimclauses.size() * sizeof(uint32_t)) / (1024*1024));

    return ok;
}


//=================================================================================================
// Garbage Collection methods:


void SimpSolver::relocAll(ClauseAllocator& to)
{
    if (!use_simplification) return;

    // All occurs lists:
    //
    occurs.cleanAll();
    for (int i = 0; i < nVars(); i++){
        vec<CRef>& cs = occurs[i];
        for (int j = 0; j < cs.size(); j++)
            ca.reloc(cs[j], to);
    }

    // Subsumption queue:
    //
    for (int i = 0; i < subsumption_queue.size(); i++)
        ca.reloc(subsumption_queue[i], to);

    // Temporary clause:
    //
    ca.reloc(bwdsub_tmpunit, to);
}


void SimpSolver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    to.extra_clause_field = ca.extra_clause_field; // NOTE: this is important to keep (or lose) the extra fields.
    relocAll(to);
    Solver::relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
