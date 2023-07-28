#include "simplify.h"
#include "internal.h"
#include "import.h"
#include "hashmap.h"
#include "math.h"
#include <stdio.h>
#include <stdlib.h>

#include <ctype.h>
#include <inttypes.h>
#define TOLIT(x) ((x) > 0 ? (x) : ((-x) + S->vars))
#define NEG(x) ((x) > S->vars ? ((x) - S->vars) : ((x) + S->vars))
typedef long long ll;
int nlit;

simplify * simplify_init() {
    simplify *s = (simplify *)malloc(sizeof(simplify));
    return s;
} 

#define NEXT() \
	next(file, lineno_ptr)

static int
next(file *file, uint64_t *lineno_ptr)
{
	int ch = kissat_getc(file);
	if (ch == '\n')
		*lineno_ptr += 1;
	return ch;
}

static const char *
nonl(int ch, const char *str, uint64_t *lineno_ptr)
{
	if (ch == '\n')
	{
		assert(*lineno_ptr > 1);
		*lineno_ptr -= 1;
	}
	return str;
}

bool simplify_store_clause(simplify *S, int v) {
    if (v == 0) {
		S->real_clauses++;
        int sz = S->store_clause->sz;
		S->clause_size[S->real_clauses] = sz;
		S->clause[S->real_clauses] = (int*)malloc(sizeof(int)*sz);
		for (int i = 0; i < sz; i++)
			S->clause[S->real_clauses][i] = cvec_data(S->store_clause, i);
		cvec_clear(S->store_clause);
        if (!sz) return false;
	}
    else cvec_push(S->store_clause, v);
    return true;
}

void simplify_alloc(simplify *S, int vars, int clauses) {
	S->vars = S->orivars = vars;
	S->clauses = S->oriclauses = clauses;
	S->real_clauses = 0;
	S->clause = (int**)malloc(sizeof(int*)*(clauses+1));
	S->clause_size = (int*)malloc(sizeof(int)*(clauses+1));
	S->color = (int*)malloc(sizeof(int)*(vars+1));
	S->varval = (int*)malloc(sizeof(int)*(vars+1));
    S->clean = (int*)malloc(sizeof(int)*(vars+1));
    S->queue = (int*)malloc(sizeof(int)*(vars+1));

    S->mapval = (int*)malloc(sizeof(int)*(vars+1));
    S->mapto = (int*)malloc(sizeof(int)*(vars+1));    
    
	S->occurp = (int**)malloc(sizeof(int*)*(vars+1));
	S->occurn = (int**)malloc(sizeof(int*)*(vars+1));
	S->occurp_size = (int*)malloc(sizeof(int)*(vars+1));
	S->occurn_size = (int*)malloc(sizeof(int)*(vars+1));
	
	S->seen = (int*)malloc(sizeof(int)*(2*vars+2));
	S->clause_delete = (int*)malloc(sizeof(int)*(clauses+1));
    S->resseen = (int*)malloc(sizeof(int)*(2*vars+2));
    S->store_clause = cvec_init();

    for (int i = 1; i <= vars; i++)
        S->mapto[i] = i, S->mapval[i] = 0;
}

void simplify_release(simplify *S) {
    for (int i = 1; i <= S->vars; i++) {
        if (S->occurp[i] != NULL) free(S->occurp[i]);
        if (S->occurn[i] != NULL) free(S->occurn[i]);
    }
    for (int i = 1; i <= S->clauses; i++) {
        free(S->clause[i]);
    }
    free(S->clause);
    free(S->clause_size);
    free(S->color);
    free(S->varval);
    free(S->clean);
    free(S->queue);
    free(S->occurp);
    free(S->occurn);
    free(S->occurn_size);
    free(S->occurp_size);
    free(S->seen);
    free(S->clause_delete);
    free(S->resseen);
    free(S->mapfrom);
    cvec_release(S->store_clause);

}
 
static const char *
simplify_parse(simplify *S, file *file, uint64_t *lineno_ptr)
{
	*lineno_ptr = 1;
	bool first = true;
	int ch;
	for (;;)
	{
		ch = NEXT();
		if (ch == 'p')
			break;
		else if (ch == EOF)
		{
			if (first)
				return "empty file";
			else
				return "end-of-file before header";
		}
		first = false;
		if (ch == '\r')
		{
			ch = NEXT();
			if (ch != '\n')
				return "expected new-line after carriage-return";
		}
		else if (ch == '\n')
		{
		}
		else if (ch == 'c')
		{
		START:
			ch = NEXT();
			if (ch == '\n')
				continue;
			else if (ch == '\r')
			{
				ch = NEXT();
				if (ch != '\n')
					return "expected new-line after carriage-return";
				continue;
			}
			else if (ch == EOF)
				return "end-of-file in header comment";
			else if (ch == ' ' || ch == '\t')
				goto START;
            while ((ch = NEXT()) != '\n')
                if (ch == EOF)
                    return "end-of-file in header comment";
                else if (ch == '\r')
                {
                    ch = NEXT();
                    if (ch != '\n')
                        return "expected new-line after carriage-return";
                    break;
                }
		}
		else
			return "expected 'c' or 'p' at start of line";
	}
	assert(ch == 'p');
	ch = NEXT();
	if (ch != ' ')
		return nonl(ch, "expected space after 'p'", lineno_ptr);
	ch = NEXT();
	if (ch != 'c')
		return nonl(ch, "expected 'c' after 'p '", lineno_ptr);
	ch = NEXT();
	if (ch != 'n')
		return nonl(ch, "expected 'n' after 'p c'", lineno_ptr);
	ch = NEXT();
	if (ch != 'f')
		return nonl(ch, "expected 'n' after 'p cn'", lineno_ptr);
	ch = NEXT();
	if (ch != ' ')
		return nonl(ch, "expected space after 'p cnf'", lineno_ptr);
	ch = NEXT();
	if (!isdigit(ch))
		return nonl(ch, "expected digit after 'p cnf '", lineno_ptr);
	int variables = ch - '0';
	while (isdigit(ch = NEXT()))
	{
		if (EXTERNAL_MAX_VAR / 10 < variables)
			return "maximum variable too large";
		variables *= 10;
		const int digit = ch - '0';
		if (EXTERNAL_MAX_VAR - digit < variables)
			return "maximum variable too large";
		variables += digit;
	}
	if (ch == EOF)
		return "unexpected end-of-file while parsing maximum variable";
	if (ch == '\r')
	{
		ch = NEXT();
		if (ch != '\n')
			return "expected new-line after carriage-return";
	}
	if (ch == '\n')
		return nonl(ch, "unexpected new-line after maximum variable",
					lineno_ptr);
	if (ch != ' ')
		return "expected space after maximum variable";
	ch = NEXT();
    while (ch == ' ' || ch == '\t')
		ch = NEXT();
	if (!isdigit(ch))
		return "expected number of clauses after maximum variable";
	uint64_t clauses = ch - '0';
	while (isdigit(ch = NEXT()))
	{
		if (UINT64_MAX / 10 < clauses)
			return "number of clauses too large";
		clauses *= 10;
		const int digit = ch - '0';
		if (UINT64_MAX - digit < clauses)
			return "number of clauses too large";
		clauses += digit;
	}
	simplify_alloc(S, variables, clauses);
	if (ch == EOF)
		return "unexpected end-of-file while parsing number of clauses";
    while (ch == ' ' || ch == '\t')
		ch = NEXT();
	if (ch == '\r')
	{
		ch = NEXT();
		if (ch != '\n')
			return "expected new-line after carriage-return";
	}
	if (ch == EOF)
		return "unexpected end-of-file after parsing number of clauses";
	if (ch != '\n')
		return "expected new-line after parsing number of clauses";
        
	uint64_t parsed = 0;
	int lit = 0;
	for (;;)
	{
		ch = NEXT();
		if (ch == ' ')
			continue;
		if (ch == '\t')
			continue;
		if (ch == '\n')
			continue;
		if (ch == '\r')
		{
			ch = NEXT();
			if (ch != '\n')
				return "expected new-line after carriage-return";
			continue;
		}
		if (ch == 'c')
		{
			while ((ch = NEXT()) != '\n')
				if (ch == EOF)
					break;
			if (ch == EOF)
				break;
			continue;
		}
		if (ch == EOF)
			break;
		int sign;
		if (ch == '-')
		{
			ch = NEXT();
			if (ch == EOF)
				return "unexpected end-of-file after '-'";
			if (ch == '\n')
				return nonl(ch, "unexpected new-line after '-'", lineno_ptr);
			if (!isdigit(ch))
				return "expected digit after '-'";
			if (ch == '0')
				return "expected non-zero digit after '-'";
			sign = -1;
		}
		else if (!isdigit(ch))
			return "expected digit or '-'";
		else
			sign = 1;
		assert(isdigit(ch));
		int idx = ch - '0';
		while (isdigit(ch = NEXT()))
		{
			if (EXTERNAL_MAX_VAR / 10 < idx)
				return "variable index too large";
			idx *= 10;
			const int digit = ch - '0';
			if (EXTERNAL_MAX_VAR - digit < idx)
				return "variable index too large";
			idx += digit;
		}
		if (ch == EOF)
		{
		}
		else if (ch == '\r')
		{
			ch = NEXT();
			if (ch != '\n')
				return "expected new-line after carriage-return";
		}
		else if (ch == 'c')
		{
			while ((ch = NEXT()) != '\n')
				if (ch == EOF) break;

		}
		else if (ch != ' ' && ch != '\t' && ch != '\n')
			return "expected white space after literal";
		if (idx > variables)
			return nonl(ch, "maximum variable index exceeded ", lineno_ptr);
		if (idx)
		{
			assert(sign == 1 || sign == -1);
			assert(idx != INT_MIN);
			lit = sign * idx;
		}
		else
		{
			if (parsed == clauses)
				return "too many clauses ";
			parsed++;
			lit = 0;
		}
		// kissat_add(solver, lit);
        int res = simplify_store_clause(S, lit);
        if (!res) return "empty clause";
	}
	if (lit)
		return "trailing zero missing";
	if (parsed < clauses)
	{
		if (parsed + 1 == clauses)
			return "one clause missing ";
		return "more than one clause missing ";
	}
	return 0;
}

inline int pnsign(int x) {
    return (x > 0 ? 1 : -1);
}
inline int sign(int x) {
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
inline ll mapv(int a, int b) {
    return 1ll * a * nlit + (ll)b;
}

void update_var_clause_label(simplify *S) {
    int remain_var = 0;
    for (int i = 1; i <= S->vars; i++) S->color[i] = 0;
    for (int i = 1; i <= S->clauses; i++) {
        if (S->clause_delete[i]) continue;
        int l = S->clause_size[i];
        for (int j = 0; j < l; j++) {
            if (S->color[abs(S->clause[i][j])] == 0) S->color[abs(S->clause[i][j])] = ++remain_var;       
        }
    }
    int id = 0;
    for (int i = 1; i <= S->clauses; i++) {
        if (S->clause_delete[i]) continue;
        ++id;
        int l = S->clause_size[i];
        if (i == id) {
            for (int j = 0; j < l; j++)
                S->clause[id][j] = S->color[abs(S->clause[i][j])] * pnsign(S->clause[i][j]);    
            continue;
        }
        if (l != S->clause_size[id]) {
            S->clause[id] = (int*) realloc(S->clause[id], sizeof(int) * l);
        }
        S->clause_size[id] = 0;
        for (int j = 0; j < l; j++) 
            S->clause[id][S->clause_size[id]++] = S->color[abs(S->clause[i][j])] * pnsign(S->clause[i][j]);;
    }
    // printf("c After simplify: S->vars: %d -> %d , S->clauses: %d -> %d ,\n", S->vars, remain_var, S->clauses, id);
    for (int i = id + 1; i <= S->clauses; i++) 
        free(S->clause[i]);
    for (int i = remain_var + 1; i <= S->vars; i++) {
        if (S->occurp[i] != NULL) free(S->occurp[i]);
        if (S->occurn[i] != NULL) free(S->occurn[i]);
    }
    S->vars = remain_var, S->clauses = id;
}

bool res_is_empty(simplify *S, int x) {
    int op = S->occurp_size[x], on = S->occurn_size[x];
    for (int i = 0; i < op; i++) {
        int o1 = S->occurp[x][i], l1 = S->clause_size[o1];
        if (S->clause_delete[o1]) continue;
        for (int j = 0; j < l1; j++)
            if (abs(S->clause[o1][j]) != x) S->resseen[abs(S->clause[o1][j])] = pnsign(S->clause[o1][j]);
        for (int j = 0; j < on; j++) {
            int o2 = S->occurn[x][j], l2 = S->clause_size[o2], flag = 0;
            if (S->clause_delete[o2]) continue;
            for (int k = 0; k < l2; k++)
                if (abs(S->clause[o2][k]) != x && S->resseen[abs(S->clause[o2][k])] == -pnsign(S->clause[o2][k])) {
                    flag = 1; break;
                }
            if (!flag) {
                for (int j = 0; j < l1; j++)
                    S->resseen[abs(S->clause[o1][j])] = 0;
                return false;
            }
        }
        for (int j = 0; j < l1; j++)
            S->resseen[abs(S->clause[o1][j])] = 0;
    }
    return true; 
}

bool simplify_resolution(simplify *S) {
    for (int i = 1; i <= S->vars; i++) {
        S->occurn_size[i] = 0;
        S->occurp_size[i] = 0;
        S->resseen[i] = S->resseen[i + S->vars] = S->clean[i] = 0;
    }
    for (int i = 1; i <= S->clauses; i++) {
        int l = S->clause_size[i];
        S->clause_delete[i] = 0;
        for (int j = 0; j < l; j++)
            if (S->clause[i][j] > 0) S->occurp_size[S->clause[i][j]]++;
            else S->occurn_size[-S->clause[i][j]]++;
    }
    for (int i = 1; i <= S->vars; i++) {
        if (S->occurp_size[i])
            S->occurp[i] = (int*)realloc(S->occurp[i], sizeof(int) * S->occurp_size[i]);
        if (S->occurn_size[i])
            S->occurn[i] = (int*)realloc(S->occurn[i], sizeof(int) * S->occurn_size[i]);
        S->occurp_size[i] = S->occurn_size[i] = 0;
    }
    for (int i = 1; i <= S->clauses; i++) {
        for (int j = 0; j < S->clause_size[i]; j++) {
            int v = S->clause[i][j];
            if (v > 0) S->occurp[v][S->occurp_size[v]++] = i;
            else S->occurn[-v][S->occurn_size[-v]++] = i;
        }
    }
    for (int i = 1; i <= S->vars; i++)
        if (S->occurn_size[i] == 0 && S->occurp_size[i] == 0) S->clean[i] = S->seen[i] = 1;  

    int l = 1, r = 0;         
    for (int i = 1; i <= S->vars; i++) {
        int op = S->occurp_size[i], on = S->occurn_size[i];
        if (op * on > op + on || S->clean[i]) continue;
        if (res_is_empty(S, i)) {
            S->queue[++r] = i, S->clean[i] = 1;
        }
    }

    int now_turn = 0, seen_flag = 0, vars_sz = 0;
    int *vars = (int*)malloc(sizeof(int)*S->vars);
    while (l <= r) {
        ++now_turn;
        for (int j = l; j <= r; j++) {
            int i = S->queue[j];
            int op = S->occurp_size[i], on = S->occurn_size[i];
            for (int j = 0; j < op; j++) S->clause_delete[S->occurp[i][j]] = 1;
            for (int j = 0; j < on; j++) S->clause_delete[S->occurn[i][j]] = 1;
        }
        int ll = l; l = r + 1;
        
        vars_sz = 0;
        ++seen_flag;
        for (int u = ll; u <= r; u++) {
            int i = S->queue[u];
            int op = S->occurp_size[i], on = S->occurn_size[i];
            for (int j = 0; j < op; j++) {
                int o = S->occurp[i][j], l = S->clause_size[o];
                for (int k = 0; k < l; k++) {
                    int v = abs(S->clause[o][k]);
                    if (!S->clean[v] && S->seen[v] != seen_flag)
                        vars[vars_sz++] = v, S->seen[v] = seen_flag;
                }
            }
            for (int j = 0; j < on; j++) {
                int o = S->occurn[i][j], l = S->clause_size[o];
                for (int k = 0; k < l; k++) {
                    int v = abs(S->clause[o][k]);
                    if (!S->clean[v] && S->seen[v] != seen_flag)
                        vars[vars_sz++] = v, S->seen[v] = seen_flag;
                }
            }
        }
        for (int u = 0; u < vars_sz; u++) {
            int i = vars[u];
            int op = 0, on = 0;
            for (int j = 0; j < S->occurp_size[i]; j++) op += 1 - S->clause_delete[S->occurp[i][j]];
            for (int j = 0; j < S->occurn_size[i]; j++) on += 1 - S->clause_delete[S->occurn[i][j]];
            if (op * on > op + on) continue;
            if (res_is_empty(S, i)) {
                S->queue[++r] = i, S->clean[i] = 1;
            }
        }
    }
    S->res_clauses = 0;
    S->resolutions = r;
    if (r) {
        for (int i = 1; i <= S->clauses; i++) {
            if (S->clause_delete[i]) S->res_clauses++;
        }
	    S->res_clause = (int**)malloc(sizeof(int*)*(S->res_clauses+1));
	    S->res_clause_size = (int*)malloc(sizeof(int)*(S->res_clauses+1));
        int id = 0;
        for (int i = 1; i <= S->clauses; i++) {
            if (!S->clause_delete[i]) continue;
            int l = S->clause_size[i];
            S->res_clause_size[++id] = l;
            S->res_clause[id] = (int*)malloc(sizeof(int)*l);
            for (int j = 0; j < l; j++)
                S->res_clause[id][j] = pnsign(S->clause[i][j]) * S->mapfrom[abs(S->clause[i][j])];
        }
        S->resolution = (int*)malloc(sizeof(int)*(r+1));
        update_var_clause_label(S);
        for (int i = 1; i <= r; i++) {
            int v = S->mapfrom[S->queue[i]];
            S->resolution[i] = v;
            if (!v) puts("c wrong mapfrom");
            S->mapto[v] = 0, S->mapval[v] = -10;
        }
        for (int i = 1; i <= S->orivars; i++) {
            if (S->mapto[i]) {
                if (!S->color[S->mapto[i]]) puts("c wrong color");
                S->mapto[i] = S->color[S->mapto[i]];
            }
        }
    }
    free(vars);
    return true;
}

bool simplify_easy_clause(simplify *S) {
    for (int i = 1; i <= S->vars; i++) {
        S->varval[i] = 0;
        S->occurp_size[i] = 0;
        S->occurn_size[i] = 0;
        S->occurn[i] = S->occurp[i] = NULL;
        S->resseen[i] = S->resseen[i + S->vars] = 0;
    }
    for (int i = 1; i <= S->clauses; i++) S->clause_delete[i] = 0;
    int head = 1, tail = 0;
    for (int i = 1; i <= S->clauses; i++) {
        int l = S->clause_size[i], t = 0;
        for (int j = 0; j < l; j++) {
            int lit = TOLIT(S->clause[i][j]);
            if (S->resseen[lit] == i) continue;
            if (S->resseen[NEG(lit)] == i) {S->clause_delete[i] = 1; break;}
            S->clause[i][t++] = S->clause[i][j];
            S->resseen[lit] = i;
        }
        if (S->clause_delete[i]) continue;
        S->clause_size[i] = t;
        for (int j = 0; j < t; j++)
            if (S->clause[i][j] > 0) S->occurp_size[S->clause[i][j]]++;
            else S->occurn_size[-S->clause[i][j]]++;
        if (t == 0) return false;
        if (t == 1) {
            int lit = S->clause[i][0];
            S->clause_delete[i] = 1;
            if (S->varval[abs(lit)]) {
                if (S->varval[abs(lit)] == pnsign(lit)) continue;
                else return false;
            }
            S->varval[abs(lit)] = pnsign(lit); 
            S->queue[++tail] = abs(lit); 
        }
    }
    for (int i = 1; i <= S->vars; i++) {
        if (S->occurp_size[i])
			S->occurp[i] = (int*)malloc(sizeof(int)*(S->occurp_size[i]));
        if (S->occurn_size[i])
			S->occurn[i] = (int*)malloc(sizeof(int)*(S->occurn_size[i]));
        S->occurp_size[i] = S->occurn_size[i] = 0;
    }
    for (int i = 1; i <= S->clauses; i++) {
        if (S->clause_delete[i]) continue;
        for (int j = 0; j < S->clause_size[i]; j++) {
            int v = S->clause[i][j];
            if (v > 0) S->occurp[v][S->occurp_size[v]++] = i;
            else S->occurn[-v][S->occurn_size[-v]++] = i;
        }
    }
    for (int i = 1; i <= S->vars + S->vars; i++) S->resseen[i] = 0;
    while (head <= tail) {
        int x = S->queue[head++];
        if (S->varval[x] == 1) {
            for (int i = 0; i < S->occurp_size[x]; i++)
                S->clause_delete[S->occurp[x][i]] = 1;
            for (int i = 0; i < S->occurn_size[x]; i++) {
                int o = S->occurn[x][i], t = 0;
                if (S->clause_delete[o]) continue;
                for (int j = 0; j < S->clause_size[o]; j++) {
                    if (S->varval[abs(S->clause[o][j])] == pnsign(S->clause[o][j])) {
                        S->clause_delete[o] = 1; break;
                    }
                    if (S->varval[abs(S->clause[o][j])] == -pnsign(S->clause[o][j])) continue;
                    S->clause[o][t++] = S->clause[o][j];
                }
                if (S->clause_delete[o]) continue;
                S->clause_size[o] = t;
                if (t == 0) return false;
                if (t == 1) {
                    int lit = S->clause[o][0];
                    S->clause_delete[o] = 1;
                    if (S->varval[abs(lit)]) {
                        if (S->varval[abs(lit)] == pnsign(lit)) continue;
                        else return false;
                    }
                    S->varval[abs(lit)] = pnsign(lit); 
                    S->queue[++tail] = abs(lit); 
                }
            }
        }
        else {
            for (int i = 0; i < S->occurn_size[x]; i++)
                S->clause_delete[S->occurn[x][i]] = 1;
            for (int i = 0; i < S->occurp_size[x]; i++) {
                int o = S->occurp[x][i], t = 0;
                if (S->clause_delete[o]) continue;
                for (int j = 0; j < S->clause_size[o]; j++) {
                    if (S->varval[abs(S->clause[o][j])] == pnsign(S->clause[o][j])) {
                        S->clause_delete[o] = 1; break;
                    }
                    if (S->varval[abs(S->clause[o][j])] == -pnsign(S->clause[o][j])) continue;
                    S->clause[o][t++] = S->clause[o][j];
                }
                if (S->clause_delete[o]) continue;
                S->clause_size[o] = t;
                if (t == 0) return false;
                if (t == 1) {
                    int lit = S->clause[o][0];
                    S->clause_delete[o] = 1;
                    if (S->varval[abs(lit)]) {
                        if (S->varval[abs(lit)] == pnsign(lit)) continue;
                        else return false;
                    }
                    S->varval[abs(lit)] = pnsign(lit); 
                    S->queue[++tail] = abs(lit); 
                }
            }
        }
    }
    update_var_clause_label(S);
    
    for (int i = 1; i <= tail; i++) {
        int v = S->queue[i];
        S->mapval[v] = S->varval[v];
        if (S->color[v]) puts("c wrong unit");
    }
    S->mapfrom = (int*)malloc(sizeof(int)*(S->vars+1));
    for (int i = 1; i <= S->vars; i++) S->mapfrom[i] = 0;
    for (int i = 1; i <= S->orivars; i++) {
        if (S->color[i])
            S->mapto[i] = S->color[i], S->mapfrom[S->color[i]] = i;
        else if (!S->mapval[i]) // not in unit queue, then it is no use var
            S->mapto[i] = 0, S->mapval[i] = 1;
        else 
            S->mapto[i] = 0;
    }
    return true;
}

simplify *S;
int search_almost_one(simplify *S) {
    HashMap *H = map_init(1000007);
    nlit = 2 * S->vars + 2;
	int **occur = (int**)malloc(sizeof(int*)*(nlit));
    int *occur_size = (int*)malloc(sizeof(int)*(nlit));
    for (int i = 0; i < nlit; i++) {
        occur[i] = NULL;
        occur_size[i] = 0;
    }
    for (int i = 1; i <= S->clauses; i++) {
        S->clause_delete[i] = 0;
        if (S->clause_size[i] != 2) continue;
        int x = tolit(S->clause[i][0]);
        int y = tolit(S->clause[i][1]);
        ll id1 = mapv(x, y);
        ll id2 = mapv(y, x);
        map_insert(H, id1, i);
        map_insert(H, id2, i);
        occur_size[x]++;
        occur_size[y]++;
    }
    for (int i = 2; i < nlit; i++) {
        if (occur_size[i])
            occur[i] = (int*)malloc(sizeof(int)*(occur_size[i]));
        occur_size[i] = S->seen[i] = 0;
    }
    for (int i = 1; i <= S->clauses; i++) {
        if (S->clause_size[i] != 2) continue;
        int x = tolit(S->clause[i][0]);
        int y = tolit(S->clause[i][1]);
        occur[x][occur_size[x]++] = y;
        occur[y][occur_size[y]++] = x;        
    }
    S->cards = 0;
    cvec *nei = cvec_init();
    cvec *ino = cvec_init();
    for (int i = 2; i <= S->vars * 2 + 1; i++) {
        if (S->seen[i] || !occur_size[i]) continue;
        S->seen[i] = 1;
        cvec_clear(nei);
        for (int j = 0; j < occur_size[i]; j++)
            if (!S->seen[occur[i][j]])
                cvec_push(nei, occur[i][j]);
        do {
            cvec_clear(ino);
            cvec_push(ino, i);
            for (int j = 0; j < nei->sz; j++) {
                int v = cvec_data(nei, j), flag = 1;
                for (int k = 0; k < ino->sz; k++) {
                    ll id = mapv(v, cvec_data(ino, k));
                    int d1 = map_get(H, id, 0);
                    if (!d1) {flag = 0; break;}
                    S->queue[k] = d1;
                }
                if (flag) {
                    for (int k = 0; k < ino->sz; k++) {
                        S->clause_delete[S->queue[k]] = 1;
                        ll id1 = mapv(v, cvec_data(ino, k)), id2 = mapv(cvec_data(ino, k), v);
                        map_delete(H, id1);
                        map_delete(H, id2);
                    }
                    cvec_push(ino, v);
                }
            }
            if (ino->sz >= 2) {
                S->card_one[S->cards] = (int*)malloc(sizeof(int)*(ino->sz));
                S->card_one_size[S->cards] = 0;
                for (int j = 0; j < ino->sz; j++) {
                    S->card_one[S->cards][S->card_one_size[S->cards]++] = -toidx(cvec_data(ino, j));
                }
                S->cards++;
                if (S->cards >= S->M_card) {
                    cvec_release(ino);
                    cvec_release(nei);
                    map_free(H);        
                    free(occur_size);
                    for (int i = 0; i < nlit; i++)
                        if (occur[i] != NULL) free(occur[i]);
                    free(occur);
                    return 0;
                }
                // printf("c catch constrain: ");
                // for (int j = 0; j < ino.size(); j++) printf("%d ", toidx(ino[j]));
                // puts("");
            }
        } while (ino->sz != 1);
    }
    cvec_release(ino);
    cvec_release(nei);
    map_free(H);        
    free(occur_size);
    for (int i = 0; i < nlit; i++) {
        if (occur[i] != NULL) free(occur[i]);
    }
    free(occur);
    return S->cards;
}

void upd_occur(simplify *S, int v, int s) {
    int x = abs(v);
    int t = 0;
    if (v > 0) {
        for (int j = 0; j < S->occurp_size[x]; j++)
            if (S->occurp[x][j] != s) S->occurp[x][t++] = S->occurp[x][j]; 
        S->occurp_size[x] = t;
    }
    else {
        for (int j = 0; j < S->occurn_size[x]; j++)
            if (S->occurn[x][j] != s) S->occurn[x][t++] = S->occurn[x][j];
        S->occurn_size[x] = t;
    }
}

int scc_almost_one(simplify *S) {
    for (int i = 1; i <= S->vars; i++) {
        S->occurp_size[i] = 0;
        S->occurn_size[i] = 0;
        S->occurp[i] = (int*)realloc(S->occurp[i], sizeof(int) * S->M_card);
        S->occurn[i] = (int*)realloc(S->occurn[i], sizeof(int) * S->M_card);
    }
    for (int i = 0; i < S->cards; i++) {
        S->cdel[i] = 0;
        for (int j = 0; j < S->card_one_size[i]; j++) {
            int v = S->card_one[i][j];
            if (v > 0)
                S->occurp[v][S->occurp_size[v]++] = i;
            else 
                S->occurn[-v][S->occurn_size[-v]++] = i;
        }
    }

    int flag = 1;
    do {
        flag = 0;
        for (int i = 1; i <= S->vars; i++) {
            if (!S->occurp_size[i] || !S->occurn_size[i]) continue;
            if (S->cards + S->occurp_size[i] * S->occurn_size[i] >= S->M_card) return 0;
            flag = 1;
            for (int ip = 0; ip < S->occurp_size[i]; ip++) 
                S->cdel[S->occurp[i][ip]] = 1;
            for (int in = 0; in < S->occurn_size[i]; in++) 
                S->cdel[S->occurn[i][in]] = 1;
            for (int ip = 0; ip < S->occurp_size[i]; ip++) {
                int op = S->occurp[i][ip];
                for (int in = 0; in < S->occurn_size[i]; in++) {
                    int on = S->occurn[i][in];
                    S->card_one[S->cards] = (int*)malloc(sizeof(int)*(S->card_one_size[op] + S->card_one_size[on] - 2));
                    S->card_one_size[S->cards] = 0;
                    S->cdel[S->cards] = 0;

                    int find = 0;
                    for (int j = 0; j < S->card_one_size[op]; j++) {
                        int v = S->card_one[op][j];
                        if (abs(v) == i && !find) continue;
                        if (abs(v) == i) find = 1;
                        S->card_one[S->cards][S->card_one_size[S->cards]++] = v;
                        if (v > 0) {
                            if (S->occurp_size[v] && S->occurp[v][S->occurp_size[v] - 1] != S->cards)
                                S->occurp[v][S->occurp_size[v]++] = S->cards;
                        }
                        else {
                            if (S->occurn_size[-v] && S->occurn[-v][S->occurn_size[-v] - 1] != S->cards)
                                S->occurn[-v][S->occurn_size[-v]++] = S->cards;
                        }
                    }
                    find = 0;
                    for (int j = 0; j < S->card_one_size[on]; j++) {
                        int v = S->card_one[on][j];
                        if (abs(v) == i && !find) continue;
                        if (abs(v) == i) find = 1;
                        S->card_one[S->cards][S->card_one_size[S->cards]++] = v;
                        if (v > 0) {
                            if (S->occurp_size[v] && S->occurp[v][S->occurp_size[v] - 1] != S->cards)
                                S->occurp[v][S->occurp_size[v]++] = S->cards;
                        }
                        else {
                            if (S->occurn_size[-v] && S->occurn[-v][S->occurn_size[-v] - 1] != S->cards)
                                S->occurn[-v][S->occurn_size[-v]++] = S->cards;
                        }
                    }
                    ++S->cards;
                }
            }
            for (int ip = 0; ip < S->occurp_size[i]; ip++) {
                int op = S->occurp[i][ip];
                for (int j = 0; j < S->card_one_size[op]; j++)
                    upd_occur(S, S->card_one[op][j], op);
            }
            
            for (int in = 0; in < S->occurn_size[i]; in++) {
                int on = S->occurn[i][in];
                for (int j = 0; j < S->card_one_size[on]; j++)
                    upd_occur(S, S->card_one[on][j], on);
            }
        }       
    } while(flag);

    int t = 0;
    for (int i = 0 ; i < S->cards; i++) {
        if (S->cdel[i]) continue;
        ++t;
        // if (S->card_one_size[i] >= 2) {
        //     printf("c catch constrain: ");
        //     for (int j = 0; j < S->card_one_size[i]; j++) printf("%d ", S->card_one[i][j]);
        //     puts("");
        // }
    }
    return t;
}

int check_card(simplify *S, int id) { //0: wrong  -1:useless    1:normal
    int ps = 0, ns = 0, t = -1;
    double poss = 0, negs = 0;
    for (int j = 1; j <= S->vars; j++) {
        if (fabs(S->mat[id][j]) < 1e-6) continue;
        t = j;
        if (S->mat[id][j] > 0) ++ps, poss += S->mat[id][j];
        if (S->mat[id][j] < 0) ++ns, negs += S->mat[id][j];
    }
    if (ns + ps == 1) {
        double r = S->mat[id][0] / S->mat[id][t];
        if (ps) {
            if (fabs(r) < 1e-6)
            {
                // printf("c [CE] get unit: %d = 0\n", t);
            }else if (r < 0) {
                // printf("c [CE] get wrong: %d < 0\n", t);
                return 0;
            }
            return -1;
        }
        if (ns) {
            if (fabs(r - 1) < 1e-6){
                // printf("c [CE] get unit: %d = 1\n", t);
            }else if (r > 1) {
                // printf("c [CE] get wrong: %d > 1\n", t);
                return 0;
            }
            return -1;
        }
    }
    if (ns + ps == 0) {
        if (S->mat[id][0] < -(1e-6)) {
            // printf("c [CE] get empty wrong clause: 0 < %.3lf\n", S->mat[id][0]);
            return 0;
        }
        return -1;   
    }
    if (poss <= S->mat[id][0]) {
        return -1;
    }
    if (negs >= S->mat[id][0]) {
        if (negs == S->mat[id][0]) {
            //unit
        }
        else return 0;
    }
    if (S->mat[id][0] == 0) {
        if (ps == 0) {
            return -1;
        }
        else if (ns == 0) {
            //unit
        }
    }
    return 1;
}

int card_elimination(simplify *S) {
    //sigma aixi <= b
    S->mat = (double**)malloc(sizeof(double*)*(S->M_card));
    S->mats = 0;
    int *row_size = (int*)malloc(sizeof(int)*(S->M_card));
    for (int i = 0; i < S->cards; i++) {
        if (S->cdel[i]) continue;
        int b = 1;
        row_size[S->mats] = S->card_one_size[i];
        S->mat[S->mats] = (double*)malloc(sizeof(double)*(S->vars + 1));
        for (int i = 0; i <= S->vars; i++)
            S->mat[S->mats][i] = 0;
        for (int j = 0; j < S->card_one_size[i]; j++) {
            if (S->card_one[i][j] < 0) b--;
            S->mat[S->mats][abs(S->card_one[i][j])] += pnsign(S->card_one[i][j]);
        }
        S->mat[S->mats][0] = b;
        ++S->mats;
    }
    for (int i = 0; i < S->cards; i++)
        free(S->card_one[i]);
    free(S->card_one);
    free(S->card_one_size);
    free(S->cdel);

    for (int i = 1; i <= S->clauses; i++) {
        if (S->clause_delete[i]) continue;
        int b = 1;
        for (int j = 0; j < S->clause_size[i]; j++)
            if (S->clause[i][j] < 0) b--;
        //convert >= to <=
        row_size[S->mats] = S->clause_size[i];
        S->mat[S->mats] = (double*)malloc(sizeof(double)*(S->vars + 1));
        for (int i = 0; i <= S->vars; i++)
            S->mat[S->mats][i] = 0;
        for (int j = 0; j < S->clause_size[i]; j++) {
            S->mat[S->mats][abs(S->clause[i][j])] += -pnsign(S->clause[i][j]);
        }
        S->mat[S->mats][0] = -b;
        ++S->mats;
    }
    
    int *low = (int*)malloc(sizeof(int)*(S->M_card));
    int *upp = (int*)malloc(sizeof(int)*(S->M_card));
    int *mat_del = (int*)malloc(sizeof(int)*(S->M_card));

    
    int *var_score1 = (int*)malloc(sizeof(int)*(S->vars + 1));
    int *var_score2 = (int*)malloc(sizeof(int)*(S->vars + 1));
    int *elim = (int*)malloc(sizeof(int)*(S->vars + 1));
    
    for (int i = 0; i < S->mats; i++) mat_del[i] = 0;
    for (int v = 1; v <= S->vars; v++) {
        var_score1[v] = var_score2[v] = elim[v] = 0;
        int lows = 0, upps = 0;
        for (int i = 0; i < S->mats; i++) {
            if (fabs(S->mat[i][v]) < 1e-6) continue;
            if (S->mat[i][v] > 0) 
                upp[upps++] = i;
            else
                low[lows++] = i;
        }
        var_score1[v] = upps * lows;
        for (int i = 0; i < upps; i++)
            for (int j = 0; j < lows; j++) 
                var_score2[v] += row_size[upp[i]] * row_size[low[j]];
    }
    for (int turn = 1; turn <= S->vars; turn++) {
        int v = 0;
        for (int i = 1; i <= S->vars; i++) {
            if (elim[i]) continue;
            if (!v) v = i;
            else {
                if (var_score1[i] < var_score1[v]) v = i;
                else if (var_score1[i] == var_score1[v] && var_score2[i] < var_score2[v])
                    v = i;
            }
        }
        elim[v] = 1;
        int l = 0, u = 0;
        for (int i = 0; i < S->mats; i++) {
            if (mat_del[i]) continue;
            if (fabs(S->mat[i][2792]) < 1e-6) continue;
            if (S->mat[i][2792] > 0) { 
                u++;
            }
            else {
                l++;
            }
        }
        //elimination v
        int lows = 0, upps = 0;
        // if (turn == 1) {
        //     printf("pick %d\n", v);
        //     for (int i = 0; i < S->mats; i++) {
        //         if (mat_del[i]) continue;
        //         printf("%d:\t", i);
        //         for (int j = 1; j <= S->vars; j++)
        //             if (fabs(S->mat[i][j])>1e-6) printf("%.2lf*%d + ", S->mat[i][j], j);
        //         printf("<= %.2lf\n", S->mat[i][0]);
        //     }
        //     puts("");
        // }
        for (int i = 0; i < S->mats; i++) {
            if (mat_del[i]) continue;
            if (fabs(S->mat[i][v]) < 1e-6) continue;
            mat_del[i] = 1;
            if (S->mat[i][v] > 0) { 
                upp[upps++] = i;
            }
            else {
                low[lows++] = i;
            }
        }
        if (S->mats + upps * lows >= S->M_card || S->mats > 1e3) break;
        for (int iu = 0; iu < upps; iu++) {
            int u = upp[iu];
            for (int il = 0; il < lows; il++) {
                int l = low[il];
                mat_del[S->mats] = 0;
                S->mat[S->mats] = (double*)malloc(sizeof(double)*(S->vars + 1));
                for (int i = 0; i <= S->vars; i++) S->mat[S->mats][i] = 0;
                for (int j = 0; j <= S->vars; j++)
                    S->mat[S->mats][j] = S->mat[u][j] / S->mat[u][v] + S->mat[l][j] / (-S->mat[l][v]);
                ++S->mats;
                
                //check can get ?
                int check_res = check_card(S, S->mats - 1);
                if (check_res == 0) {
                    free(row_size);
                    free(mat_del);
                    free(low);
                    free(upp);
                    free(var_score1);
                    free(var_score2);
                    free(elim);
                    return 0;
                }
                if (check_res == -1) {
                    free(S->mat[S->mats - 1]);
                    S->mats--;
                }
            }
        }
    }
    free(row_size);
    free(mat_del);
    free(low);
    free(upp);
    free(var_score1);
    free(var_score2);
    free(elim);
    return 1;
}

int simplify_card(simplify *S) {

    S->M_card = 1e7 / S->vars;
	S->card_one = (int**)malloc(sizeof(int*)*(S->M_card));
	S->card_one_size = (int*)malloc(sizeof(int)*(S->M_card));
    S->cdel = (int*)malloc(sizeof(int)*(S->M_card));
    
    int sone = search_almost_one(S);
    // printf("c [CE] almost one cons: %d\n", sone);
    if (!sone) {
        for (int i = 0; i < S->cards; i++)
            free(S->card_one[i]);
        free(S->card_one);
        free(S->card_one_size);
        free(S->cdel);
        return 1;
    }

    int scc = scc_almost_one(S);
    // printf("c [CE] scc cons: %d\n", scc);
    if (!scc) {
        for (int i = 0; i < S->cards; i++)
            free(S->card_one[i]);
        free(S->card_one);
        free(S->card_one_size);
        free(S->cdel);
        return 1;
    }

    int sz = S->cards;
    for (int i = 1; i <= S->clauses; i++)
        if (!S->clause_delete[i]) ++sz;
        
    if (sz >= S->M_card || sz > 1e3) {
        for (int i = 0; i < S->cards; i++)
            free(S->card_one[i]);
        free(S->card_one);
        free(S->card_one_size);
        free(S->cdel);
        return 1;
    }

    int res = card_elimination(S);
    for (int i = 0; i < S->mats; i++)
        free(S->mat[i]);
    free(S->mat);
    return res;
}


bool kissat_simplify(kissat *solver, int *maxvar, file *file) {
    S = simplify_init();
	uint64_t lineno_ptr;
    const char *error = simplify_parse(S, file, &lineno_ptr);
    // printf("c vars: %d, clauses: %d\n", S->vars, S->clauses);
    solver->mapidx = (int*)malloc(sizeof(int)*(S->orivars + 1));
    for (int i = 1; i <= S->orivars; i++) 
        solver->mapidx[i] = i;

    int res = simplify_easy_clause(S);
    if (!res) {
        simplify_release(S);
        free(S->mapto);
        free(S->mapval);
        free(S);
        return false;
    }
  
    if (S->vars<=1e5 && S->clauses <= 1e6) {
        int res = simplify_card(S);
        if (!res) {
            simplify_release(S);
            free(S->mapto);
            free(S->mapval);
            free(S);
            return false;
        }
    }

    res = simplify_resolution(S);
    if (!res) {
        simplify_release(S);
        free(S->mapto);
        free(S->mapval);
        free(S->res_clause_size);
        for (int i = 1; i <= S->res_clauses; i++)
            free(S->res_clause[i]);
        free(S->res_clause);
        free(S->resolution);
        free(S);
        return false;
    }
    
    // printf("c vars: %d, clauses: %d\n", S->vars, S->clauses);

    solver->mapidx = (int*)realloc(solver->mapidx, sizeof(int) * (S->vars + 1));
    for (int i = 1; i <= S->vars; i++)
        solver->mapidx[i] = 0;
    for (int i = 1; i <= S->orivars; i++)
        if (S->mapto[i]) {
            // if (solver->mapidx[S->mapto[i]] != 0 || S->mapto[i] < 0) printf("c wrong mapidx %d %d %d\n", i, S->mapto[i], solver->mapidx[S->mapto[i]]);
            solver->mapidx[S->mapto[i]] = i;
        }

	*maxvar = S->vars;
	
	kissat_reserve(solver, S->vars);
	for (int i = 1; i <= S->clauses; i++) {
		for (int j = 0; j < S->clause_size[i]; j++) {
			kissat_add(solver, S->clause[i][j]);
		}
		kissat_add(solver, 0);
	}
    simplify_release(S);
    return true;
}

static void
flush_buffer(chars *buffer)
{
  fputs("v", stdout);
  for (all_stack(char, ch, *buffer))
    fputc(ch, stdout);
  fputc('\n', stdout);
  CLEAR_STACK(*buffer);
}

static void
print_int(kissat *solver, chars *buffer, int i)
{
  char tmp[16];
  sprintf(tmp, " %d", i);
  size_t tmp_len = strlen(tmp);
  size_t buf_len = SIZE_STACK(*buffer);
  if (buf_len + tmp_len > 77)
    flush_buffer(buffer);
  for (const char *p = tmp; *p; p++)
    PUSH_STACK(*buffer, *p);
}

void kissat_complete_val(kissat *solver) {
    int r = 0;
    for (int i = 1; i <= S->orivars; i++) {
        if (S->mapto[i]) S->mapval[i] = pnsign(S->mapto[i]) * solver->last_val[abs(S->mapto[i])];
        else {
            if (!S->mapval[i]) puts("c wrong empty val");
            else if (abs(S->mapval[i]) != 1) S->mapval[i] = 0, ++r;
        }
    }
    if (r != S->resolutions) puts("c wrong resolution num");
    if (r) {
        S->occurp = (int**)malloc(sizeof(int*)*(S->orivars+1));
        S->occurn = (int**)malloc(sizeof(int*)*(S->orivars+1));
        S->occurp_size = (int*)malloc(sizeof(int)*(S->orivars+1));
        S->occurn_size = (int*)malloc(sizeof(int)*(S->orivars+1));
        for (int i = 1; i <= S->orivars; i++) {
            S->occurp_size[i] = S->occurn_size[i] = 0;
            S->occurp[i] = S->occurn[i] = NULL;
        }
        for (int i = 1; i <= S->res_clauses; i++) {
            for (int j = 0; j < S->res_clause_size[i]; j++) {
                int v = S->res_clause[i][j];
                if (v > 0) S->occurp_size[v]++;
                else S->occurn_size[-v]++;
            }
        }
        for (int i = 1; i <= S->orivars; i++) {
            if (S->occurp_size[i])
                S->occurp[i] = (int*)malloc(sizeof(int)*(S->occurp_size[i]));
            if (S->occurn_size[i])
                S->occurn[i] = (int*)malloc(sizeof(int)*(S->occurn_size[i]));
            S->occurp_size[i] = S->occurn_size[i] = 0;
        }
        S->clause_state = (int*)malloc(sizeof(int)*(S->res_clauses+1));
        for (int i = 1; i <= S->res_clauses; i++) {
            S->clause_state[i] = 0;
            int satisify = 0;
            for (int j = 0; j < S->res_clause_size[i]; j++) {
                int v = S->res_clause[i][j];
                if (abs(v) > S->orivars || v == 0) puts("c wrong idx");
                if (v > 0) S->occurp[v][S->occurp_size[v]++] = i;
                else S->occurn[-v][S->occurn_size[-v]++] = i;
                if (pnsign(v) * S->mapval[abs(v)] == 1) satisify = 1;
                if (!S->mapval[abs(v)]) ++S->clause_state[i];
            }
            if (satisify) S->clause_state[i] = -1;
            if (!S->clause_state) puts("c wrong unsat clause");
        }
        for (int ii = S->resolutions; ii >= 1; ii--) {
            int v = S->resolution[ii];
            if (v > S->orivars || v <= 0) puts("c wrong idx");
            //attempt 1
            int assign = 1;
            for (int i = 0; i < S->occurn_size[v]; i++) {
                int o = S->occurn[v][i];
                if (S->clause_state[o] != -1 && S->clause_state[o] <= 1) {assign = 0; break;}
            }
            if (assign == 1) {
                S->mapval[v] = 1;
                for (int i = 0; i < S->occurn_size[v]; i++) {
                    int o = S->occurn[v][i];
                    if (S->clause_state[o] != -1) S->clause_state[o]--;
                } 
                for (int i = 0; i < S->occurp_size[v]; i++) 
                    S->clause_state[S->occurp[v][i]] = -1;
                continue;
            }
            //attempt -1
            assign = -1;
            for (int i = 0; i < S->occurp_size[v]; i++) {
                int o = S->occurp[v][i];
                if (S->clause_state[o] != -1 && S->clause_state[o] <= 1) {assign = 0; break;}
            }
            if (assign == -1) {
                S->mapval[v] = -1;
                for (int i = 0; i < S->occurp_size[v]; i++) {
                    int o = S->occurp[v][i];
                    if (S->clause_state[o] != -1) S->clause_state[o]--;
                } 
                for (int i = 0; i < S->occurn_size[v]; i++) 
                    S->clause_state[S->occurn[v][i]] = -1;
                continue;
            }
            printf("c wrong assign");
        }
        free(S->clause_state);
        for (int i = 1; i <= S->orivars; i++) {
            if (S->occurn[i] != NULL) free(S->occurn[i]);
            if (S->occurp[i] != NULL) free(S->occurp[i]);
        }
        free(S->occurn_size);
        free(S->occurp_size);
        free(S->occurn);
        free(S->occurp);

        free(S->res_clause_size);
        for (int i = 1; i <= S->res_clauses; i++)
            free(S->res_clause[i]);
        free(S->res_clause);
        free(S->resolution);
    }  
    chars buffer;
    INIT_STACK(buffer);
    for (int i = 1; i <= S->orivars; i++) {
        print_int(solver, &buffer, i * S->mapval[i]);
    }
    print_int(solver, &buffer, 0);
    assert(!EMPTY_STACK(buffer));
    flush_buffer(&buffer);
    RELEASE_STACK(buffer);
    free(S->mapto);
    free(S->mapval);
}