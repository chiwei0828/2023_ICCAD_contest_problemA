#include "simplify.h"
#include "internal.h"
#include "import.h"
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
        if (S->occurn_size[i] == 0 && S->occurp_size[i] == 0) S->clean[i] = 1;  

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
            // printf("c wrong assign");
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