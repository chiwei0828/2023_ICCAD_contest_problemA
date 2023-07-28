// Norbert Manthey, 2017

// make sure we use IPASIR
#define HAVE_IPASIR

// declare IPASIR functions here, which we might need
#include "SATSolver.h"

#include <iostream>
#include <vector>

using namespace std;

#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#include <time.h>

inline double cpuTime(void)
{
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000;
}

int main(int argc, char* argv[])
{
  std::cout << "Norbert Manthey -- IPASIR iterative load checker" << std::endl;
  std::cout << "  add formula that has sub formulas of blocks" << std::endl
            << "  use full stack of assumptions and modify last polarities per call" << std::endl;
  if(argc < 3) {
    std::cout << "usage: " << argv[0] << " X Y Z ... with 2 < X < 2^30, 1 < Y < 10, 1 < Z" << std::endl;
    return 1;
  }
  
  int X = atoi(argv[1]);
  int Y = atoi(argv[2]);
  int Z = atoi(argv[3]);
  
  if(X<3) {
    std::cout << "error: given first number " << X << " is not in limits" << std::endl;
    return 1;
  }
  
  if(Y<1 || Y>9) {
    std::cout << "error: given second number " << Y << " is not in limits" << std::endl;
    return 1;
  }
  
  if(Z < 2)  {
    std::cout << "error: given third number " << Z << " is not in limits" << std::endl;
    return 1;
  }

  SATSolver solver;
  
  const int periodsize = (1 << Y);
  vector<int> clause(Y,0);
  int index = 0;
  int clauses = 0;
  int maxvar = 0;
  for(int i = 1 ; i < periodsize; ++i) {
    index = i;
    int sum = 0;
    for(int j = 0 ; j < Y; ++j) {
      clause[j] = ((index & 1) == 0) ? j+1 : -j-1;
      sum += clause[j] > 0 ? 1 : -1;
      index = index >> 1;
    }
    assert(sum < (int)clause.size() && "clause with positive literals only should not be created");
    
    for(int j = 0; j < Z; ++ j) {
      if(j>0) {
	for(int k=0; k < Y; ++k) {
	  clause[k] = clause[k] > 0 ? clause[k] + Y : clause[k] - Y;
	  maxvar = maxvar > clause[k] ? maxvar : clause[k];
	}
      }
      solver.addClause(clause);
      clauses ++;
    }
  }
  
  std::cout << "created formula with " << clauses << " clauses, and maxvar " << maxvar << std::endl;
  
  vector<int> assumptions;
  std::vector<int> model;
  std::vector<int> conflict;
  
  for(int i = 1 ; i <= maxvar; ++i) assumptions.push_back(-i);
  int ret = solver.solve(assumptions, model, conflict);
  std::cout << "initial call returned with " << ret << std::endl;
  if(ret != 10)
  {
    std::cout << "error: first call did not result in model, but " << ret << ", abort" << std::endl;
    return 1;
  }
  
  double runtime = cpuTime();
  int call = 0;
  for(int i = 2; i <= X; ++ i)
  {
    // modify last bits of assumptions
    int mask = call;
    int index = 1;
    while(mask > 0 && index <= assumptions.size()) {
      if((mask & 1)==1) assumptions[assumptions.size() - index] = -assumptions[assumptions.size() - index];
      mask = mask >> 1;
      index ++;
    }
    conflict.clear();
    int ret = solver.solve(assumptions, model, conflict);
    call ++;
    if(i % 256 == 0) std::cout << "  after " << i << " calls: " << (double)X / (cpuTime()-runtime) << " calls per second" << std::endl;
    if (ret==20) {
      solver.addClause(conflict);
    } else if (call!=1) {
      std::cout << "error: in call " << call << ", did not detect conflict (but " << ret << ") on unsatisfiable input, abort" << std::endl;
      std::cout << "used assumptions: " << assumptions << std::endl;
      return 1;
    }

    // modify last bits of assumptions
    mask = call;
    index = 1;
    while(mask > 0 && index <= assumptions.size()) {
      if(assumptions[assumptions.size() - index] > 0) assumptions[assumptions.size() - index] = -assumptions[assumptions.size() - index];
      mask = mask >> 1;
      index ++;
    }
  }
  runtime = cpuTime() - runtime;
  std::cout << "performed " << (double)X / runtime << " calls per second" << std::endl;
  
  return 0;
}
  
