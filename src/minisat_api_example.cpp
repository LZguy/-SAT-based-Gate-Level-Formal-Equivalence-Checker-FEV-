/*****************************************************************************************
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson
Copyright (c) 2014, Eitan Zahavi

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
/*
  An API example for (a’+b+c’)(d+c+a)(d’+e+f)(a+f’)(b+d+e)
  Clauses are:
  -1 2 -3 0
  4 3 1 0
  -4 5 6 0
  1 -6 0
  2 4 5 0
*/

#include <errno.h>

#include <signal.h>
#include <zlib.h>
#define __STDC_LIMIT_MACROS
#define __STDC_FORMAT_MACROS

//#include <stdint.h>
//#include <inttypes.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"

#include <string>
#include "hcm.h"

using namespace Minisat;

//=================================================================================================


void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %"PRIu64"\n", solver.starts);
    printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
    printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
    printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
    printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}

//=================================================================================================
// Main:

int main(int argc, char** argv)
{
  // just that you can see HCM compiles and links with example Makefile
    hcmDesign* specDes = new hcmDesign("spec");

    try {
      Solver S1;
      Solver S2;

      S1.verbosity = false;
      S2.verbosity = false;
      
      // Declare 16 variables
      for (unsigned int i = 0; i < 6; i++) {
	S1.newVar();
	S2.newVar();
      }

      // each clause needs its own literals vector
      vec<Lit> lits;
      
      // -1 2 -3 0 
      lits.clear();
      lits.push( ~mkLit(0) );
      lits.push(  mkLit(1) );
      lits.push( ~mkLit(2) );

      // HACK: shouldn't we check for the result?
      S1.addClause(lits);
      S2.addClause(lits);

      // 4 3 1 0
      lits.clear();
      lits.push( mkLit(3) );
      lits.push( mkLit(2) );
      lits.push( mkLit(0) );
      S1.addClause(lits);
      S2.addClause(lits);

      // -4 5 6 0
      lits.clear();
      lits.push( ~mkLit(3) );
      lits.push(  mkLit(4) );
      lits.push(  mkLit(5) );
      S1.addClause(lits);
      S2.addClause(lits);

      // 1 -6 0
      lits.clear();
      lits.push( mkLit(0) );
      lits.push( ~mkLit(5) );
      S1.addClause(lits);
      S2.addClause(lits);

      // 2 4 5 0
      lits.clear();
      lits.push( mkLit(1) );
      lits.push( mkLit(3) );
      lits.push( mkLit(4) );
      S1.addClause(lits);
      S2.addClause(lits);

      if (S1.verbosity > 0){
	printf("============================[ Problem Statistics ]=============================\n");
	printf("|                                                                             |\n"); 
	printf("|  Number of variables:  %12d                                         |\n", S1.nVars());
	printf("|  Number of clauses:    %12d                                         |\n", S1.nClauses()); 
      }
      
      FILE* res = fopen("minisat_api_example.out", "wb");
      
      if (!S1.simplify()){
	if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
	if (S1.verbosity > 0){
	  printf("===============================================================================\n");
	  printf("S1 Solved by unit propagation\n");
	  printStats(S1);
	  printf("\n"); 
	}
	printf("S1 UNSATISFIABLE\n");
	exit(20);
      }

      if (!S2.simplify()){
	if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
	if (S1.verbosity > 0){
	  printf("===============================================================================\n");
	  printf("S2 Solved by unit propagation\n");
	  printStats(S2);
	  printf("\n"); 
	}
	printf("S1 UNSATISFIABLE\n");
	exit(20);
      }
      
      vec<Lit> dummy;
      lbool ret = S1.solveLimited(dummy);
      if (S1.verbosity > 0) {
	printStats(S1);
	printf("\n"); 
      }
      printf(ret == l_True ? "S1 SATISFIABLE\n" : ret == l_False ? "S1 UNSATISFIABLE\n" : "S1 INDETERMINATE\n");
      if (res != NULL){
	if (ret == l_True){
	  fprintf(res, "S1 SAT\n");
	  for (int i = 0; i < S1.nVars(); i++)
	    if (S1.model[i] != l_Undef)
	      fprintf(res, "%s%s%d", (i==0)?"":" ", (S1.model[i]==l_True)?"":"-", i+1);
	  fprintf(res, " 0\n");
	} else if (ret == l_False)
	  fprintf(res, "S1 UNSAT\n");
	else
	  fprintf(res, "S1 INDET\n");
      }

      // we now do provide an assumptions section
      // dummy.push( mkLit(2) );
      // dummy.push( mkLit(4) );
      // dummy.push( mkLit(5) );
      bool ret2 = S2.solve();
      if (S2.verbosity > 0) {
	printStats(S2);
	printf("\n"); 
      }
      printf(ret2 == true ? "S2 SATISFIABLE\n" : "S2 UNSATISFIABLE\n");
      if (ret2 == true){
	fprintf(res, "S2 SAT\n");
	for (int i = 0; i < S2.nVars(); i++)
	  if (S2.model[i] != l_Undef)
	    fprintf(res, "%s%s%d", (i==0)?"":" ", (S2.model[i]==l_True)?"":"-", i+1);
	fprintf(res, " 0\n");
      } else {
	fprintf(res, "S2 UNSAT\n");
      }
      fclose(res);
      
      return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
    } catch (OutOfMemoryException&){
      printf("===============================================================================\n");
      printf("INDETERMINATE\n");
      exit(0);
    }
}
