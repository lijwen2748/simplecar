/*
    Copyright (C) 2018, Jianwen Li (lijwen2748@gmail.com), Iowa State University

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

/* 
 * File:   carsolver.cpp
 * Author: Jianwen Li
 * Note: An inheritance class from Minisat::Solver for CAR use 
 * Created on October 4, 2017
 */
 
#include "carsolver.h"
#include <iostream>
#include <vector>
using namespace std;

#ifndef ENABLE_PICOSAT  
using namespace Minisat;
//using namespace Glucose;
#endif

namespace car
{
 	#ifdef ENABLE_PICOSAT
 	int CARSolver::SAT_lit (int id) {
 	    assert (id != 0);
 	    while (abs (id) > picosat_variables (picosat_)) {
 	        picosat_inc_max_var (picosat_);
 	    }
 	    return id;
 	}
 	
 	int CARSolver::lit_id (int id) {
 	    return id;
 	}
 	
 	bool CARSolver::solve_assumption () {
 		for (int i = 0; i < assumption_.size (); i ++) {
 			picosat_assume (picosat_, assumption_[i]);
 		}
 	    int res = picosat_sat(picosat_, -1);
        return res == PICOSAT_SATISFIABLE;
 	}
 	
 	//return the model from SAT solver when it provides SAT
	std::vector<int> CARSolver::get_model () {
	    vector<int> res;
	    int max_var = picosat_variables (picosat_);
	    res.resize (max_var, 0);
	    for (int i = 1; i < max_var; i ++) {
	        int val = picosat_deref(picosat_, i);
            if (val == 1)
                res[i-1] = i;
            else if (val == -1)
                res[i-1] = -i;
        }
        
   		return res;
	}
	
	//return the UC from SAT solver when it provides UNSAT
 	std::vector<int> CARSolver::get_uc () {
 		std::vector<int> reason;
		if (verbose_)
			cout << "get uc: \n";
		//const int *p = picosat_failed_assumptions (picosat_);
		const int *p = picosat_mus_assumptions (picosat_, 0, NULL, 0);
		while (*p != 0) {
		    reason.push_back (*p);
		    if (verbose_)
				cout << *p << ", ";
		    p++; 
		}
 		
		if (verbose_)
			cout << endl;
    	return reason;
  	}
	
	void CARSolver::add_clause (std::vector<int>& v) {
	    for (int i = 0; i < v.size(); i ++) {
            picosat_add(picosat_, v[i]);
        }
        picosat_add(picosat_, 0);
 		
 	}
 	
 	#else
 	
 	Lit CARSolver::SAT_lit (int id)
 	{
 		assert (id != 0);
        int var = abs(id)-1;
        while (var >= nVars()) newVar();
        return ( (id > 0) ? mkLit(var) : ~mkLit(var) );
 	}
 	
 	int CARSolver::lit_id (Lit l)
    {
    	if (sign(l)) 
            return -(var(l) + 1);
        else 
            return var(l) + 1;
    }
 	
 	bool CARSolver::solve_assumption ()
	{
		lbool ret = solveLimited (assumption_);
		if (verbose_)
		{
			cout << "CARSolver::solve_assumption: assumption_ is" << endl;
			for (int i = 0; i < assumption_.size (); i ++)
				cout << lit_id (assumption_[i]) << ", ";
			cout << endl;
		}
		if (ret == l_True)
     		return true;
   		else if (ret == l_Undef)
     		exit (0);
   		return false;
	}
	
	//return the model from SAT solver when it provides SAT
	std::vector<int> CARSolver::get_model ()
	{
		std::vector<int> res;
		res.resize (nVars (), 0);
   		for (int i = 0; i < nVars (); i ++)
   		{
     		if (model[i] == l_True)
       			res[i] = i+1;
     		else if (model[i] == l_False)
       			res[i] = -(i+1);
   		}
   		return res;
	}
	
	//return the UC from SAT solver when it provides UNSAT
 	std::vector<int> CARSolver::get_uc ()
 	{
 		std::vector<int> reason;
		if (verbose_)
			cout << "get uc: \n";
 		for (int k = 0; k < conflict.size(); k++) 
 		{
        	Lit l = conflict[k];
        	reason.push_back (-lit_id (l));
			if (verbose_)
				cout << -lit_id (l) << ", ";
    	}
		if (verbose_)
			cout << endl;
    	return reason;
  	}
	
	void CARSolver::add_clause (std::vector<int>& v)
 	{
 		vec<Lit> lits;
 		for (std::vector<int>::iterator it = v.begin (); it != v.end (); it ++)
 			lits.push (SAT_lit (*it));
 		/*
 		if (verbose_)
 		{
 			cout << "Adding clause " << endl << "(";
 			for (int i = 0; i < lits.size (); i ++)
 				cout << lit_id (lits[i]) << ", ";
 			cout << ")" << endl;
 			cout << "Before adding, size of clauses is " << clauses.size () << endl;
 		}
 		*/
 		bool res = addClause (lits);
 		
 		if (!res && verbose_)
 			cout << "Warning: Adding clause does not success\n";
 		
 	}
 	
 	#endif
 	
 	void CARSolver::add_clause (int id)
 	{
 		std::vector<int> v;
 		v.push_back (id);
 		add_clause (v);
 	}
 	
 	void CARSolver::add_clause (int id1, int id2)
 	{
 		std::vector<int> v;
 		v.push_back (id1);
 		v.push_back (id2);
 		add_clause (v);
 	}
 	
 	void CARSolver::add_clause (int id1, int id2, int id3)
 	{
 		std::vector<int> v;
 		v.push_back (id1);
 		v.push_back (id2);
 		v.push_back (id3);
 		add_clause (v);
 	}
 	
 	void CARSolver::add_clause (int id1, int id2, int id3, int id4)
 	{
 		std::vector<int> v;
 		v.push_back (id1);
 		v.push_back (id2);
 		v.push_back (id3);
 		v.push_back (id4);
 		add_clause (v);
 	}
 	
 	void CARSolver::add_cube (const std::vector<int>& cu)
 	{
 	    for (int i = 0; i < cu.size (); i ++)
 	        add_clause (cu[i]);
 	}
 	
 	void CARSolver::add_clause_from_cube (const std::vector<int>& cu)
 	{
 	    vector<int> v;
 	    for (int i = 0; i < cu.size (); i ++)
 	        v.push_back (-cu[i]);
 	    add_clause (v);
 	}
 	
 	void CARSolver::print_clauses ()
	{
		#ifndef ENABLE_PICOSAT
		cout << "clauses in SAT solver: \n";
		for (int i = 0; i < clauses.size (); i ++)
		{
			Clause& c = ca[clauses[i]];
			for (int j = 0; j < c.size (); j ++)
				cout << lit_id (c[j]) << " ";
			cout << "0 " << endl;
		}
		#endif
	}
	
	void CARSolver::print_assumption ()
	{
	    cout << "assumptions in SAT solver: \n";
	    for (int i = 0; i < assumption_.size (); i ++)
	        cout << lit_id (assumption_[i]) << " ";
	    cout << endl;
	}
	
}
