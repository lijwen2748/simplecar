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
//using namespace Minisat;
using namespace Glucose;

namespace car
{
 	
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
		cout << "clauses in SAT solver: \n";
		for (int i = 0; i < clauses.size (); i ++)
		{
			Clause& c = ca[clauses[i]];
			for (int j = 0; j < c.size (); j ++)
				cout << lit_id (c[j]) << " ";
			cout << "0 " << endl;
		}
	}
	
	void CARSolver::print_assumption ()
	{
	    cout << "assumptions in SAT solver: \n";
	    for (int i = 0; i < assumption_.size (); i ++)
	        cout << lit_id (assumption_[i]) << " ";
	    cout << endl;
	}
	
}
