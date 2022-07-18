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
 * File:   carsolver.h
 * Author: Jianwen Li
 * Note: An inheritance class from Minisat::Solver for CAR use 
 * Created on October 4, 2017
 */
 
#ifndef CAR_SOLVER_H
#define	CAR_SOLVER_H

#ifdef ENABLE_PICOSAT
extern "C" {
#include "picosat/picosat.h"
}
#else
#include "minisat/core/Solver.h"
//#include "glucose/core/Solver.h"
#endif

#include "statistics.h"  //zhang xiaoyu made this change
#include <vector>
#include <assert.h>
#include <fstream>      //zhang xiaou add this code

namespace car
{
    #ifdef ENABLE_PICOSAT
    class CARSolver 
    #else
	class CARSolver : public Minisat::Solver //Glucose:Solver
	#endif
	{
	public:
	    #ifdef ENABLE_PICOSAT
	    CARSolver () { picosat_ = picosat_init(); }
		CARSolver (bool verbose) : verbose_ (verbose) { picosat_reset(picosat_); } 
	    #else
		CARSolver () {}
		CARSolver (bool verbose) : verbose_ (verbose) {} 
		#endif
		
		bool verbose_;
		
		#ifdef ENABLE_PICOSAT
		std::vector<int> assumption_;
		#else
		Minisat::vec<Minisat::Lit> assumption_;  //Assumption for SAT solver
		//Glucose::vec<Glucose::Lit> assumption_;  //Assumption for SAT solver     
		#endif
		Statistics* stats_;   //zhang xiaoyu made this change
		//functions
		bool solve_assumption ();
		std::vector<int> get_model ();    //get the model from SAT solver
 		std::vector<int> get_uc ();       //get UC from SAT solver
		//zhang xiaoyu code begins
		void update_assumption(std::vector<int> new_reason);
		std::vector<int> get_solver_uc();  //get UC from sat solver 
	    std::vector<int> get_mus(std::vector<int> mus_reason);
		
        // void recursive_model_rotation();
	    //zhang xiaoyu code ends	
		void add_cube (const std::vector<int>&);
		void add_clause_from_cube (const std::vector<int>&);
		void add_clause (int);
 		void add_clause (int, int);
 		void add_clause (int, int, int);
 		void add_clause (int, int, int, int);
 		void add_clause (std::vector<int>&);
 	
 	    #ifdef ENABLE_PICOSAT
 	    int SAT_lit (int id); //create the Lit used in PicoSat SAT solver for the id.
 		int lit_id (int);  //return the id of SAT lit
 	    #else
 		Minisat::Lit SAT_lit (int id); //create the Lit used in SAT solver for the id.
 		int lit_id (Minisat::Lit);  //return the id of SAT lit
 		
 		//Glucose::Lit SAT_lit (int id); //create the Lit used in SAT solver for the id.
 		//int lit_id (Glucose::Lit);  //return the id of SAT lit
 		#endif
 		
 		//inline int size () {return clauses.size ();}
 		inline void clear_assumption () {assumption_.clear ();}
 		
 		inline void assumption_push (int id) {
 			#ifdef ENABLE_PICOSAT
 			assumption_.push_back (id);
 			#else
 			assumption_.push (SAT_lit (id));
 			#endif
 		}
 		
 		inline void assumption_pop () {
 			#ifdef ENABLE_PICOSAT
 			assumption_.pop_back ();
 			#else
 			assumption_.pop ();
 			#endif
 		}
 		
 		//printers
 		void print_clauses ();
 		void print_assumption ();
 		
 		//l <-> r
 		inline void add_equivalence (int l, int r)
 		{
 			add_clause (-l, r);
 			add_clause (l, -r);
 		}
 	
 		//l <-> r1 /\ r2
 		inline void add_equivalence (int l, int r1, int r2)
 		{
 			add_clause (-l, r1);
 			add_clause (-l, r2);
 			add_clause (l, -r1, -r2);
 		}
 	
 		//l<-> r1 /\ r2 /\ r3
 		inline void add_equivalence (int l, int r1, int r2, int r3)
 		{
 			add_clause (-l, r1);
 			add_clause (-l, r2);
 			add_clause (-l, r3);
 			add_clause (l, -r1, -r2, -r3);
 		}
 	#ifdef ENABLE_PICOSAT
 	private:
 	   PicoSAT* picosat_;
 	#endif
	};
}

#endif
