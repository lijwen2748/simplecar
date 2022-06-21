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
	Author: Jianwen Li
	Update Date: October 6, 2017
	Main Solver in CAR
*/

#ifndef MAIN_SOLVER_H
#define MAIN_SOLVER_H

#include "carsolver.h"
#include "data_structure.h"
#include "model.h"
#include "statistics.h"
#include <vector>
#include <assert.h>
#include <iostream>

namespace car{

class MainSolver : public CARSolver 
{
	public:
		MainSolver (Model*, Statistics* stats, const bool verbose = false);
		~MainSolver (){}
		
		//public funcitons
		void set_assumption (const Assignment&, const int frame_level, const bool forward);
		void set_assumption (const Assignment&, const int);
		void set_assumption (const Assignment& st){
			assumption_.clear ();
			for (auto it = st.begin(); it != st.end(); ++it)
				assumption_push (*it);
		}
		
		
		inline bool solve_with_assumption (const Assignment& st, const int p)
		{
		    set_assumption (st, p);
		    if (verbose_)
		    	std::cout << "MainSolver::";
		    return solve_assumption ();
		}
		
		inline bool solve_with_assumption (const Assignment& st)
		{
		    set_assumption (st);
		    if (verbose_)
		    	std::cout << "MainSolver::";
		    return solve_assumption ();
		}
		
		inline bool solve_with_assumption ()
		{
			if (verbose_)
		    	std::cout << "MainSolver::";
		    return solve_assumption ();
		}
		
		Assignment get_state (const bool forward = true, const bool partial = false);
		
		//this version is used for bad check only
		Cube get_conflict (const int bad);
		Cube get_conflict (const bool forward, const bool minimal, bool& constraint);
		
		void add_new_frame (const Frame& frame, const int frame_level, const bool forward);
		//overload
		void add_clause_from_cube (const Cube& cu, const int frame_level, const bool forward_);
		
		bool solve_with_assumption_for_temporary (Cube& s, int frame_level, bool forward, Cube& tmp_block);
		
		inline void update_constraint (Cube& cu)
		{
		    CARSolver::add_clause_from_cube (cu);
		}
		
		inline void clear_frame_flags () {frame_flags_.clear ();}
		
		inline int new_flag (){
			return max_flag_++;
		}
		
		inline int init_flag () {return init_flag_;}
		inline int dead_flag () {return dead_flag_;}
		
	private:
		//members
		int max_flag_;
		std::vector<int> frame_flags_;
		
		int init_flag_, dead_flag_;
		
		Model* model_;
		
		Statistics* stats_;
		
		//bool verbose_;
		
		//functions
		
		
		
		inline int flag_of (const unsigned frame_level) 
		{
		    assert (frame_level >= 0);
			while (frame_level >= frame_flags_.size ())
			{
				frame_flags_.push_back (max_flag_++);
			}
	        
			return frame_flags_[frame_level];
		}
		void shrink_model (Assignment& model, const bool forward, const bool partial);
		void try_reduce (Cube& cu);
};

}

#endif

