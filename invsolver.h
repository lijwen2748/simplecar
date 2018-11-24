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
	Update Date: October 4, 2017
	Invariant Solver in CAR
*/

#ifndef INV_SOLVER_H
#define INV_SOLVER_H

#include "data_structure.h"
#include "carsolver.h"
#include "model.h"
#include <vector>

namespace car 
{
	class InvSolver : public CARSolver
	{
		public:
			InvSolver (const Model* m, bool verbose = false) : id_aiger_max_ (const_cast<Model*>(m)->max_id ())
			{
				model_ = const_cast<Model*> (m);
			    verbose_ = verbose;
			    int end = model_->outputs_start ();
			    for (int i = 0; i < end ; i ++)
                    add_clause (model_->element (i));
			}
			~InvSolver () {;}
		
			inline bool solve_with_assumption ()
			{
				if (verbose_)
					std::cout << "InvSolver::";
				return solve_assumption ();
			}
			
			inline void add_constraint_or (const Frame &frame, bool forward = false)
			{
				std::vector<int> v;
 				for (int i = 0; i < frame.size (); i ++)
 				{
 					int clause_flag = new_var ();
 					v.push_back (clause_flag);
 					for (int j = 0; j < frame[i].size (); j ++)
 					{
 						int id = frame[i][j];
 						add_clause (-clause_flag, id);
 					}
 				}
 				add_clause (v);
			}
			
			inline void add_constraint_and (const Frame &frame, bool forward = false)
			{
				int frame_flag = new_var ();
 				for (int i = 0; i < frame.size (); i ++)
 				{
 					std::vector<int> v;
 					for (int j = 0; j < frame[i].size (); j ++)
 					{
 						int id = frame[i][j];
 						v.push_back (-id);
 					}
 					v.push_back (-frame_flag);
 					add_clause (v);
 				}
 				update_assumption_for_constraint (frame_flag);
			}
			
			inline void update_assumption_for_constraint (const int frame_flag)
			{
				assumption_push (frame_flag);
			}
			
			inline void release_constraint_and ()
			{
				#ifdef ENABLE_PICOSAT
				int l = assumption_.back ();
				assumption_pop ();
 				assumption_push (-l);
				#else
				Minisat::Lit l = assumption_.last ();
				//Glucose::Lit l = assumption_.last ();
				assumption_.pop ();
 				assumption_.push (~l);
 				#endif
			}
			
			inline int new_var () {return ++id_aiger_max_;}
		protected:
			Model* model_;
			int id_aiger_max_;  	//to store the maximum number used in aiger model
	};
}
#endif
