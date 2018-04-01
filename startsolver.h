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
	Update Date: October 23, 2017
	Start Solver in CAR
*/

#ifndef START_SOLVER_H
#define START_SOLVER_H

#include "carsolver.h"
#include "model.h"
#include "data_structure.h"

namespace car {
    class StartSolver : public CARSolver {
    public:
        StartSolver (const Model* m, const int bad, const bool forward, const bool verbose = false)
        {
            verbose_ = verbose;
            if (!forward)
                add_cube (const_cast<Model*>(m)->init ());
            else
            {
                for (int i = 0; i < const_cast<Model*>(m)->latches_start (); i ++)
                    add_clause (const_cast<Model*>(m)->element (i));
                assumption_push (bad);
            }
            
            forward_ = forward;
            max_id_ = const_cast<Model*>(m)->max_id () + 1;
            flag_ = max_id_;
        }
        ~StartSolver () {}
        
        inline bool solve_with_assumption ()
        {
        	if (verbose_)
        		std::cout << "StartSolver::";
        	return solve_assumption ();
        }
        
        inline void reset ()
        {
        	int threshold = forward_ ? 1 : 0;
            if (assumption_.size () <= threshold)
            {
                assumption_push (flag_);
                return;
            }
            assumption_pop ();
            assumption_push (-flag_);
            assumption_push (++flag_);
        }
        inline void add_clause_with_flag (const Cube& cu)
        {
            std::vector<int> cl;
            cl.push_back (-flag_);
            for (int i = 0; i < cu.size (); i ++)
                cl.push_back (-cu[i]);
            add_clause (cl);
        }
        
        inline void update_constraint (Cube &cu)
        {
            CARSolver::add_clause_from_cube (cu);
        }
        
     private:
        int max_id_;
        int flag_;
        bool forward_;
        
    };
}

#endif
