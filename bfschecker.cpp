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
	Update Date: July 21, 2018
	Interface for the BFS checker class
*/

#include "bfschecker.h"
#include <iostream>
using namespace std;

namespace car {

    bool BfsChecker::try_satisfy (const int frame_level)
	{
				
		int res = do_search (frame_level);
		if (res == 1)
		    return true;
		else if (res == 0)
		    return false;
		
		//for forward CAR, the initial states are set of cubes
		State *s = enumerate_start_state ();
		while (s != NULL)
		{
		    if (!forward_) //for dot drawing
			    s->set_initial (true);
			
			//////generate dot data
			if (dot_ != NULL)
			    (*dot_) << "\n\t\t\t" << s->id () << " [shape = circle, color = red, label = \"Init\", size = 0.1];";
			//////generate dot data
			
			s->set_depth (0);
		    update_B_sequence (s);
		    
		    const_cast<State*> (s)->set_work_level (frame_level);
		    
			if (try_satisfy_by (frame_level, s))
			    return true;
			if (safe_reported ())
				return false;
		    s = enumerate_start_state ();
		}
	
		return false;
	}

    int BfsChecker::do_search (const int frame_level) {
        for (int i = B_.size () - 1; i >= 0; i --){
	        for (int j = 0; j < B_[i].size (); j ++){
			    if (try_satisfy_by (B_[i][j]->work_level (), B_[i][j]))
			        return 1;
				if (safe_reported ())
				    return 0;
			    }
		    }
		return -1;
    }

    bool BfsChecker::try_satisfy_by (int frame_level, const State* s) {
        if (tried_before (s, frame_level+1)) {
            const_cast<State*> (s)->set_work_level (frame_level+1);
			return false;
	    }
		
		if (frame_level < minimal_update_level_)
			minimal_update_level_ = frame_level;
		
		
		if (frame_level == -1)
		{
		    if (immediate_satisfiable (s))
		        return true;
		}
		else
		{
		    
		    while (solve_with (const_cast<State*>(s)->s (), frame_level))
		    {
			    State* new_state = get_new_state (s);
			    assert (new_state != NULL);
			    
			    //////generate dot data
			    if (dot_ != NULL)
			        (*dot_) << "\n\t\t\t" << const_cast<State*> (s)->id () << " -- " << new_state->id ();
			    //////generate dot data
			    
			    int new_level = get_new_level (new_state, frame_level);

			    update_B_sequence (new_state);
			    
			    new_state -> set_work_level (new_level);
			    
			    if (try_satisfy_by (new_level, new_state))
				    return true;
				if (safe_reported ())
				    return false;
				if (frame_level < s->work_level ())
				{ 
				    while (tried_before (s, frame_level+1))
				    {
				        frame_level = frame_level + 1;
					    if (frame_level >= s->work_level ()) {
					        const_cast<State*> (s)->set_work_level (frame_level+1);
						    return false;	
						}
				    }
				}
		    }
		}

		update_F_sequence (s, frame_level+1);
		if (safe_reported ())
			return false;
		
		const_cast<State*> (s)->set_work_level (frame_level+1);

		return false;
    }
    
}

