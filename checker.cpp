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
	Update Date: September 8, 2017
	Interface for the checker class
*/
#include "checker.h"
#include <vector>
#include <iostream>
#include "utility.h"
#include "statistics.h"
using namespace std;

namespace car
{
    ///////////////////////////////////main functions//////////////////////////////////
    bool Checker::check (std::ofstream& out)
	{
	    for (int i = 0; i < model_->num_outputs (); i ++)
	    {
	        bad_ = model_->output (i);
	        if (bad_ == model_->true_id ())
	        {
	        	out << "1" << endl;
	        	out << "b" << i << endl;
	        	if (evidence_)
	        	{
	        	    //print init state
	        	    out << init_->latches() << endl;
	        	    //print an arbitary input vector
	        	    for (int j = 0; j < model_->num_inputs (); j ++)
	        	        out << "0";
	        	    out << endl;
	        	}
	        	out << "." << endl;
	        	if (verbose_)
	        	{
	        		cout << "return SAT since the output is true" << endl;
	        	}
	        	return true;
	        }
	        else if (bad_ == model_->false_id ())
	        {
	        	out << "0" << endl;
	        	out << "b" << endl;
	        	out << "." << endl;
	        	if (verbose_)
	        	{
	        		cout << "return UNSAT since the output is false" << endl;
	        	}
	        	return false;
	        }
	        car_initialization ();
	        bool res = car_check ();
	        if (res)
    			out << "1" << endl;
   			else
    			out << "0" << endl;
    		out << "b" << i << endl;
   			if (evidence_ && res)
    			print_evidence (out);
    		out << "." << endl;
	        car_finalization ();
	        return res;
	    }
	}
	
	bool Checker::car_check ()
	{
		if (verbose_)
			cout << "start check ..." << endl;
		if (immediate_satisfiable ())
		{
			if (verbose_)
				cout << "return SAT from immediate_satisfiable" << endl;
			return true;
		}

		initialize_sequences ();
			
		int frame_level = 0;
		while (true)
		{
		    if (verbose_)
		    {
		        cout << "-----------------Step " << frame_level << "------------------" << endl;
		        print ();
		    }
		    //handle the special start states
			reset_start_solver ();
		    clear_frame ();
		    if (propagate_)
			{
				if (propagate ())
				{
					return false;
				}
			}
			minimal_update_level_ = F_.size () - 1;
			if (try_satisfy (frame_level))
			{
				if (verbose_)
					cout << "return SAT from try_satisfy at frame level " << frame_level << endl;
				return true;
			}
			//it is true when some reason returned from Main solver is empty
			if (safe_reported ())
			{
				if (verbose_)
					cout << "return UNSAT from safe reported" << endl;
				return false;
			}
			extend_F_sequence ();
			frame_level ++;
			
			if (invariant_found (frame_level+1))
			{
				if (verbose_)
				{
					cout << "return UNSAT from invariant found at frame " << F_.size ()-1 << endl;
					print ();
				}
				return false;
			}
			
		}
		if (verbose_)
			cout << "end of check" << endl;
		return false;
	}
	bool Checker::try_satisfy (const int frame_level)
	{
		
		    remove_dead_states ();
		
		for (int i = B_.size () - 1; i >= 0; i --)
		{
			for (int j = 0; j < B_[i].size (); j ++)
			{
			    
				if (try_satisfy_by (frame_level, B_[i][j]))
					return true;
				if (safe_reported ())
					return false;
			}
		}
		
		State *s = enumerate_start_state ();
		while (s != NULL)
		{
			
		    update_B_sequence (s, 0);
			if (try_satisfy_by (frame_level, s))
			    return true;
			if (safe_reported ())
				return false;
		    s = enumerate_start_state ();
		}
	
		return false;
	}
	
	bool Checker::try_satisfy_by (int frame_level, const State* s)
	{
		if (tried_before (s, frame_level+1))
			return false;
		
		if (frame_level < minimal_update_level_)
			minimal_update_level_ = frame_level;
		
		//print state and frame level
		if (verbose_)
		{
			cout << "try_satisfy_by:" << endl;
			cout << "	current frame level: " << frame_level << endl;
			cout << "	current state: ";
		    const_cast<State*>(s)->print ();
		    cout << "	current state address: " << s << endl;
		    cout << "	next state address: " << const_cast<State*> (s)->next () << endl;
		    cout << "	pre state address: " << const_cast<State*> (s)->pre () << endl;
		}
		
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
			    int new_level = get_new_level (new_state, frame_level);
			    if (detect_dead_state_ && new_level != -1)
		    	{	
		        	if (dead_state (new_state))
		        	{
		            	stats_->count_detect_dead_state_success ();
		            	bool con;
		            	Cube cu = solver_->get_conflict (forward_, minimal_uc_, con);
		            	update_constraint (cu);
		            	delete new_state;
		            	if (safe_reported ())
		            		return false;
		            	continue;
		        	}
		    	}
			    update_B_sequence (new_state, frame_level);
			    
			    if (try_satisfy_by (new_level, new_state))
				    return true;
				if (frame_level < F_.size ())
				{
				    
				    while (tried_before (s, frame_level+1))
				    {
				        frame_level = frame_level + 1;
					    if (frame_level >= F_.size ())
						    return false;	
				    }
				}
		    }
		}

		update_F_sequence (s, frame_level+1);
		if (safe_reported ())
			return false;
		
		frame_level += 1;
		if (frame_level < int (F_.size ()))
		{
		    return try_satisfy_by (frame_level, s);
		}
		
		return false;
	}
	
	bool Checker::propagate () 
	{
		if (verbose_)
			cout << "start propagate " << endl;
		for (int i = minimal_update_level_+1; i < F_.size (); i ++)
		{
			if (propagate (i))
			{
				if (verbose_)
				{
					cout << "return UNSAT from propagate found at frame " << i << endl;
					print ();
				}
				return true;
			}
		}
		if (verbose_)
			cout << "end propagate " << endl;
		return false;
	}
	
	bool Checker::propagate (int pos)
	{
		Frame &frame = F_[pos];
		int sz = frame.size ();
		for (int i = propagate_start_[pos]; i < sz; i ++)
		{
			if (!solve_with (frame[i], pos))
			{
				push_to_frame (frame[i], pos+1);
				propagate_start_[pos] = propagate_start_[pos] + 1;
			}
			else
			{
				Cube cu = frame[i];
				for (int j = i; j < frame.size ()-1; j++)
					frame[j] = frame[j+1];
				frame[frame.size ()-1] = cu;
				sz --;
				i --;
			}
		}
		propagate_start_[pos] = sz;
		//if (sz == frame.size ())
			//return true;
		return false;
	}
	
	
	
	
	//////////////helper functions/////////////////////////////////////////////
	Checker::Checker (Model* model, Statistics& stats, double ratio, bool forward, bool inv_next, bool propagate, bool evidence, bool verbose, bool intersect, bool minimal_uc, bool detect_dead_state, bool relative, bool relative_full)
	{
	    
		model_ = model;
		reduce_ratio_ = ratio;
		stats_ = &stats;
		solver_ = NULL;
		start_solver_ = NULL;
		inv_solver_ = NULL;
		init_ = new State (model_->init ());
		last_ = NULL;
		forward_ = forward;
		safe_reported_ = false;
		minimal_uc_ = minimal_uc;
		evidence_ = evidence;
		verbose_ = verbose;
		detect_dead_state_ = detect_dead_state;
		relative_ = relative;
		relative_full_ = relative_full;
		minimal_update_level_ = F_.size ()-1;
		propagate_ = propagate;
		intersect_ = intersect;
		inv_next_ = inv_next;
	}
	Checker::~Checker ()
	{
		if (init_ != NULL)
		{
			delete init_;
			init_ = NULL;
		}
		if (last_ != NULL)
		{
		    delete last_;
		    last_ = NULL;
		}
		//car_finalization ();
	}
	
	void Checker::destroy_states ()
	{    
	    for (int i = 0; i < B_.size (); i ++)
	    {
	        for (int j = 0; j < B_[i].size (); j ++)
	        {
	        	if (B_[i][j] != NULL)
	        	{
	            	delete B_[i][j];
	            	B_[i][j] = NULL;
	            }
	        }
	    }
	    B_.clear ();
	}
	
	void Checker::car_initialization ()
	{
	    solver_ = new MainSolver (model_, stats_, reduce_ratio_, verbose_);
		start_solver_ = new StartSolver (model_, bad_, forward_, verbose_);
		assert (F_.empty ());
		assert (FC_.empty ());
		assert (B_.empty ());
		
	}
	
	void Checker::car_finalization ()
	{
	    F_.clear ();
	    propagate_start_.clear ();
	    FC_.clear ();
	    destroy_states ();
	    delete solver_;
	    solver_ = NULL;
	    delete start_solver_;
	    start_solver_ = NULL;
	}
	
	
	bool Checker::immediate_satisfiable ()
	{
	    stats_->count_main_solver_SAT_time_start ();
	    bool res = solver_->solve_with_assumption (init_->s (), bad_);
	    stats_->count_main_solver_SAT_time_end ();
	    if (res)
	    {
	        Assignment st = solver_->get_model ();
	        std::pair<Assignment, Assignment> pa = state_pair (st);
	        if (forward_)
	            init_->set_inputs (pa.first);
	        else
	            last_ = new State (NULL, pa.first, pa.second, forward_, true);
	        
	        return true;
	    }

	    return false;
	}
	
	void Checker::initialize_sequences ()
	{
		Frame frame;
		FrameCounter fc;
	    if (forward_)
		{
		    for (int i = 0; i < init_->size (); i ++)
		    {
		        Cube cu;
		        cu.push_back (-init_->element (i));
		        frame.push_back (cu);
		        fc.push_back (0);
		    }
		}
		else
		{
			bool con;
		    Cube cu = solver_->get_conflict (bad_);
	        if (cu.empty ())
	        {
	             report_safe ();
	             return;
	        }
	        frame.push_back (cu);
	        fc.push_back (0);
		}
		F_.push_back (frame);
		propagate_start_.push_back (0);
		FC_.push_back (fc);
		solver_->add_new_frame (frame, F_.size()-1, forward_);
	}
	
		
	State* Checker::enumerate_start_state ()
	{
		while (true)
		{
	    	stats_->count_start_solver_SAT_time_start ();
	    	bool val = start_solver_->solve_with_assumption ();
	    	stats_->count_start_solver_SAT_time_end ();
			if (val)  
			{
				State* res = get_new_start_state ();
				if (detect_dead_state_)
		    	{	
		        	if (dead_state (res))
		       	 	{
		            	stats_->count_detect_dead_state_success ();
		            	bool con;
		            	Cube cu = solver_->get_conflict (forward_, minimal_uc_, con);
		            	update_constraint (cu);
		            	delete res;
		            	if (safe_reported ())
		            		return NULL;
		            	continue;
		        	}
		    	}
				return res;
			}
			else
				break;
		}
		
		return NULL;
	}
	
	State* Checker::get_new_start_state ()
	{
		Assignment st = start_solver_->get_model ();
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State *res = new State (NULL, pa.first, pa.second, forward_, true);
		if (detect_dead_state_)
		    res->set_detect_dead_start (constraints_.size ());
		return res;
	}
	
	std::pair<Assignment, Assignment> Checker::state_pair (const Assignment& st)
	{
	    assert (st.size () >= model_->num_inputs () + model_->num_latches ());
	    Assignment inputs, latches;
	    for (int i = 0; i < model_->num_inputs (); i ++)
	        inputs.push_back (st[i]);
	    for (int i = model_->num_inputs (); i < st.size (); i ++)
	    {
	        if (abs (st[i]) > model_->num_inputs () + model_->num_latches ())
	            break;
	        latches.push_back (st[i]);
	    }
	    return std::pair<Assignment, Assignment> (inputs, latches);
	}
	
	
	
	bool Checker::immediate_satisfiable (const State* s)
	{
	    if (forward_)
	    {//s is actually the initial state
	    	init_->set_inputs (const_cast<State*> (s)->inputs_vec ());
	    	init_->set_next (const_cast<State*> (s)->next ());
	        return true;
	    }
	    else
	    {
	        stats_->count_main_solver_SAT_time_start ();
	        bool res = solver_->solve_with_assumption (const_cast<State*> (s)-> s(), bad_);
	        stats_->count_main_solver_SAT_time_end ();
	        if (res)
	        {//s is actually the last_ state
	            Assignment st = solver_->get_model ();
	            std::pair<Assignment, Assignment> pa = state_pair (st);
	            const_cast<State*> (s)->set_last_inputs (pa.first);
	            last_ = new State (const_cast<State*>(s));
	            return true;
	        }
	        return false;
	    }
	}
	
	//a copy for cube
	bool Checker::immediate_satisfiable (const Cube& cu)
	{
	    if (forward_)
	    {
	        return true;
	    }
	    else
	    {
	        stats_->count_main_solver_SAT_time_start ();
	        bool res = solver_->solve_with_assumption (cu, bad_);
	        stats_->count_main_solver_SAT_time_end ();
	        return res;
	    }
	}
	
	bool Checker::invariant_found (int frame_level)
	{
		if (frame_level == 0)
			return false;
		bool res = false;
		create_inv_solver ();
		for (int i = 0; i < frame_level; i ++)
		{
			if (invariant_found_at (i))
			{
				res = true;
				//delete frames after i, and the left F_ is the invariant
				while (F_.size () > i+1)
				{
					F_.pop_back ();
					propagate_start_.pop_back ();
				}
				break;
			}
		}
		delete_inv_solver ();
		return res;
	}
	
	//irrelevant with the direction, so don't care forward or backward
	bool Checker::invariant_found_at (const int frame_level) 
	{
		if (inv_next_)
		{
			inv_solver_add_constraint_or (frame_level);
			if (frame_level <= minimal_update_level_)
				return false;
			inv_solver_add_constraint_and (frame_level);
			stats_->count_inv_solver_SAT_time_start ();
			bool res = !inv_solver_->solve_with_assumption ();
			stats_->count_inv_solver_SAT_time_end ();
			inv_solver_release_constraint_and ();
			return res;
		}
		else
		{
			if (frame_level <= minimal_update_level_)
			{
				inv_solver_add_constraint_or (frame_level);
				return false;
			}
			inv_solver_add_constraint_and (frame_level);
			stats_->count_inv_solver_SAT_time_start ();
			bool res = !inv_solver_->solve_with_assumption ();
			stats_->count_inv_solver_SAT_time_end ();
			inv_solver_release_constraint_and ();
			inv_solver_add_constraint_or (frame_level);
			return res;
		}
	}
	
	
	void Checker::inv_solver_add_constraint_or (const int frame_level)
	{
		//add \bigcup F_i (\bigcup B_i)
		inv_solver_->add_constraint_or (F_[frame_level], inv_next_, forward_);
	}
	
	void Checker::inv_solver_add_constraint_and (const int frame_level)
	{
		//add \neg F_{frame_level} (\neg B_{frame_level})
		inv_solver_->add_constraint_and (F_[frame_level], inv_next_, forward_);
	}
	
	void Checker::inv_solver_release_constraint_and ()
	{
		inv_solver_->release_constraint_and ();
	}
	
	bool Checker::solve_with (const Cube& s, const int frame_level)
	{
		if (frame_level == -1)
			return immediate_satisfiable (s);
				
		solver_->set_assumption (s, frame_level, forward_);
		stats_->count_main_solver_SAT_time_start ();
		bool res = solver_->solve_with_assumption ();
		stats_->count_main_solver_SAT_time_end ();
		
		return res;
	}
	
	State* Checker::get_new_state (const State* s)
	{
		Assignment st = solver_->get_state (forward_, partial_state_);
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State* res = new State (s, pa.first, pa.second, forward_);
		if (detect_dead_state_)
		    res->set_detect_dead_start (constraints_.size ());
		
		return res;
	}
	
	
	void Checker::extend_F_sequence ()
	{
		F_.push_back (frame_);
		propagate_start_.push_back (0);
		FrameCounter fc;
		for (int i = 0; i < frame_.size (); i ++)
			fc.push_back (0);
		FC_.push_back (fc);
		solver_->add_new_frame (frame_, F_.size()-1, forward_);
	}
	
	void Checker::update_B_sequence (const State* s, const int frame_level)
	{
	    while (int (B_.size ()) <= frame_level)
	    {
	        vector<State*> v;
	        B_.push_back (v);
	    }
	    B_[frame_level].push_back (const_cast<State*> (s));
	}
	
	void Checker::update_F_sequence (const State* s, const int frame_level)
	{	
		bool constraint = false;
		Cube cu = solver_->get_conflict (forward_, minimal_uc_, constraint);
			
		//pay attention to the size of cu!
		if (cu.empty ())
		{
			report_safe ();
			return;
		}
		
		if (constraint)
		{
			if (intersect_)
				update_constraint (cu, s);
			else
				update_constraint (cu);
		}
		else
		{
			if (intersect_)
				push_to_frame (cu, frame_level, s);
			else
			{
				push_to_frame (cu, frame_level);
				if (relative_ && frame_level < int (F_.size ()))
					update_frame_by_relative (s, frame_level);
			}
		}

		
	}
	
	void Checker::update_frame_by_relative (const State* s, const int frame_level)
	{
		if (verbose_)
			cout << "start update_frame_by_relative" << endl;
		Cube cu = const_cast<State*> (s)->s();
		while (true)
		{
			if (solve_with (cu, frame_level))
			{
				State *s = get_new_state (NULL);
				assert (s != NULL);
				Cube cu2 = s->intersect (cu);
				delete s;
				if (cu2.empty ())
					break;
				if (!solve_with (cu2, frame_level-1))
				{
					bool constraint = false;
					Cube cu3 = solver_->get_conflict (forward_, minimal_uc_, constraint);
					if (cu3.empty ())
					{
						report_safe ();
						break;
					}
					if (constraint)
					{
						update_constraint (cu3);
						break;
					}
					push_to_frame (cu3, frame_level);
					assert (cu.size () > cu2.size ());
					cu = cu2;
				}
				else
					break;
			}
			else
			{
				bool constraint = false;
				Cube cu3 = solver_->get_conflict (forward_, minimal_uc_, constraint);
				if (cu3.empty ())
				{
					report_safe ();
					break;
				}
				if (constraint)
				{
					update_constraint (cu3);
					break;
				}
				push_to_frame (cu3, frame_level+1);
				break;
			}
		}
		if (verbose_)
			cout << "end update_frame_by_relative" << endl;
	}
	
	Cube Checker::cube_intersection (const State *s, Cube& cu, const int frame_level)
	{
		Cube res = cu;
		if (verbose_ && intersect_)
		{
			cout << "before intersection, cube is" << endl;
			car::print (cu);
		}
		if (s != NULL)
		{
			State *st = const_cast<State*> (s);
			Cube& cu2 = intersect_of (frame_level);
			cu2 = st->intersect (cu2);
			if (cu2.empty ())
			{
				cu2 = st->s();
			}
			else if (!solve_with (cu2, frame_level-1))
			{
				bool constraint;
				res = solver_->get_conflict (forward_, minimal_uc_, constraint);
			}
			else
			{
				cu = st->s();
			}		
		}
		if (verbose_ && intersect_)
		{
			cout << "after intersection, cube is" << endl;
			car::print (res);
		}
		return res;
	}
	
	void Checker::push_to_frame (Cube& cu2, const int frame_level, const State* s)
	{
		
		Cube cu = cube_intersection (s, cu2, frame_level);
		Frame& frame = (frame_level < int (F_.size ())) ? F_[frame_level] : (frame_level == int (F_.size ()) ? frame_ : frame2_);
		
		//To add \@ cu to \@ frame, there must be
		//1. \@ cu does not imply any clause in \@ frame
		//2. if a clause in \@ frame implies \@ cu, replace it by \@cu
		Frame tmp_frame;
		stats_->count_clause_contain_time_start ();
		for (int i = 0; i < frame.size (); i ++)
		{   
		
			if (!imply (frame[i], cu))
				tmp_frame.push_back (frame[i]);	
			else if (frame_level < int (F_.size ()))
			{
				if (propagate_start_[frame_level] > i)
					propagate_start_[frame_level] = propagate_start_[frame_level] - 1;
			}
		} 
		stats_->count_clause_contain_time_end ();
		tmp_frame.push_back (cu);
		frame = tmp_frame;
		
		if (frame_level < int (F_.size ()))
			solver_->add_clause_from_cube (cu, frame_level, forward_);
		else if (frame_level == int (F_.size ()))
			start_solver_->add_clause_with_flag (cu);
		
		//frame.push_back (cu);
	}
	
	//it is not useful, because the successful attempts are very small
	void Checker::add_reduced_uc (Cube& cu, int frame_level)
	{
		Frame& frame = (frame_level < F_.size ()) ? F_[frame_level] : frame_;
		FrameCounter& counter = (frame_level < F_.size ()) ? FC_[frame_level] : fc_;
		assert (frame.size () == counter.size ());
		bool success = false;
		for (int i = 0; i < frame.size (); i ++)
		{
			if (counter[i] >= MAX_COUNT)
				continue;
			if (frame[i].size () == 1)
				continue;
			//stats_->count_clause_contain_time_start ();
			Cube inter_cu = vec_intersect (frame[i], cu);
			//stats_->count_clause_contain_time_end ();
			if (inter_cu.size () == frame[i].size ()) //inter_cu is frame[i] itself
				continue;
			if (inter_cu.size () == 0)
				continue;
			bool res = false;
			if (frame_level-1 == -1)
			{
				//stats_->count_main_solver_SAT_time_start ();
	        	res = solver_->solve_with_assumption (inter_cu, bad_);
	        	//stats_->count_main_solver_SAT_time_end ();
			}
			else 
				res = solve_with (inter_cu, frame_level-1);
			//stats_->add_intersect_solve_number ();
			if (!res)
			{
			    //stats_->add_intersect_solve_success_number ();
			    bool con;
				Cube res_cu = solver_->get_conflict (forward_, minimal_uc_, con);
				if (res_cu.empty ())
				{
					report_safe ();
					return; 
				}
				frame[i] = res_cu;
				counter[i] = 0;
				success = true;
				
				if (frame_level < int (F_.size ()))
					solver_->add_clause_from_cube (res_cu, frame_level, forward_);
				else
					start_solver_->add_clause_with_flag (res_cu);
			}
			else
			{
				counter[i] = counter[i] + 1;
			}
		}
		if (!success)
		{
			frame.push_back (cu);
			counter.push_back (0);
			if (frame_level < int (F_.size ()))
				solver_->add_clause_from_cube (cu, frame_level, forward_);
			else
				start_solver_->add_clause_with_flag (cu);
		}
		return;
	}
	
	int Checker::get_new_level (const State *s, const int frame_level)
	{
	    for (int i = 0; i < frame_level; i ++)
	    {
	        int j = 0;
	        for (; j < F_[i].size (); j ++)
	        {
	            if (s->imply (F_[i][j]))
	                break;
	        }
	        if (j >= F_[i].size ())
	            return i-1;
	    }
		return frame_level - 1;
	}
	
	bool Checker::tried_before (const State* st, const int frame_level)
	{
		//first check whether st is in constraints_
		for (int i = 0; i < constraints_.size (); i ++)
		{
			if (st->imply (constraints_[i]))
				return true;
		}
		//
	    assert (frame_level >= 0);
	    Frame &frame = (frame_level < F_.size ()) ? F_[frame_level] : frame_;
	    //assume that st is a full state
	    assert (const_cast<State*>(st)->size () == model_->num_latches ());
	    
	    stats_->count_state_contain_time_start ();
	    for (int i = 0; i < frame.size (); i ++)
	    {
	        if (st->imply (frame[i]))
	        {
	            stats_->count_state_contain_time_end ();
	            return true;
	        } 
	    }
	    stats_->count_state_contain_time_end ();
	    
	    return false;
	}
	
	void Checker::update_constraint (Cube& cu, const State* s)
	{
		State *st = const_cast<State*> (s);
	    if (cu.empty ())
	    {
	        report_safe ();
	        return;
	    }
	    Cube to_add = cu;
	    if (s != NULL)
	    {
	    	constraint_intersect_ = st->intersect (constraint_intersect_);
	    	if (constraint_intersect_.empty ())
	    		constraint_intersect_ = st->s();
	    	else if (!solve_with (constraint_intersect_, -2))
	    	{
	    		bool constraint = false;
	    		to_add = solver_->get_conflict (forward_, minimal_uc_, constraint);
	    	}
	    	else
	    	{
	    		constraint_intersect_ = st->s();
	    	}
	    }
	    constraints_.push_back (to_add);
	    model_->update_constraint (to_add);
	    //cu will be updated in model_->update_constraint 
	    start_solver_->update_constraint (to_add);
	    solver_->update_constraint (to_add);
    }
    
    void Checker::remove_dead_states ()
    {
        for (int i = 0; i < B_.size (); i ++)
	    {
	        vector<State*> tmp;
	        for (int j = 0; j < B_[i].size (); j ++)
	        {
	            int k = B_[i][j]->detect_dead_start ();
	            //if (k == constraints_.size ())
	                //continue;
	            for (; k < constraints_.size (); k ++)
	            {
	                if (B_[i][j]->imply (constraints_[k]))
	                    break;
	            }
	        	if (k == constraints_.size ())
	        	{
	        	    B_[i][j]->set_detect_dead_start (constraints_.size ());
	        	    tmp.push_back (B_[i][j]);
	        	    
	        	}
	        	else
	        	    delete B_[i][j];
	        }
	        B_[i] = tmp;
	    }
    }
    
    Cube Checker::relative_cube (const State* s, const int frame_level)
    {
    	bool constraint;
    	Cube back_up_cu = solver_->get_conflict (forward_, minimal_uc_, constraint);
    	Cube cu = relative_full_ ? const_cast<State*>(s)->s () : back_up_cu;
    	if (cu.empty ())
    		return cu;	
    	Cube cu2;
    	while (true)
    	{
    		solver_->add_clause_from_cube (cu, frame_level, forward_);
    		if (solve_with (cu, frame_level))
    		{
    			cu2 = cube_intersect (cu, solver_->get_model ());
    			if (cu2.empty ())
    				break;
    			if (!solve_with (cu2, frame_level-1))
    			{
    				bool con = false;
    				back_up_cu = solver_->get_conflict (forward_, minimal_uc_, con);
    				cu = relative_full_ ? cu2 : back_up_cu;
    			}
    			else
    				break;
    		}
    		else
    		{
    			bool con = false;
    			back_up_cu = solver_->get_conflict (forward_, minimal_uc_, con);
    			//push_to_frame (back_up_cu, frame_level);
    			push_to_frame (back_up_cu, frame_level+1);
    			break;
    		}
    	}
    	return back_up_cu;
    }
	
	void Checker::print_evidence (ofstream& out)
	{
		if (forward_)
			init_->print_evidence (forward_, out);
		else
			last_->print_evidence (forward_, out);
	}
		
}
