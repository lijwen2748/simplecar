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
    bool Checker::check (std::ofstream& out){
	    for (int i = 0; i < model_->num_outputs (); i ++){
	        bad_ = model_->output (i);
	        
	        //for the particular case when bad_ is true or false
	        if (bad_ == model_->true_id ()){
	        	out << "1" << endl;
	        	out << "b" << i << endl;
	        	if (evidence_){
	        	    //print init state
	        	    out << init_->latches() << endl;
	        	    //print an arbitary input vector
	        	    for (int j = 0; j < model_->num_inputs (); j ++)
	        	        out << "0";
	        	    out << endl;
	        	}
	        	out << "." << endl;
	        	if (verbose_){
	        		cout << "return SAT since the output is true" << endl;
	        	}
	        	return true;
	        }
	        else if (bad_ == model_->false_id ()){
	        	out << "0" << endl;
	        	out << "b" << endl;
	        	out << "." << endl;
	        	if (verbose_){
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
	
	bool Checker::car_check (){
		if (verbose_)
			cout << "start check ..." << endl;
		if (immediate_satisfiable ()){
			if (verbose_)
				cout << "return SAT from immediate_satisfiable" << endl;
			return true;
		}

		initialize_sequences ();
			
		int frame_level = 0;
		while (true){
		    cout << "Frame " << frame_level << endl;
		    //print the number of clauses in each frame
		    for (int i = 0; i < F_.size (); i ++) {
		    	cout << F_[i].size () << " ";
		    }
		    cout << endl;
		    //end of print
		    
		    //handle the special start states
			reset_start_solver ();
			if (!propagate_)
		    	clear_frame ();
			minimal_update_level_ = F_.size () - 1;
			if (try_satisfy (frame_level)){
				if (verbose_)
					cout << "return SAT from try_satisfy at frame level " << frame_level << endl;
				return true;
			}
			//it is true when some reason returned from Main solver is empty
			if (safe_reported ()){
				if (verbose_)
					cout << "return UNSAT from safe reported" << endl;
				return false;
			}
			extend_F_sequence ();
			
			if (propagate_){
				clear_frame ();
				if (propagate ())
					return false;
			}
			
			frame_level ++;
			
			if (invariant_found (frame_level+1)){
				if (verbose_){
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
			if (try_satisfy_by (frame_level, s))
			    return true;
			if (safe_reported ())
				return false;
		    s = enumerate_start_state ();
		}
	
		return false;
	}
	
	/*Main function to do state search in CAR
	* Input:
	*       frame_level: The frame level currently working on
	* Output:
	*       1: a counterexample is found
	*       0: The safe result is reported
	*       -1: else
	*/
	int Checker::do_search (const int frame_level) {	
		//erase dead states
		for (int i = B_.size()-1; i >= 0; --i){
			for (int j = 0; j < B_[i].size(); ++j){
				if (B_[i][j]->is_dead()){
					State* s = B_[i][j];
					B_[i].erase (B_[i].begin()+j);
					delete s;
					j --;
				}
			}
		}
		//end of erase
		
		if (begin_) {
			vector<State*> states;
			for (int i = 0; i < B_.size (); ++ i) {
				for (int j = 0; j < B_[i].size (); ++ j) 
					states.push_back (B_[i][j]);
			}
			for (int i = 0; i < states.size (); ++ i) {
				if (try_satisfy_by (frame_level, states[i]))
			    	return 1;
				if (safe_reported ())
					return 0;
			}
		}
	
		if (end_) {
	    	for (int i = B_.size () - 1; i >= 0; -- i) {
	        	for (int j = 0; j < B_[i].size (); ++ j) {
			    	if (try_satisfy_by (frame_level, B_[i][j]))
			        	return 1;
					if (safe_reported ())
				    	return 0;
			    }
		    }
		}
		   
		return -1;
	}
	
	bool Checker::try_satisfy_by (int frame_level, State* s)
	{
		if (tried_before (s, frame_level+1))
			return false;
		
		//if (frame_level < minimal_update_level_)
			//minimal_update_level_ = frame_level;
		
		bool all_predeccessor_dead = true; 
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
			    /*
			    cout << "frame " << frame_level << ":" << endl;
			    cout << "s: " << endl;
			    car::print (s->s());
			    cout << "new state:" << endl;
			    car::print (new_state->s());
			    */
			    
			    
			    //////generate dot data
			    if (dot_ != NULL)
			        (*dot_) << "\n\t\t\t" << const_cast<State*> (s)->id () << " -- " << new_state->id ();
			    //////generate dot data
			    
			    int new_level = get_new_level (new_state, frame_level);

			    update_B_sequence (new_state);
			    
			    if (try_satisfy_by (new_level, new_state))
				    return true;
				if (safe_reported ())
				    return false;
				    
				if (!new_state->is_dead ())
					all_predeccessor_dead = false;
					
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
		
		if (all_predeccessor_dead){
			Cube dead_uc;
			if (is_dead (s, dead_uc)){
				//cout << "dead: " << endl;
				//car::print (dead_uc);
				s->mark_dead ();
				add_dead_to_solvers (dead_uc);
				//if (car::imply (cu, dead_uc))
				return false;
			}
		}

		update_F_sequence (s, frame_level+1);
		if (safe_reported ())
			return false;
		
		frame_level += 1;
		if (frame_level < int (F_.size ()))
		{
		   /*
		    if (s->work_count () >= MAX_TRY) {
		        s->set_work_level (frame_level);
		        states_.push_back (s);
		        return false;
		    }
		    s->work_count_inc ();
		   */
		    return try_satisfy_by (frame_level, s);
		}
		
		return false;
	}
	
	/*************propagation****************/
	bool Checker::propagate (){
		int start = forward_ ? (minimal_update_level_ == 0 ? 1 : minimal_update_level_) : minimal_update_level_;
		for (int i = (start); i < F_.size(); ++i)
			if (propagate (i))
				return true;
		return false;
	}
	
	bool Checker::propagate (int n){
		assert (n >= 0 && n < F_.size());
		Frame& frame = F_[n];
		Frame& next_frame = (n+1 >= F_.size()) ? frame_ : F_[n+1];
		
		bool flag = true;
		for (int i = 0; i < frame.size (); ++i){
			Cube& cu = frame[i];
			
			
			bool propagated = false;
			for (int j = 0; j < next_frame.size(); ++j){
				if (car::imply (cu, next_frame[j]) && car::imply (next_frame[j], cu)){
					propagated = true;
					break;
				}
			}
			if (propagated) continue;
			
	
		    if (propagate (cu, n)){
		    	push_to_frame (cu, n+1);
		    }
		    else
		    	flag = false;
		}
		
		if (flag)
			return true;
		return false;
	}
	
	bool Checker::propagate (Cube& cu, int n){
		solver_->set_assumption (cu, n, forward_);
		//solver_->print_assumption();
		//solver_->print_clauses();
	    stats_->count_main_solver_SAT_time_start ();
		bool res = solver_->solve_with_assumption ();
		stats_->count_main_solver_SAT_time_end ();
		if (!res)
			return true;
		return false;
	}
	
		
	//////////////helper functions/////////////////////////////////////////////

	Checker::Checker (Model* model, Statistics& stats, ofstream* dot, bool forward, bool evidence, bool partial, bool propagate, bool begin, bool end, bool inter, bool rotate, bool verbose, bool minimal_uc)
	{
	    
		model_ = model;
		stats_ = &stats;
		dot_ = dot;
		solver_ = NULL;
		lift_ = NULL;
		dead_solver_ = NULL;
		start_solver_ = NULL;
		inv_solver_ = NULL;
		init_ = new State (model_->init ());
		last_ = NULL;
		forward_ = forward;
		safe_reported_ = false;
		minimal_uc_ = minimal_uc;
		evidence_ = evidence;
		verbose_ = verbose;
		minimal_update_level_ = F_.size ()-1;
		solver_call_counter_ = 0;
		start_solver_call_counter_ = 0; 
		partial_state_ = partial;
		dead_flag_ = false;
		//set propagate_ to be true by default
		propagate_ = propagate;
		
		begin_ = begin;
		end_ = end;
		inter_ = inter;
		rotate_ = rotate;
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
		car_finalization ();
	}
	
	void Checker::destroy_states ()
	{    
	    for (int i = 0; i < B_.size (); i ++)
	    {
	    	//cout << "B[" << i << "]:" <<endl;
	        for (int j = 0; j < B_[i].size (); j ++)
	        {
	        	if (B_[i][j] != NULL)
	        	{
	        		//car::print (B_[i][j]->s());
	            	delete B_[i][j];
	            	B_[i][j] = NULL;
	            }
	        }
	    }
	    B_.clear ();
	}
	
	void Checker::car_initialization ()
	{
	    solver_ = new MainSolver (model_, stats_, verbose_);
	    if (forward_){
	    	lift_ = new MainSolver (model_, stats_, verbose_);
	    	dead_solver_ = new MainSolver (model_, stats_, verbose_);
	    	dead_solver_->add_clause (-bad_);
	    }
		start_solver_ = new StartSolver (model_, bad_, forward_, verbose_);
		assert (F_.empty ());
		assert (B_.empty ());
		
	}
	
	void Checker::car_finalization ()
	{
	/*
		for (int i = 0; i < F_.size(); ++i){
			cout << "Frame " << i << endl;
			for (int j = 0; j < F_[i].size(); ++j)
				car::print (F_[i][j]);
		}
		*/
		
	    F_.clear ();
	    destroy_states ();
	    if (solver_ != NULL) {
	        delete solver_;
	        solver_ = NULL;
	    }
	    if (lift_ != NULL) {
	        delete lift_;
	        lift_ = NULL;
	    }
	    if (dead_solver_ != NULL) {
	        delete dead_solver_;
	        dead_solver_ = NULL;
	    }
	    if (start_solver_ != NULL) {
	        delete start_solver_;
	        start_solver_ = NULL;
	    }
	}
	
	
	bool Checker::immediate_satisfiable ()
	{
	    bool res = solver_solve_with_assumption (init_->s (), bad_);
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
	    if (forward_)
		{
		    for (int i = 0; i < init_->size (); i ++)
		    {
		        Cube cu;
		        cu.push_back (-init_->element (i));
		        frame.push_back (cu);
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
		comms_.push_back (cu);
		}
		F_.push_back (frame);
		Cube& cu = init_->s();
		cubes_.push_back (cu);
		solver_->add_new_frame (frame, F_.size()-1, forward_);
	}
	
		
	State* Checker::enumerate_start_state ()
	{
		while (true)
		{
			//start_solver_->print_assumption ();
	    	//start_solver_->print_clauses ();
	    	bool val = start_solver_solve_with_assumption ();

			if (val)  
			{
				State* res = get_new_start_state ();
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
		assert (st.size() >= model_->num_inputs() + model_->num_latches());
		st.resize (model_->num_inputs() + model_->num_latches());
		if (partial_state_)
			get_partial (st);
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State *res = new State (NULL, pa.first, pa.second, forward_, true);
		return res;
	}
	
	std::pair<Assignment, Assignment> Checker::state_pair (const Assignment& st)
	{
		Assignment inputs, latches;
		if (!partial_state_){
	    	assert (st.size () >= model_->num_inputs () + model_->num_latches ());
	    	for (int i = 0; i < model_->num_inputs (); i ++)
	        	inputs.push_back (st[i]);
	    	for (int i = model_->num_inputs (); i < st.size (); i ++)
	    	{
	        	if (abs (st[i]) > model_->num_inputs () + model_->num_latches ())
	            	break;
	        	latches.push_back (st[i]);
	    	}
	    }
	    else{
	    	for (auto it = st.begin(); it != st.end (); ++it){
	    		if (abs(*it) <= model_->num_inputs ())
	    			inputs.push_back (*it);
	    		else if (abs(*it) <= model_->num_inputs () + model_->num_latches ())
	    			latches.push_back (*it);
	    	}
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
	        bool res = solver_solve_with_assumption (const_cast<State*> (s)-> s(), bad_);
	        if (res)
	        {//s is actually the last_ state
	            Assignment st = solver_->get_model ();
	            std::pair<Assignment, Assignment> pa = state_pair (st);
	            const_cast<State*> (s)->set_last_inputs (pa.first);
	            last_ = new State (const_cast<State*>(s));
	            last_->set_final (true);
	            //////generate dot data
	            if (dot_ != NULL)
	                (*dot_) << "\n\t\t\t" << last_->id () << " [shape = circle, color = red, label = \"final\", size = 0.01];";
	            //////generate dot data
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
	        bool res = solver_solve_with_assumption (cu, bad_);
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
					F_.pop_back ();
				//cout << "invariant found at frame " << i << endl;
				break;
			}
		}
		delete_inv_solver ();
		return res;
	}
	
	//irrelevant with the direction, so don't care forward or backward
	bool Checker::invariant_found_at (const int frame_level) 
	{

		if (frame_level <= minimal_update_level_){
			inv_solver_add_constraint_or (frame_level);
			return false;
		}
		inv_solver_add_constraint_and (frame_level);

		//inv_solver_->print_assumption ();
		//inv_solver_->print_clauses();	
		stats_->count_inv_solver_SAT_time_start ();
		bool res = !inv_solver_->solve_with_assumption ();
		stats_->count_inv_solver_SAT_time_end ();
		inv_solver_release_constraint_and ();
		inv_solver_add_constraint_or (frame_level);
		return res;
	}
	
	
	void Checker::inv_solver_add_constraint_or (const int frame_level)
	{
		//add \bigcup F_i (\bigcup B_i)
		inv_solver_->add_constraint_or (F_[frame_level], forward_);
	}
	
	void Checker::inv_solver_add_constraint_and (const int frame_level)
	{
		//add \neg F_{frame_level} (\neg B_{frame_level})
		inv_solver_->add_constraint_and (F_[frame_level], forward_);
	}
	
	void Checker::inv_solver_release_constraint_and ()
	{
		inv_solver_->release_constraint_and ();
	}
	
	bool Checker::solve_with (const Cube& s, const int frame_level)
	{
		if (frame_level == -1)
			return immediate_satisfiable (s);
				
		bool res = solver_solve_with_assumption (s, frame_level, forward_);
		
		return res;
	}
	
	bool Checker::solve_for_recursive (Cube& s, int frame_level, Cube& tmp_block){
		assert (frame_level != -1);
		
		return solver_->solve_with_assumption_for_temporary (s, frame_level, forward_, tmp_block);
				
	}
	
	State* Checker::get_new_state (const State* s)
	{
		Assignment st = solver_->get_state (forward_, partial_state_);
		//st includes both input and latch parts
		if (partial_state_)
			get_partial (st, s);
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State* res = new State (s, pa.first, pa.second, forward_);
		
		return res;
	}
	
	void Checker::get_partial (Assignment& st, const State* s){
		if (!forward_) 
			return;
		Cube assumption = st;
		if (s != NULL){
			Cube& cube = s->s();
			Clause cl;
			for (auto it = cube.begin(); it != cube.end(); ++it)
				cl.push_back (-model_->prime (*it));
			int flag = lift_->new_flag ();
			cl.push_back (flag);
			lift_->add_clause (cl);
		
			assumption.push_back (-flag);
			bool ret = lift_->solve_with_assumption (assumption);
			//lift_->print_assumption ();
			//lift_->print_clauses ();
		
			assert (!ret);
			bool constraint = false;
			st = lift_->get_conflict (!forward_, minimal_uc_, constraint);
			if (st.empty()){
			//every state can reach s, thus make st the initial state.
				st = init_->s();
				return;
			}
			
		///?????????????????
			lift_->add_clause (-flag);	
			//lift_->print_clauses ();
		}
		else{
			assumption.push_back (-bad_);
			//lift_->print_clauses();
			bool ret = lift_->solve_with_assumption (assumption);
			assert (!ret);
			bool constraint = false;
			st = lift_->get_conflict (!forward_, minimal_uc_, constraint);
		
			//remove -bad_
			for (auto it = st.begin(); it != st.end(); ++it){
				if (*it == -bad_){
					st.erase (it);
					break;
				}
			}
			
			assert (!st.empty());
		}
	}
	
	
	void Checker::extend_F_sequence ()
	{
		F_.push_back (frame_);
		cubes_.push_back (cube_);
		comms_.push_back (comm_);
		solver_->add_new_frame (frame_, F_.size()-1, forward_);
	}
	
	void Checker::update_B_sequence (State* s)
	{
	    while (int (B_.size ()) <= s->depth ())
	    {
	        vector<State*> v;
	        B_.push_back (v);
	    }
	    B_[s->depth ()].push_back (s);
	}
	
	void Checker::update_F_sequence (const State* s, const int frame_level)
	{	
		bool constraint = false;
		Cube cu = solver_->get_conflict (forward_, minimal_uc_, constraint);
		
		/*
		Cube dead_uc;
		if (is_dead (s, dead_uc)){
			//cout << "dead: " << endl;
			//car::print (dead_uc);
			add_dead_to_solvers (dead_uc);
			//if (car::imply (cu, dead_uc))
				return;
		}
		*/
		
		
		//foward cu MUST rule out those not in \@s
		if (forward_){
			Cube tmp;
			Cube &st = s->s();
			if (!partial_state_){
				for(auto it = cu.begin(); it != cu.end(); ++it){
					int latch_start = model_->num_inputs()+1;
					if (st[abs(*it)-latch_start] == *it)
						tmp.push_back (*it);
				}
			}
			else{
				hash_set<int> tmp_set;
				for (auto it = st.begin (); it != st.end(); ++it)
					tmp_set.insert (*it);
				for (auto it = cu.begin(); it != cu.end(); ++it){
					if (tmp_set.find (*it) != tmp_set.end())
						tmp.push_back (*it);
				}
			}
			cu = tmp;
		}
		
		//assert (!cu.empty());
		
		if(cu.empty()){
			report_safe ();
		}
		
		/*
		if (frame_level <= F_.size()){
			Cube next_cu;
			cu = recursive_block (s, frame_level, cu, next_cu);
		}
		*/
		
		//pay attention to the size of cu!
		if (safe_reported ())
		{
			return;
		}
		
		
		if (forward_){
			if (is_initial (cu)){
				auto it = s->s().begin();
				while ((*it) < 0) ++it;
				assert (it != s->s().end());
				int i = 0;
				for (; i < cu.size(); ++i)
					if (abs(cu[i]) > abs(*it))
						break;
				cu.insert (cu.begin()+i, *it);
			}
		}
		
		
		push_to_frame (cu, frame_level);
		
		
		if (forward_){
			for (int i = frame_level-1; i >= 1; --i)
				push_to_frame (cu, i);
		}
		
		
	}
	
	bool Checker::is_dead (const State* s, Cube& dead_uc){
	
		Cube assumption;
		
		Cube common;
		if (deads_.size() > 0) 
			common = car::cube_intersect (deads_[deads_.size()-1], s->s());
			
		for (auto it = common.begin(); it != common.end(); ++it)
			assumption.push_back (forward_ ? model_->prime (*it) : (*it));
			
		for (auto it = s->s().begin(); it != s->s().end(); ++it)
			assumption.push_back (forward_ ? model_->prime (*it) : (*it));
		
		/*
		Cube common;
		if (deads_.size() > 0) 
			common = car::cube_intersect (deads_[deads_.size()-1], s->s());
		for (auto it = common.begin(); it != common.end(); ++it)
			assumption.push_back (forward_ ? model_->prime (*it) : (*it));
		//assumption.insert (assumption.begin (), common.begin (), common.end ());
		*/
		
		
		/*
		if (!s->added_to_dead_solver ()){
			dead_solver_->CARSolver::add_clause_from_cube (s->s());
			s->set_added_to_dead_solver (true);
		}
		*/
			
		bool res = dead_solver_->solve_with_assumption (assumption);
		if (!res){
			bool constraint = false;
			dead_uc = dead_solver_->get_conflict (forward_, minimal_uc_, constraint);
			//foward dead_cu MUST rule out those not in \@s //TO BE REUSED!
			if (forward_){
				Cube tmp;
				Cube &st = s->s();
				if (!partial_state_){
					for(auto it = dead_uc.begin(); it != dead_uc.end(); ++it){
						int latch_start = model_->num_inputs()+1;
						if (st[abs(*it)-latch_start] == *it)
							tmp.push_back (*it);
					}
				}
				else{
					hash_set<int> tmp_set;
					for (auto it = st.begin (); it != st.end(); ++it)
						tmp_set.insert (*it);
					for (auto it = dead_uc.begin(); it != dead_uc.end(); ++it){
						if (tmp_set.find (*it) != tmp_set.end())
							tmp.push_back (*it);
					}
				}
				dead_uc = tmp;
				
				/*
				//shrink dead_uc
				while (dead_uc.size() != assumption.size()){
					assumption.clear ();
					for (auto it = dead_uc.begin(); it != dead_uc.end(); ++it)
						assumption.push_back (forward_ ? model_->prime (*it) : (*it));
						
					dead_solver_->CARSolver::add_clause_from_cube (dead_uc);
					
					res = dead_solver_->solve_with_assumption (assumption);
					assert (!res);
					
					constraint = false;
					Cube last_dead_uc = dead_uc;
					dead_uc = dead_solver_->get_conflict (forward_, minimal_uc_, constraint);
					//foward dead_cu MUST rule out those not in \@s //TO BE REUSED!
					Cube tmp;
					Cube &st = last_dead_uc;
					hash_set<int> tmp_set;
					for (auto it = st.begin (); it != st.end(); ++it)
						tmp_set.insert (*it);
					for (auto it = dead_uc.begin(); it != dead_uc.end(); ++it){
						if (tmp_set.find (*it) != tmp_set.end())
							tmp.push_back (*it);
					}

					dead_uc = tmp;
				}
				*/
			}
			assert (!dead_uc.empty());
		}
		else{
			if (!s->added_to_dead_solver ()){
				dead_solver_->CARSolver::add_clause_from_cube (s->s());
				s->set_added_to_dead_solver (true);
			}
		}
		return !res;
	}
	
	void Checker::add_dead_to_inv_solver (){
		for (auto it = deads_.begin (); it != deads_.end(); ++it){
			Clause cl;	
			for (auto it2 = (*it).begin(); it2 != (*it).end (); ++it2){
				cl.push_back (forward_? -(*it2) : -model_->prime(*it2));
			}
		
			if (is_initial (*it)){
				//create dead clauses : MUST consider the initial state not excluded by dead states!!!
				std::vector<Clause> cls;
				int init_flag = inv_solver_->new_var ();
				int dead_flag = inv_solver_->new_var ();
				if (true){//not consider initial state yet
					Clause cl2;
					
					cl2.push_back (init_flag);
					cl2.push_back (dead_flag);
					cls.push_back (cl2);
					//create clauses for I <- inv_solver_->init_flag
					for (auto it2 = init_->s().begin(); it2 != init_->s().end(); ++it2){
						cl2.clear ();
						cl2.push_back (init_flag);
						cl2.push_back (*it2);
						cls.push_back (cl2);
					}
				}
				//create clauses for !dead <-inv_solver->dead_flag
				cl.push_back (dead_flag);
				cls.push_back (cl);
		
				for (auto it2 = cls.begin(); it2 != cls.end(); ++it2){
					inv_solver_->add_clause (*it2);
				}
			}
			else
				inv_solver_->add_clause (cl);
		}
	}
	
	void Checker::add_dead_to_solvers (Cube& dead_uc){
		std::vector<Cube> tmp_deads;
		for (auto it = deads_.begin (); it != deads_.end (); ++it){
			if (!imply (*it, dead_uc))
				tmp_deads.push_back (*it);
		}
		deads_ = tmp_deads;
		deads_.push_back (dead_uc);
		//car::print (dead_uc);
		
		Clause cl;	
		for (auto it = dead_uc.begin(); it != dead_uc.end (); ++it){
			cl.push_back (forward_? -(*it) : -model_->prime(*it));
		}
		start_solver_->add_clause (cl);
		
		if (is_initial (dead_uc)){
			//create dead clauses : MUST consider the initial state not excluded by dead states!!!
			std::vector<Clause> cls;
			if (!dead_flag_){//not consider initial state yet
				Clause cl2;
				cl2.push_back (solver_->init_flag());
				cl2.push_back (solver_->dead_flag());
				cls.push_back (cl2);
				//create clauses for I <- solver_->init_flag()
				for (auto it = init_->s().begin(); it != init_->s().end(); ++it){
					cl2.clear ();
					cl2.push_back (-solver_->init_flag());
					cl2.push_back (*it);
					cls.push_back (cl2);
				}
				dead_flag_ = true;
			}
			//create clauses for !dead <-solver_->dead_flag()
			cl.push_back (-solver_->dead_flag());
			cls.push_back (cl);
		
			for (auto it = cls.begin(); it != cls.end(); ++it){
				solver_->add_clause (*it);
				lift_->add_clause (*it);
				dead_solver_->add_clause (*it);
			}
		}
		else{
			solver_->add_clause (cl);
			lift_->add_clause (cl);
			dead_solver_->add_clause (cl);
		}
			
	}
	
	
	Cube Checker::recursive_block (State* s, int frame_level, Cube cu, Cube& next_cu){
		
		Cube common = s->s();
		State *tmp_s = new State (common);
		
		while (true){
			
			bool res = solve_for_recursive (common, frame_level, common);
			if (!res){
				next_cu = get_uc(common);
				delete tmp_s;
				return cu;
			}
			State* new_state = get_new_state (tmp_s);
			assert (new_state != NULL);
			common = car::cube_intersect (common, new_state->s());
			delete new_state;
			tmp_s->set_s(common);
			
			if (common.empty()){
				delete tmp_s;
				return cu;
			}
			
			if (is_initial (common)){
				delete tmp_s;
				return cu;
			}
			
			if (solve_with (common, frame_level-1)){
				delete tmp_s;
				return cu;
			}
			
			cu = get_uc (common); 
			
			
		}
		
	}
	
	Cube Checker::get_uc (Cube &c) {
		bool constraint = false;
		Cube cu = solver_->get_conflict (forward_, minimal_uc_, constraint);
		    
		//foward cu MUST rule out those not in \@s
		Cube tmp;
		//Cube &st = s->s();
		for(auto it = cu.begin(); it != cu.end(); ++it){
			if (car::is_in (*it, c, 0, c.size()-1))
				tmp.push_back (*it);
		}
		cu = tmp;
			
		//pay attention to the size of cu!
		if (cu.empty ())
		{
			report_safe ();
			//return cu;
		}
		return cu;
	}

	
	void Checker::push_to_frame (Cube& cu, const int frame_level)
	{
		
		Frame& frame = (frame_level < int (F_.size ())) ? F_[frame_level] : frame_;
		
				
		//To add \@ cu to \@ frame, there must be
		//1. \@ cu does not imply any clause in \@ frame
		//2. if a clause in \@ frame implies \@ cu, replace it by \@cu
		Frame tmp_frame;
		stats_->count_clause_contain_time_start ();
		for (int i = 0; i < frame.size (); i ++)
		{   
			if (forward_){//for incremental
				if (imply (cu, frame[i]))
					return;
			}
			if (!imply (frame[i], cu))
				tmp_frame.push_back (frame[i]);	
			else {
				
			    stats_->count_clause_contain_success ();
			}
		} 
		stats_->count_clause_contain_time_end ();
		tmp_frame.push_back (cu);
		/*
		//update comm
		Cube& comm = (frame_level < int (comms_.size ())) ? comms_[frame_level] : comm_;
		if (comm.empty ())
			comm = cu;
		else {
		        comm = vec_intersect (cu, comm);
		}
		*/
		frame = tmp_frame;
		
		if (frame_level-1 < minimal_update_level_)
			minimal_update_level_ = frame_level;
		
		if (frame_level < int (F_.size ()))
			solver_->add_clause_from_cube (cu, frame_level, forward_);
		else if (frame_level == int (F_.size ()))
			start_solver_->add_clause_with_flag (cu);
	}
	
	
	int Checker::get_new_level (const State *s, const int frame_level){
	    for (int i = 0; i < frame_level; i ++){
	        int j = 0;
	        for (; j < F_[i].size (); j ++){
	        	bool res = partial_state_ ? car::imply (s->s(), F_[i][j]) : s->imply (F_[i][j]);
	            if (res)
	                break;
	        }
	        if (j >= F_[i].size ())
	            return i-1;
	    }
		return frame_level - 1;
	}
	
	bool Checker::tried_before (const State* st, const int frame_level) {
		//check whether st is a dead state	
		if (st->is_dead ()) 
			return true;
		for(auto it = deads_.begin(); it != deads_.end(); ++it){
			bool res = partial_state_ ? car::imply (st->s(), *it) : st->imply (*it);
			res = res && !is_initial (st->s());
			if (res){
				st->mark_dead ();
				return true;
			}
		}
		//end of check
		
	    assert (frame_level >= 0);
	    Frame &frame = (frame_level < F_.size ()) ? F_[frame_level] : frame_;
	    if (!partial_state_){
	    	//assume that st is a full state
	    	assert (const_cast<State*>(st)->size () == model_->num_latches ());
	    
	    	stats_->count_state_contain_time_start ();
	    	for (int i = 0; i < frame.size (); i ++) {
	        	if (st->imply (frame[i])) {
	            	stats_->count_state_contain_time_end ();
	            	return true;
	        	} 
	    	}
	    	stats_->count_state_contain_time_end ();
	    }
	    else{
	    	stats_->count_state_contain_time_start ();
	    	for (int i = 0; i < frame.size (); i ++) {
	        	if (car::imply (st->s(), frame[i])) {
	            	stats_->count_state_contain_time_end ();
	            	return true;
	        	} 
	    	}
	    	stats_->count_state_contain_time_end ();
	    }
	   
	    
	    return false;
	}
	
	
	void Checker::get_previous (const Assignment& st, const int frame_level, std::vector<int>& res) {
	    if (frame_level == -1) return;
	    Frame& frame = (frame_level < F_.size ()) ? F_[frame_level] : frame_;
	    
	    for (int i = frame.size ()-1; i >= 0; --i) {
	        Cube& cu = frame[i];
	        int j = 0;
	        for (; j < cu.size() ; ++ j) {
	    	    if (st[abs(cu[j])-model_->num_inputs ()-1] != cu[j]) {
	    		    break;
	    	    }
	        }
	        if (j >= cu.size ()) { 
	            res = cu;
	            break;
	        }
	    }
	}
	
	//collect priority ids and store in \@ res
	void Checker::get_priority (const Assignment& st, const int frame_level, std::vector<int>& res) {
	    
	    //get_previous (st, frame_level, res);
	    
	    Frame& frame = (frame_level+1 < F_.size ()) ? F_[frame_level+1] : frame_;
	    if (frame.size () == 0)  
	    	return;
	    	
	    Cube& cu = frame[frame.size()-1];
	        
	    std::vector<int> tmp;
	    tmp.reserve (cu.size());
	    if(!forward_){
	    	for (int i = 0; i < cu.size() ; ++ i) {
	    		if (st[abs(cu[i])-model_->num_inputs ()-1] == cu[i]) {
	    			tmp.push_back (cu[i]);
	    		}
	    	}
	    	res = tmp;
	    }
	    else{
	    	res = car::cube_intersect (cu, st);
	    }
	    //res.insert (res.begin (), tmp.begin (), tmp.end ());
	}
	
	//add the intersection of the last UC in frame_level+1 with the state \@ st to \@ st
	void Checker::add_intersection_last_uc_in_frame_level_plus_one (Assignment& st, const int frame_level) {
		/*
	    std::vector<int> tmp;
	    get_priority (st, frame_level, tmp);
	    st.insert (st.begin (), tmp.begin (), tmp.end ());
	    */
	    /*
	    Frame& frame = (frame_level+1 < F_.size ()) ? F_[frame_level+1] : frame_;
	    if (frame.size () == 0)  
	    	return;
	    Cube& cu = frame[frame.size()-1];
	    std::vector<int> tmp, tmp_st;
	    tmp.reserve (st.size());
	    tmp_st.reserve (st.size ());
	    int j = 0;
	    for (int i = 0; i < st.size (); ++ i) {
	        if (j >= cu.size ()) 
	            tmp_st.push_back (st[i]);
	        else {
	            if (abs(st[i]) < abs (cu[j])) {
	                tmp.push_back (st[i]);
	            }
	            else {
	                if (st[i] != cu[j])
	                    tmp.push_back (st[i]);
	                else
	                    tmp_st.push_back (st[i]);
	                ++ j;
	            }
	        }
	    }
	    
	    for (int i = 0; i < tmp.size (); ++ i)
	        tmp_st.push_back (tmp[i]);
	    st = tmp_st;
	    */
	    //if(forward_)
	    	//return;
	    
	    std::vector<int> prefix;
	    if (inter_) 
	    	get_priority (st, frame_level, prefix);	
	    
	    if (rotate_) { 	    
	    std::vector<int> tmp_st, tmp;
	    tmp_st.reserve (st.size());
	    tmp.reserve (st.size());
	    Cube& cube = (frame_level+1 < cubes_.size ()) ? cubes_[frame_level+1] : cube_;
	    if (cube.empty ()) {
	        //cube = st;
	        return;
	    }
	    for (int i = 0; i < cube.size (); ++ i) {
	        if (st[abs(cube[i])-model_->num_inputs ()-1] == cube[i]) 
	    		tmp_st.push_back (cube[i]);
	    	else
	    	    tmp.push_back (-cube[i]);
	    }
	    
	    for (int i = 0; i < tmp.size (); ++ i)
	        tmp_st.push_back (tmp[i]);
	        
	    st = tmp_st;
	    //cube = st;
	    }
	    
	    st.insert (st.begin (), prefix.begin (), prefix.end ());
	  
           /* 
            Cube& comm = (frame_level+1 < comms_.size ()) ? comms_[frame_level+1] : comm_;
	    vector<int> tmp_comm;
	    tmp_comm.reserve (comm.size ());
	    for (int i = 0; i < comm.size (); ++ i) {
	        if (st[abs(comm[i])-model_->num_inputs ()-1] == comm[i]) 
	    		tmp_comm.push_back (comm[i]);
	    }
            st.insert (st.begin (), tmp_comm.begin(), tmp_comm.end ());
	*/
	}
	
		
	void Checker::print_evidence (ofstream& out) {
		if (forward_)
			init_->print_evidence (forward_, out);
		else
			last_->print_evidence (forward_, out);
	}
		
}
