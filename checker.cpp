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
			    
			    if (try_satisfy_by (new_level, new_state))
				    return true;
				if (safe_reported ())
				    return false;
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
	
		
	//////////////helper functions/////////////////////////////////////////////

	Checker::Checker (Model* model, Statistics& stats, ofstream* dot, bool forward, bool evidence, bool begin, bool end, bool inter, bool rotate, bool verbose, bool minimal_uc)
	{
	    
		model_ = model;
		stats_ = &stats;
		dot_ = dot;
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
		minimal_update_level_ = F_.size ()-1;
		solver_call_counter_ = 0;
		start_solver_call_counter_ = 0; 
		
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
	    solver_ = new MainSolver (model_, stats_, verbose_);
		start_solver_ = new StartSolver (model_, bad_, forward_, verbose_);
		assert (F_.empty ());
		assert (B_.empty ());
		
	}
	
	void Checker::car_finalization ()
	{
	    F_.clear ();
	    destroy_states ();
	    if (solver_ != NULL) {
	        delete solver_;
	        solver_ = NULL;
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
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State *res = new State (NULL, pa.first, pa.second, forward_, true);
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
	
	State* Checker::get_new_state (const State* s)
	{
		Assignment st = solver_->get_state (forward_, partial_state_);
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State* res = new State (s, pa.first, pa.second, forward_);
		
		return res;
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
			
		//pay attention to the size of cu!
		if (cu.empty ())
		{
			report_safe ();
			return;
		}
		
		
		push_to_frame (cu, frame_level);
		
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
		
		if (frame_level < int (F_.size ()))
			solver_->add_clause_from_cube (cu, frame_level, forward_);
		else if (frame_level == int (F_.size ()))
			start_solver_->add_clause_with_flag (cu);
	}
	
	
	int Checker::get_new_level (const State *s, const int frame_level){
	    for (int i = 0; i < frame_level; i ++){
	        int j = 0;
	        for (; j < F_[i].size (); j ++){
	            if (s->imply (F_[i][j]))
	                break;
	        }
	        if (j >= F_[i].size ())
	            return i-1;
	    }
		return frame_level - 1;
	}
	
	bool Checker::tried_before (const State* st, const int frame_level) {
	    assert (frame_level >= 0);
	    Frame &frame = (frame_level < F_.size ()) ? F_[frame_level] : frame_;
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
	    for (int i = 0; i < cu.size() ; ++ i) {
	    	if (st[abs(cu[i])-model_->num_inputs ()-1] == cu[i]) {
	    		tmp.push_back (cu[i]);
	    	}
	    }
	    res = tmp;
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
