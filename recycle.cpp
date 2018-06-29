/*
 * This file is not a part of SimpleCAR
 * It is used to collect source codes that are shown not useful to improve SimpleCAR
 * But we keep the codes in case of further usage.
*/


   /*try to generate a smaller cube in a relative way
    * Idea: If c2 is the next state of c1, get c = c1 \cap c2 and consider c instead c1 for UC extraction.
    */
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
    
    
    //it is not useful, because the successful attempts are very small
    /*
     * Idea: If cu is going to be added into the frame, get c = cu \cap frame[i] instead to seek a smaller cube
     */
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
	        	res = solver_solve_with_assumption (inter_cu, bad_);
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
	
	/*
	 * Idea: intersect cubes
	*/
	
	
	
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
	
	void MainSolver::try_reduce (Cube& cu)
	{
		int try_times = int ((cu.size ()) * reduce_ratio_);
		int i = 0;
		int sz = cu.size ()-1;
		hash_set<int> tried;
		for (; i < try_times; i ++)
		{
			int pos = i;
			while (tried.find (cu[pos]) != tried.end ())
			{
				pos ++;
				if (pos >= cu.size ())
					return;
			}
			
		    assumption_.clear ();
		    for (int j = 0; j < pos; j ++)
		    {
			    assumption_push (cu[sz-j]);
		    }
		    for (int j = pos+1; j < cu.size (); j ++)
		    {
			    assumption_push (cu[sz-j]);
		    }
		    stats_->count_reduce_uc_SAT_time_start ();
		    if (!solve_with_assumption ())
		    {
		        cu = get_uc ();
		        try_times = int ((cu.size ()) * reduce_ratio_);
		        i = -1;
		        sz = cu.size ()-1;
		    }
		    else
		    	tried.insert (cu[pos]);
		    stats_->count_reduce_uc_SAT_time_end ();
		}
	}
	
	/*
	* If the UC returned from SAT solver does not contain frame flags, 
	* we consider it is a permenant constraint.
	*/
	void Checker::update_constraint (Cube& cu) {
	    if (cu.empty ())
	    {
	        report_safe ();
	        return;
	    }
	    Cube to_add = cu;
	    constraints_.push_back (to_add);
	    model_->update_constraint (to_add);
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
    
    	    inline bool dead_state (const State* s){
	        stats_->count_detect_dead_state_time_start ();
	        bool res = solve_with (const_cast<State*>(s)->s (), -2);
	        stats_->count_detect_dead_state_time_end ();
	        return !res;
	    }

    /*
	* Initialize \@ state_seq by filling all states of \@ B_ into state_seq[0]
	* 
	*/
	void Checker::initial_greedy_state_sequence (std::vector<std::vector<State*> > &state_seq)
	{
	    assert (state_seq.size () == 0);
	    vector<State *> v;
	    for (int i = 0; i < B_.size (); i ++)
	    {
	        for (int j = 0; j < B_[i].size (); j ++)
	            v.push_back (B_[i][j]);
	    }
	    state_seq.push_back (v);   
	}
	
	/*
	* Pick up one state from the vector \@ states
	* There are different ways to pick up: Right now we just use the simplest one -- choose the last state 
	* After the state is picked up, it must also be removed from the vector
	*
	*/
	State* Checker::pick_up_one_state (std::vector<State*>& states)
	{
	    /*
	    assert (!states.empty ());
	    State *res = states.back ();
	    states.pop_back ();
	    return res;
	    */
	    
	    assert (!states.empty ());
	    State *res = states[0];
	    int index = 0;
	    for (int i = 1; i < states.size (); i ++) {
	        if (states[i]->depth () < res->depth ()) {
	            res = states[i];
	            index = i;
	        }
	    }
	    //delete res from states
	    states.erase (states.begin () + index);
	    return res;
	    
	}
	
	
	/*
	* Push \@ new_state into \@states_seq[\@ work]
	*
	*/
	void Checker::push_back_to (std::vector<std::vector<State*> >& states_seq, const int work, State* new_state)
	{
	    while (states_seq.size () <= work)
	    {
	        vector<State *> v;
	        states_seq.push_back (v);
	    }
	    states_seq[work].push_back (new_state);
	}
	
	
	/*
	* The implementation of the attempt to migrate A* algorithm for the search
	* The results turn out to be not quite successful.
	* Leave it for future exploration.
	*/
	int Checker::greedy_search (const int frame_level) {
	    vector<vector<State*> > states_seq;
	    initial_greedy_state_sequence (states_seq);
	    int work = 0;
	    while (true) {
	        //all states have been explored, but cannot find a solution
	        if (work == 0 && states_seq[work].empty ())
	            return -1;
	        if (states_seq[work].empty ())
	            work --;
	        else {
	            State* s = pick_up_one_state (states_seq[work]);
	            bool check_res = (frame_level-work == -1) ? immediate_satisfiable (s) : solve_with (const_cast<State*>(s)->s (), frame_level-work);
	            if (check_res) {
	                if (frame_level - work == -1)
	                    return 1;
	                State* new_state = get_new_state (s);
	                assert (new_state != NULL);
	                    
	                //////generate dot data
	                if (dot_ != NULL)
			            (*dot_) << "\n\t\t\t" << const_cast<State*> (s)->id () << " -- " << new_state->id ();
			        //////generate dot data
	                    
	                update_B_sequence (new_state);
	                push_back_to (states_seq, work, s);
	                int new_level = get_new_level (new_state, frame_level-work);
	                    	                    
	                work = frame_level - new_level;
	                push_back_to (states_seq, work, new_state); 
	            }
	            else {
	                update_F_sequence (s, frame_level-work+1);
	                if (safe_reported ())
			            return 0;
	                if (work > 0)
	                    push_back_to (states_seq, work-1, s);
	                    
	            }
	                
	        }
	    }
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
		return false;
	}
	
	
	
	
