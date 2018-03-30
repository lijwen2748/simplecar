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
	
	
