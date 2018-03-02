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

 #ifndef CHECKER_H
 #define CHECKER_H
 
#include "data_structure.h"
#include "invsolver.h"
#include "startsolver.h"
#include "mainsolver.h"
#include "model.h"
#include <assert.h>
#include "utility.h"
#include "statistics.h"
#include <fstream>

#define MAX_COUNT 5

namespace car 
{
	class Checker 
	{
	public:
		Checker (Model* model, Statistics& stats, std::ofstream& dot, double ratio = 1.0, bool forward = true, bool inv_next = false, bool propage = false, bool evidence = false, bool verbose = false, bool intersect = false, bool minimal_uc = false, bool detect_dead_state = false, bool relative = false, bool relative_full = false);
		~Checker ();
		
		bool check (std::ofstream&);
		void print_evidence (std::ofstream&);
	private:
		//flags 
		bool forward_;
		bool partial_state_;
		bool minimal_uc_;
		bool evidence_;
		bool verbose_;
		bool detect_dead_state_;
		bool relative_;
		bool relative_full_;
		bool propagate_;
		bool intersect_;
		bool inv_next_;
		//members
		Statistics *stats_;
		double reduce_ratio_;
		
		std::ofstream* dot_;
		
		int minimal_update_level_;
		State* init_;  // the start state for forward CAR
		State* last_;  // the start state for backward CAR
		int bad_;
		std::vector<Cube> constraints_;  //to store the invariant found under detect_dead_state_
		Model* model_;
		MainSolver *solver_;
		StartSolver *start_solver_;
		InvSolver *inv_solver_;
		Fsequence F_;
		typedef std::vector<int> FrameCounter;
		typedef std::vector<FrameCounter> FrameCounters;
		FrameCounters FC_;  //corresponds to F_, for every cube in every frame in F_, i.e. F[i][j], there is FC_[i][j] corresponds to the 
							//number of attempts to reduce
		Bsequence B_;
		Frame frame_;   //to store the frame willing to be added in F_ in one step
		Frame frame2_;  //to store the frame willing to be added in F_ in two step (for relative only)
		FrameCounter fc_; //corresponds to frame_, for every cube frame_[i], fc_[i] corresponds to the number of attempts to reduce
		bool safe_reported_;  //true means ready to return SAFE
		//functions
		bool immediate_satisfiable ();
		bool immediate_satisfiable (const State*);
		bool immediate_satisfiable (const Cube&);
		void initialize_sequences ();
		bool try_satisfy (const int frame_level);
		bool try_satisfy_by (int frame_level, const State* s);
		bool invariant_found (int frame_level);
		bool invariant_found_at (const int frame_level);
		void inv_solver_add_constraint_or (const int frame_level);
		void inv_solver_add_constraint_and (const int frame_level);
		void inv_solver_release_constraint_and ();
		bool solve_with (const Cube &cu, const int frame_level);
		State* get_new_state (const State *s);
		void extend_F_sequence ();
		void update_F_sequence (const State* s, const int frame_level);
		void update_frame_by_relative (const State* s, const int frame_level);
		void update_B_sequence (const State* s, const int frame_level);
		int get_new_level (const State *s, const int frame_level);
		void push_to_frame (Cube& cu, const int frame_level, const State* s = NULL);
		bool tried_before (const State* s, const int frame_level);
		bool state_imply (const State* st, const Cube& cu);
		void add_reduced_uc (Cube& cu, int frame_level);
		
		Cube relative_cube (const State* s, const int frame_level);
		
		State* enumerate_start_state ();
		State* get_new_start_state ();
		std::pair<Assignment, Assignment> state_pair (const Assignment& st);
		
		void car_initialization ();
		void car_finalization ();
		void destroy_states ();
		bool car_check ();
		void set_initial_frame ();
		void update_constraint (Cube& cu, const State* s = NULL);
		void remove_dead_states ();
		
		bool propagate ();
		bool propagate (int pos);
		std::vector<int> propagate_start_;
		
		Cube constraint_intersect_;  //for constraint_
		std::vector<Cube> frames_intersect_; //for F_
		Cube cube_intersection (const State *s, Cube& cu, const int frame_level);
		
		inline Cube& intersect_of (const int frame_level)
		{
			Cube cu;
			while (frames_intersect_.size () <= frame_level)
				frames_intersect_.push_back (cu);
			return frames_intersect_[frame_level];
		}
		
		//inline functions
		inline void create_inv_solver ()
		{
			inv_solver_ = new InvSolver (model_, inv_next_, verbose_);
		}
		inline void delete_inv_solver ()
		{
			delete inv_solver_;
			inv_solver_ = NULL;
		}
		inline void report_safe ()
		{
		    safe_reported_ = true;
		}
		inline bool safe_reported ()
		{
		    return safe_reported_;
		}
		
		inline void reset_start_solver ()
	    {
	        assert (start_solver_ != NULL);
	        start_solver_->reset ();
	    }
	    
	    inline void clear_frame () 
	    {
	        frame_.clear ();
	        frame_ = frame2_;
	        for (int i = 0; i < frame_.size (); i ++)
	        	start_solver_->add_clause_with_flag (frame_[i]);
	        frame2_.clear ();
	        fc_.clear ();
	    }
	    
	    inline bool dead_state (const State* s)
	    {
	        stats_->count_detect_dead_state_time_start ();
	        bool res = solve_with (const_cast<State*>(s)->s (), -2);
	        stats_->count_detect_dead_state_time_end ();
	        return !res;
	    }
	    
	    
	    
	    inline void print_frame (const Frame& f)
	    {
	        for (int i = 0; i < f.size (); i ++)
	            car::print (f[i]);
	    }
	    
	    inline void print_F ()
	    {
	        std::cout << "-----------F sequence information------------" << std::endl;
	        for (int i = 0; i < F_.size (); i ++)
	        {
	            std::cout << "Frame " << i << ":" << std::endl;
	            print_frame (F_[i]);
	        }
	        std::cout << "-----------End of F sequence information------------" << std::endl;
	    }
	    
	    inline void print_B ()
	    {
	        std::cout << "-----------B sequence information------------" << std::endl;
	        for (int i = 0; i < B_.size (); i ++)
	        {
	            for (int j = 0; j < B_[i].size (); j ++)
	                B_[i][j]->print ();
	        }
	        std::cout << "-----------End of B sequence information------------" << std::endl;
	    }
	    
	    inline void print ()
	    {
	        print_F ();
	        print_B ();
	    }
	    
	};
}
#endif
