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
	Update Date: September 20, 2017
	Data structures in CAR
*/

 #ifndef DATA_STRUCTURE_H
 #define DATA_STRUCTURE_H
 
 #include <vector>
 #include <stdlib.h>
 #include <iostream>
 #include <fstream>
 
 namespace car
 {
 	typedef std::vector<int> Assignment;
 	typedef std::vector<int> Cube;
 	typedef std::vector<int> Clause;
 	typedef std::vector<Cube> Frame;
 	typedef std::vector<Frame> Fsequence;
 	
 	//state 
 	class State 
 	{
 	public:
 	    State (const Assignment& latches) : s_ (latches), pre_ (NULL), next_ (NULL), dead_ (false), added_to_dead_solver_ (false) {}

 		State (const State *s, const Assignment& inputs, const Assignment& latches, const bool forward, const bool last = false); 
 		
 		State (State *s): pre_ (s->pre_), next_(s->next_), s_(s->s_), inputs_(s->inputs_), last_inputs_(s->last_inputs_), 
 		init_ (s->init_), id_ (s->id_), dep_ (s->dep_), dead_ (false), added_to_dead_solver_ (false) {}

 		~State () {}
 		
 		bool imply (const Cube& cu) const;
 		Cube intersect (const Cube& cu);
 		inline void set_detect_dead_start (int pos) {detect_dead_start_ = pos;}
 		inline int detect_dead_start () {return detect_dead_start_;}
 		
 		inline void set_inputs (const Assignment& st) {inputs_ = st;}
 		inline void set_last_inputs (const Assignment& st) {last_inputs_ = st;}
 		inline void set_initial (bool val) {init_ = val;}
 		inline void set_final (bool val) {final_ = val;}
 		inline void set_depth (int pos) {dep_ = pos;}
 		inline int id () {return id_;}
 		
 		inline void print () { std::cout << latches () << std::endl;}
 		
 		void print_evidence (bool forward, std::ofstream&);
 		
 		inline int depth () {return dep_;}
 		inline Assignment& s () {return s_;}
 		inline State* next () {return next_;}
 		inline State* pre () {return pre_;}
 		inline Assignment& inputs_vec () {return inputs_;}
 		std::string inputs (); 
 		
 		std::string last_inputs (); 

 		std::string latches ();
 		
 		inline int size () {return s_.size ();}
 		inline int element (int i) {return s_[i];}
 		
 		inline void set_s (Cube &cube) {s_ = cube;}
 		inline void set_next (State* nx) {next_ = nx;}
 		static void set_num_inputs_and_latches (const int n1, const int n2); 
 		
 		inline void set_nexts (std::vector<int>& nexts) {nexts_ = nexts; computed_next_ = true;}
 		inline std::vector<int>& nexts () {return nexts_;}
 		inline bool computed_next () const {return computed_next_;}
 		
 		inline int work_level () const {return work_level_;}
 		inline void set_work_level (int id) {work_level_ = id;}
		inline void work_count_inc () {work_count_ ++;}
 		inline int work_count () {return work_count_;}
 		inline int work_count_reset () {work_count_ = 0;}
 		
 		inline void mark_dead () {dead_ = true;}
 		inline bool is_dead () {return dead_;}
 		inline void set_added_to_dead_solver (bool val) {added_to_dead_solver_ = val;}
 		inline bool added_to_dead_solver () {return added_to_dead_solver_;}
 	private:
 	//s_ contains all latches, but if the value of latch l is not cared, assign it to -1.
 		Assignment s_;
 		State* next_;
 		State* pre_;
 		std::vector<int> inputs_;
 		std::vector<int> last_inputs_; // for backward CAR only!
 		
 		bool init_;  //whether it is an initial state
 		bool final_; //whether it is an final state
 		bool dead_;  //whether it is a dead state 
 		bool added_to_dead_solver_; //whether it is added to the dead solver
 		int id_;     //the state id
 		int dep_;    //the length from the starting state
 		
 		bool computed_next_;  //flag to label whether the next part of the state has been computed
 		std::vector<int> nexts_; //the next part which can be decided by the state without input
 		
 		int work_level_;
		int work_count_;
 		
 		
 		int detect_dead_start_; //to store the start position to check whether it is a dead state
 		
 		static int num_inputs_;
 		static int num_latches_;
 		static int id_counter_;
 	};
 	
 	typedef std::vector<std::vector<State*> > Bsequence;
 	 
 }
 #endif
