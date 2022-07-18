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

 
 #include <vector>
 #include "utility.h"
 #include <stdlib.h>
 #include "data_structure.h"
 #include <string.h>
 #include <assert.h>
 using namespace std;
 
 namespace car
 {
 
    State::State (const State *s, const Assignment& inputs, const Assignment& latches, const bool forward, const bool last) 
 	{
 		if (forward)
 		{
 			pre_ = NULL;
 			next_ = const_cast<State*> (s);
 			inputs_ = inputs;
 			s_ = latches;
 		}
 		else
 		{
 			pre_ = const_cast<State*> (s);
 			next_ = NULL;
 			if (last)
 				last_inputs_ = inputs;
 			else
 				inputs_ = inputs;
 			s_ = latches;
 		}
 		detect_dead_start_ = 0;
 		init_ = false;
 		id_ = id_counter_++;
 		if (s == NULL)
 		    dep_ = 0;
 		else
 		    dep_ = s->dep_ + 1;
		work_count_ = 0;
		dead_ = false;
		added_to_dead_solver_ = false;
 	}
 	
 	bool State::imply (const Cube& cu) const
	{
		for (int i = 0; i < cu.size (); i ++)
		{
			int index = abs(cu[i]) - num_inputs_ - 1;
			assert (index >= 0);
			if (s_[index] != cu[i])
				return false;
		}
		return true;
	}
	
	Cube State::intersect (const Cube& cu) 
	{
		Cube res;
		for (int i = 0; i < cu.size (); i ++)
		{
			int index = abs(cu[i]) - num_inputs_ - 1;
			assert (index >= 0);
			if (s_[index] == cu[i])
				res.push_back (cu[i]);
		}
		return res;
	}
 	
 	void State::print_evidence (bool forward, ofstream& out)
 	{
 		State* nx = this;
	    if (forward)
	    {
	        out << nx->latches () << endl;
	    	out << nx->inputs ()  << endl;
	    	while (nx->next() != NULL)
	    	{
	    		nx = nx->next ();
	    		out << nx->inputs () << endl;
	    	}
	    }
	    else
	    {
	    
	    	vector<string> tmp;
	    	State *start = this;
	    	//reversve the states order
	    	tmp.push_back (start->last_inputs ());
	    	while (start->pre () != NULL)
	    	{
	    		tmp.push_back (start->inputs ());
	    		start = start->pre ();
	    	}
	    	//start now is the initial state
	    	for (int i = tmp.size ()-1; i >= 0; i --)
	    	{
	    		if (i == tmp.size() - 1) //init state
	    		    out << start->latches () << endl;
	    		out << tmp[i] << endl;
	    	}
	    
	    /*
	    	vector<State*> tmp;
	    	tmp.push_back (this);
	    	State *start = this;
	    	//reversve the states order
	    	while (start->pre () != NULL)
	    	{
	    		tmp.push_back (start->pre ());
	    		start = start->pre ();
	    	}
	    	//start now is the initial state
	    	for (int i = tmp.size ()-1; i >= 0; i --)
	    	{
	    		car::print (tmp[i]->s());
	    	}
	    	*/
	    }
	    
 	}
 	
 	string State::inputs () 
 	{
 		string res = "";
 		for (int i = 0; i < inputs_.size (); i ++)
 			res += (inputs_[i] > 0) ? "1" : "0";
 		return res;
 	}
 	
 	string State::last_inputs () 
 	{
 		string res = "";
 		for (int i = 0; i < last_inputs_.size (); i ++)
 			res += (last_inputs_[i] > 0) ? "1" : "0";
 		return res;
 	}
 	
 	string State::latches () 
 	{
 		string res = "";
 		//int input_size = inputs_.size ();
 		int j = 0;
 		for (int i = 0; i < num_latches_; i ++)
 		{
 			if (j == s_.size ())
 				res += "x";
 			else if (num_inputs_+i+1 < abs (s_[j]))
 				res += "x";
 			else
 			{
 				res += (s_[j] >0) ? "1" : "0";
 				j ++;
 			}
 		}
 		return res;
 	}
 	
 	int State::num_inputs_ = 0;
 	int State::num_latches_ = 0;
 	int State::id_counter_ = 1;
 	
 	void State::set_num_inputs_and_latches (const int n1, const int n2) 
 	{
 		num_inputs_ = n1;
 	    num_latches_ = n2;
 	}
 	
 	
}
 		
