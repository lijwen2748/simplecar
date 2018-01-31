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
	Update Date: October 17, 2017
	Data Structure for models
*/

#include "model.h"
#include "utility.h"
#include <stdlib.h>
#include <iostream>
#include <assert.h>

using namespace std;

namespace car{

	Model::Model (aiger* aig, const bool verbose)
	{
	    verbose_ = verbose;
	//According to aiger format, inputs should be [1 ... num_inputs_]
	//and latches should be [num_inputs+1 ... num_latches+num_inputs]]
		num_inputs_ = aig->num_inputs;
		num_latches_ = aig->num_latches;
		num_ands_ = aig->num_ands;
		num_constraints_ = aig->num_constraints;
		num_outputs_ = aig->num_outputs;
		flag_for_constraint_ = 0; //will set in create_constraints_for_latches
		
		//preserve two more ids for TRUE (max_id_ - 1) and FALSE (max_id_)
		max_id_ = aig->maxvar+2;
		true_ = max_id_ - 1;
		false_ = max_id_;
		
		collect_trues (aig);
		
		set_constraints (aig);
		set_outputs (aig);
		
		set_init (aig);
		
		create_next_map (aig);
		create_clauses (aig);
	}
	
	void Model::collect_trues (const aiger* aig)
	{
		for (int i = 0; i < aig->num_ands; i ++)
		{
			aiger_and& aa = aig->ands[i];
			//and gate is always an even number in aiger
			assert (aa.lhs % 2 == 0);
			if (is_true (aa.rhs0) && is_true (aa.rhs1))
				trues_.insert (aa.lhs);
			else if (is_false (aa.rhs0) || is_false (aa.rhs1))
				trues_.insert (aa.lhs + 1);
		}
	}
	
	void Model::create_next_map (const aiger* aig)
	{
		for (int i = 0; i < aig->num_latches; i ++)
		{
			int val = (int)aig->latches[i].lit;
			//a latch should not be a negative number
			assert (val % 2 == 0);
			val = val / 2;
			//make sure our assumption about latches is correct
			assert (val == (num_inputs_ + 1 + i));
			
			//pay attention to the special case when next_val = 0 or 1
			if (is_false (aig->latches[i].next))  //FALSE
			{
				next_map_.insert (std::pair<int, int> (val, false_));
				insert_to_reverse_next_map (false_, val);
			}
			else if (is_true (aig->latches[i].next)) //TRUE
			{
				next_map_.insert (std::pair<int, int> (val, true_));
				insert_to_reverse_next_map (true_, val);
			}
			else
			{
				int next_val = (int) aig->latches[i].next;
				next_val = (next_val % 2 == 0) ? (next_val/2) : -(next_val/2);
				next_map_.insert (std::pair<int, int> (val, next_val));
				insert_to_reverse_next_map (abs (next_val), (next_val > 0) ? val : -val);
			}
			
		}
	}
	
	void Model::insert_to_reverse_next_map (const int index, const int val)
	{
	    reverseNextMap::iterator it = reverse_next_map_.find (index);
	    if (it == reverse_next_map_.end ())
	    {
	        vector<int> v;
	        v.push_back (val);
	        reverse_next_map_.insert (std::pair<int, vector<int> > (index, v));
	    }
	    else
	        (it->second).push_back (val);
	}
	
	void Model::create_clauses (const aiger* aig)
	{
	    //contraints, outputs and latches gates are stored in order, 
	    //as the need for start solver construction
		hash_set<unsigned> exist_gates, gates;
		//create clauses for constraints
		collect_necessary_gates (aig, aig->constraints, aig->num_constraints, exist_gates, gates);
		
		for (hash_set<unsigned>::iterator it = gates.begin (); it != gates.end (); it ++)
		{
			aiger_and* aa = aiger_is_and (const_cast<aiger*>(aig), *it);
			assert (aa != NULL);
			add_clauses_from_gate (aa);
		}
		
		//if several latches' next value points to a same one, the values of these latches also have the constraint
		//But NOTE that all states in the aiger model must satisfy this constraint, EXCEPT the initial state
		//Also it is needed to add new contraints later
		create_constraints_for_latches ();
		
		set_outputs_start ();
		
		//create clauses for outputs
		gates.clear ();
		collect_necessary_gates (aig, aig->outputs, aig->num_outputs, exist_gates, gates);
		
		for (hash_set<unsigned>::iterator it = gates.begin (); it != gates.end (); it ++)
		{
			aiger_and* aa = aiger_is_and (const_cast<aiger*>(aig), *it);
			assert (aa != NULL);
			add_clauses_from_gate (aa);
		}
		
		set_latches_start ();
		
		//create clauses for latches
		gates.clear ();
		collect_necessary_gates (aig, aig->latches, aig->num_latches, exist_gates, gates, true);
		for (hash_set<unsigned>::iterator it = gates.begin (); it != gates.end (); it ++)
		{
			aiger_and* aa = aiger_is_and (const_cast<aiger*>(aig), *it);
			assert (aa != NULL);
			add_clauses_from_gate (aa);
		}
		
		//create clauses for true and false
		cls_.push_back (clause (true_));
		cls_.push_back (clause (-false_));
	}
	
	void Model::create_constraints_for_latches ()
	{
	    int flag1 = ++max_id_, flag2 = ++max_id_;
	    set_flag_for_constraint (flag1);
	    bool exist = false;
	    for (reverseNextMap::iterator it = reverse_next_map_.begin (); it != reverse_next_map_.end (); it ++)
	    {
	        vector<int>& v = it->second;
	        if (v.size () <= 1)
	            continue;
	        for (int i = 0; i < v.size () - 1; i ++)
	        {
	            exist = true;
	            vect tmp;
	            tmp.push_back (v[i]);
	            tmp.push_back (-v[i+1]);
	            tmp.push_back (-flag1);
	            cls_.push_back (tmp);
	            tmp.clear ();
	            tmp.push_back (-v[i]);
	            tmp.push_back (v[i+1]);
	            tmp.push_back (-flag1);
	            cls_.push_back (tmp);
	        }
	    }
	    if (!exist)
	    {
	        //at last add one clause for flag1 so that the sat solver will not treat flag1 as one literal
	        vect tmp;
	        tmp.push_back (++max_id_);
	        tmp.push_back (-flag1);
	        cls_.push_back (tmp);
	    }
	    //add initial state
	    for (int i = 0; i < init_.size (); i ++)
	    {
	        vect tmp;
	        tmp.push_back (init_[i]);
	        tmp.push_back (-flag2);
	        cls_.push_back (tmp);
	    }
	    vect tmp;
	    tmp.push_back (flag1);
	    tmp.push_back (flag2);
	    cls_.push_back (tmp);
	}
	
	void Model::collect_necessary_gates (const aiger* aig, const aiger_symbol* as, const int as_size, 
	                                        hash_set<unsigned>& exist_gates, hash_set<unsigned>& gates, bool next)
	{
		for (int i = 0; i < as_size; i ++)
		{
			aiger_and* aa;
			if (next) 
			    aa = necessary_gate (as[i].next, aig);
			else
			{
			    aa = necessary_gate (as[i].lit, aig);
			    if (aa == NULL)
			    {
			    	if (is_true (as[i].lit))
			    		outputs_[i] = true_;
			    	else if (is_false (as[i].lit))
			    		outputs_[i] = false_;
			    }
			}
			recursively_add (aa, aig, exist_gates, gates);	
		}
		
	}
	
	
	aiger_and* Model::necessary_gate (const unsigned id, const aiger* aig)
	{
		if (!is_true (id) && !is_false (id))
			return aiger_is_and (const_cast<aiger*> (aig), (id % 2 == 0) ? id : (id-1));
			
		return NULL;
	}
	
	void Model::recursively_add (const aiger_and* aa, const aiger* aig, hash_set<unsigned>& exist_gates, hash_set<unsigned>& gates)
	{
		if (aa == NULL)
			return;
		if (exist_gates.find (aa->lhs) != exist_gates.end ())
			return;
		
		gates.insert (aa->lhs);
		exist_gates.insert (aa->lhs);
		aiger_and* aa0 = necessary_gate (aa->rhs0, aig);
		recursively_add (aa0, aig, exist_gates, gates);
		
		aiger_and* aa1 = necessary_gate (aa->rhs1, aig);
		recursively_add (aa1, aig, exist_gates, gates);
	}
	
	void Model::add_clauses_from_gate (const aiger_and* aa)
	{
		assert (aa != NULL);
		assert (!is_true (aa->lhs) && !is_false (aa->lhs));
		
		if (is_true (aa->rhs0))
		{
			cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs1)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
		}
		else if (is_true (aa->rhs1))
		{
			cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
		}
		else
		{
			cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0), -car_var (aa->rhs1)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
		}
			
	}
	
	void Model::set_init (const aiger* aig)
	{
		for (int i = 0; i < aig->num_latches; i ++)
		{
			if (aig->latches[i].reset == 0)
				init_.push_back (-(num_inputs_+1+i));
			else if (aig->latches[i].reset == 1)
				init_.push_back (num_inputs_+1+i);
			else
			{
				cout << "Error setting initial state!" << endl;
				exit (0);
			}
		}
	}
	
	void Model::set_constraints (const aiger* aig)
	{
		for (int i = 0; i < aig->num_constraints; i ++)
		{
			int id = (int) aig->constraints[i].lit;
			constraints_.push_back ((id%2 == 0) ? (id/2) : -(id/2));
		}
	}
	
	void Model::set_outputs (const aiger* aig)
	{
		for (int i = 0; i < aig->num_outputs; i ++)
		{
			int id = (int) aig->outputs[i].lit;
			outputs_.push_back ((id%2 == 0) ? (id/2) : -(id/2));
		}
	}
	
	int Model::prime (const int id)
	{
		nextMap::iterator it = next_map_.find (abs (id));
		if (it == next_map_.end ())
		    return 0; //not found
		return (id > 0 ? it->second : -(it->second));
	}
	
	std::vector<int> Model::previous (const int id)
	{
	    vector<int> res;
	    reverseNextMap::iterator it = reverse_next_map_.find (abs (id));
		if (it == reverse_next_map_.end ())
		    return res; //not found
		res = it->second;
		if (id < 0)
		{
		    for (int i = 0; i < res.size (); i ++)
		        res[i] = -res[i];
		}
		return res;
	}
	
	void Model::shrink_to_previous_vars (Cube& uc, bool& constraint)
	{
		Cube tmp;
		constraint = true;
		for (int i = 0; i < uc.size (); i ++)
		{
		    vector<int> ids = previous (abs (uc[i]));
			if (ids.empty ())
			{
				constraint = false;
			    continue;
			}
			else
			{
			    for (int j = 0; j < ids.size (); j ++)
			        tmp.push_back ((uc[i] > 0) ? ids[j] : (-ids[j]));
			}
				
		}
		uc = tmp;
	}
	
	void Model::shrink_to_latch_vars (Cube& uc, bool& constraint)
	{
		Cube tmp;
		constraint = true;
		for (int i = 0; i < uc.size (); i ++)
		{
			if (latch_var (abs (uc[i])))
				tmp.push_back (uc[i]);
			else
				constraint = false;
		}
		uc = tmp;
	}
	
	void Model::update_constraint (Cube& cu)
	{
	    vect v;
	    for (int i = 0; i < cu.size (); i ++)
	        v.push_back (-cu[i]);
	    v.push_back (-flag_for_constraint_);
	    //update cu for later use
	    cu.push_back (flag_for_constraint_);
	    cls_.insert (cls_.begin (), v);
	    outputs_start_ += 1;
	    latches_start_ += 1;
	}
	
	void Model::print ()
	{
	    cout << "-------------------Model information--------------------" << endl;
	    cout << endl << "number of clauses: " << cls_.size () << endl;
	    for (int i  = 0; i < cls_.size (); i ++)
	        car::print (cls_[i]);
	    cout << endl << "next map: " << endl;
	    car::print (next_map_);
	    cout << endl << "reverse next map:" << endl;
	    car::print (reverse_next_map_);
	    cout << endl << "Initial state:" << endl;
	    car::print (init_);
	    cout << endl << "number of Inputs: " << num_inputs_ << endl;
	    cout << endl << "number of Latches: " << num_latches_ << endl;
	    cout << endl << "number of Outputs: " << num_outputs_ << endl;
	    car::print (outputs_);
	    cout << endl << "number of constraints: " << num_constraints_ << endl;
	    car::print (constraints_);
	    cout << endl << "Max id used: " << max_id_ << endl;
	    cout << endl << "outputs start index: " << outputs_start_ << endl;
	    cout << endl << "latches start index: " << latches_start_ << endl;
	    cout << endl << "number of TRUE variables: " << trues_.size () << endl;
	    car::print (trues_); 
	    cout << endl << "-------------------End of Model information--------------------" << endl;   
	}
}
