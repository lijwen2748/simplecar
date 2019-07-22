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
 	struct P_Cube {
 	    Cube c_;
 	    bool propagated_;
 	    //constructor
 	    P_Cube (Cube& c) {c_ = c; propagated_ = false;}
 	    
 	    const int size () const {return c_.size ();}
 	    const int &operator[] (int id) const {return c_[id];}
 	};
 	typedef std::vector<P_Cube> Frame;
 	 
 }
 #endif
