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
	Update Date: October 30, 2017
	Utility functions
*/

#ifndef UTILITY_H
#define UTILITY_H

#include <vector>
#include <iostream>
#include "hash_set.h"
#include "hash_map.h"
#include <stdlib.h>

namespace car{

void print (const std::vector<int>& v);

void print (const hash_set<int>& s);

void print (const hash_set<unsigned>& s);

void print (const hash_map<int, int>& m);

void print (const hash_map<int, std::vector<int> >& m);

bool is_in (const int id, const std::vector<int>& v, const int begin, const int end);



//elements in v1, v2 are in order
//check whether v2 is contained in v1 
bool imply (const std::vector<int>& v1, const std::vector<int>& v2);

std::vector<int> vec_intersect (const std::vector<int>& v1, const std::vector<int>& v2);
inline std::vector<int> cube_intersect (const std::vector<int>& v1, const std::vector<int>& v2)
{
	return vec_intersect (v1, v2);
}

bool comp (int i, int j);

}

#endif


