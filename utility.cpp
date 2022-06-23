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

#include "utility.h"
#include <vector>
#include <algorithm>
using namespace std;

namespace car {

void print (const std::vector<int>& v)
{
    for (int i = 0; i < v.size (); i ++)
        std::cout << v[i] << " ";
    std::cout << std::endl;
}

void print (const hash_set<int>& s)
{
    for (hash_set<int>::const_iterator it = s.begin (); it != s.end (); it ++)
        std:: cout << *it << " ";
    std::cout << std::endl;
}

void print (const hash_set<unsigned>& s)
{
    for (hash_set<unsigned>::const_iterator it = s.begin (); it != s.end (); it ++)
        std:: cout << *it << " ";
    std::cout << std::endl;
}

void print (const hash_map<int, int>& m)
{
    for (hash_map<int, int>::const_iterator it = m.begin (); it != m.end (); it ++)
        std:: cout << it->first << " -> " << it->second << std::endl;
}

void print (const hash_map<int, std::vector<int> >& m)
{
    for (hash_map<int, std::vector<int> >::const_iterator it = m.begin (); it != m.end (); it ++)
    {
        std::cout << it->first << " -> {";
        vector<int> v = it->second;
        for (int i = 0; i < v.size (); i ++)
            cout << v[i] << " ";
        cout << "}" << endl;
    }
}

bool comp (int i, int j)
{
	return abs (i) < abs(j);
}

//elements in v1, v2 are in order
//check whether v2 is contained in v1 
bool imply ( std::vector<int>& v1,  std::vector<int>& v2)
{

    if (v1.size () < v2.size ())
        return false;
    
    
    std::vector<int>::iterator first1 = v1.begin (), first2 = v2.begin (), last1 = v1.end (), last2 = v2.end ();
    while (first2 != last2) 
    {
        if ( (first1 == last1) || comp (*first2, *first1) ) 
            return false;
        if ((*first1) == (*first2)) 
            ++ first2;
        ++ first1;
    }
    return true;
    
  
/*
    if (v1.size () < v2.size ())
        return false;
    int j = 0; 
    for (int i = 0; i < v2.size (); i ++)
    {
        if (j >= v1.size ())
            return false;
        while (abs(v1[j]) < abs(v2[i]))
        {
            j++;
            if (j >= v1.size ())
                return false;
        }
        
        if (v1[j] == v2[i])
            j++;
        else
            return false;
    }
    return true;
  */  
}

std::vector<int> vec_intersect (const std::vector<int>& v1, const std::vector<int>& v2)
{
	std::vector<int> res;
	std::vector<int>::const_iterator first1 = v1.begin (), first2 = v2.begin (), last1 = v1.end (), last2 = v2.end ();
    while (first2 != last2) 
    {
    	if (first1 == last1)
    		break;
    	if (comp (*first1, *first2))
    		first1 ++;
    	else if ((*first1) == (*first2))
    	{
    		res.push_back (*first1);
    		first1 ++;
    		first2 ++;
    	}
    	else
    		first2 ++;
    	    
    }
    return res;

}

bool is_in (const int id, const std::vector<int>& v, const int begin, const int end){
	//v is in order
	if (begin > end)
		return false;
	int pos = (begin+end)/2;
	if (v[pos] == id)
		return true;
	return (is_in (id, v, begin, pos-1) || is_in (id, v, pos+1, end));
}



}
