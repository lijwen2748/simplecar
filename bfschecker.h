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
	Update Date: July 21, 2018
	Interface for the BFS checker class
*/

 #ifndef BFSCHECKER_H
 #define BFSCHECKER_H
 
 #include "checker.h"
 
 namespace car {
 
    class BfsChecker: public Checker {
        public:
            BfsChecker (Model* model, Statistics& stats, std::ofstream* dot, bool forward = true, bool evidence = false, bool verbose = false, bool minimal_uc = false) : Checker (model, stats, dot, forward, evidence, verbose, minimal_uc) {}
        protected:
            bool try_satisfy (const int frame_level);
            int do_search (const int frame_level);
            bool try_satisfy_by (int frame_level, const State* s);
    };
 
 }
 
 #endif
