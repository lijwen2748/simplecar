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
 * File:   hash_map.h
 * Author: Yinbo Yao and Jianwen Li
 *
 * Created on October 29, 2013, 1:46 PM
 */

#ifndef HASH_MAP_H
#define	HASH_MAP_H

#if defined __APPLE__

#include <unordered_map>

#ifndef hash_map
#define hash_map std::unordered_map
#endif

#elif defined __GNUC__

#include <tr1/unordered_map>

#ifndef hash_map
#define hash_map std::tr1::unordered_map
#endif

#else //@ TODO: 补完整
#include <hash_map>
#endif

#ifndef HASH_INIT
#define HASH_INIT 1315423911
#endif

#endif	/* HASH_MAP_H */

