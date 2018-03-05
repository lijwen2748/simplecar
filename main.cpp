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

#include "checker.h"
#include "statistics.h"
#include "data_structure.h"
#include "model.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <iostream>
#include <fstream>
#include <signal.h>
#include <assert.h>
using namespace std;
using namespace car;

Statistics stats;
ofstream dot_file;

void  signal_handler (int sig_num)
{
	stats.count_total_time_end ();
	stats.print ();
	
	//write the dot file tail
    dot_file << "\n}" << endl;
	dot_file.close ();
	exit (0);
}

void print_usage () 
{
  printf ("Usage: simplecar <-f|-b|-p|-e|-v|-h> <aiger file> <output directory>\n");
  printf ("       -f          forward checking (Default = backward checking)\n");
  printf ("       -b          backward checking \n");
  printf ("       -p          enable propagation (Default = off)\n");
  printf ("       -e          print witness (Default = off)\n");
  printf ("       -v          print verbose information (Default = off)\n");
  printf ("       -h          print help information\n");
  exit (0);
}

string get_file_name (string& s)
{
    size_t start_pos = s.find_last_of ("/");
    if (start_pos == string::npos)
       start_pos = 0;
    else
        start_pos += 1;
         
    
    string tmp_res = s.substr (start_pos);
    
    string res = "";
    //remove .aig

    size_t end_pos = tmp_res.find (".aig");
    assert (end_pos != string::npos);
    
    for (int i = 0; i < end_pos; i ++)
        res += tmp_res.at (i);
        
    return res;
    
}

void check_aiger (int argc, char** argv)
{

   bool forward = false;
   bool verbose = false;
   bool evidence = false;
   bool minimal_uc = false;
   double reduce_ratio = 0.5;
   bool detect_dead_state = false;
   bool relative = false;
   bool relative_full = false;
   bool propagate = false;
   bool intersect = false;
   bool inv_next = false;
   bool greedy = true;
   
   
   string input;
   string output_dir;
   bool input_set = false;
   bool output_dir_set = false;
   for (int i = 1; i < argc; i ++)
   {
   		if (strcmp (argv[i], "-f") == 0)
   			forward = true;
   		else if (strcmp (argv[i], "-b") == 0)
   			forward = false;
   		else if (strcmp (argv[i], "-p") == 0)
   			propagate = true;
   		else if (strcmp (argv[i], "-v") == 0)
   			verbose = true;
   		else if (strcmp (argv[i], "-e") == 0)
   			evidence = true;
   		else if (strcmp (argv[i], "-h") == 0)
   			print_usage ();
   		else if (!input_set)
   		{
   			input = string (argv[i]);
   			input_set = true;
   		}
   		else if (!output_dir_set)
   		{
   			output_dir = string (argv[i]);
   			output_dir_set = true;
   		}
   		else
   			print_usage ();
   }
   if (!input_set || !output_dir_set)
   		print_usage ();
   /*
  if (argc <= 3 || argc > 4)
	  print_usage ();

  if (strcmp (argv[1], "-f") == 0)
	  forward = true;
  else if (strcmp (argv[1], "-b") == 0)
	  forward = false;
  else
	  print_usage ();
	*/

  //std::string output_dir (argv[3]);
  if (output_dir.at (output_dir.size()-1) != '/')
    output_dir += "/";
  //std::string s (argv[2]);
  std::string filename = get_file_name (input);
  
  std::string stdout_filename = output_dir + filename + ".log";
  std::string stderr_filename = output_dir + filename + ".err";
  std::string res_file_name = output_dir + filename + ".res";
  
  std::string dot_file_name = output_dir + filename + ".gv";
  
  if (!verbose)
    freopen (stdout_filename.c_str (), "w", stdout);
  //freopen (stderr_filename.c_str (), "w", stderr);
  ofstream res_file;
  res_file.open (res_file_name.c_str ());
  
  //write the Bad states to dot file
  
  dot_file.open (dot_file_name.c_str ());
  //prepare the dot header
  dot_file << "graph system {\n\t\t\tnode [shape = point];\n\t\t\tedge [penwidth = 0.1];\n\t\t\tratio = auto;";
  
  stats.count_total_time_start ();
  //get aiger object
   aiger* aig = aiger_init ();
   //aiger_open_and_read_from_file(aig, s.c_str());
   aiger_open_and_read_from_file(aig, input.c_str());
   const char * err = aiger_error(aig);
   if (err) 
   {
     printf ("read agier file error!\n");
     //throw InputError(err);
     exit (0);
   }
   if (!aiger_is_reencoded(aig))
     aiger_reencode(aig);
     
   stats.count_model_construct_time_start ();
   Model* model = new Model (aig);
   stats.count_model_construct_time_end ();
   
   if (verbose)
    model->print ();
   
   State::set_num_inputs_and_latches (model->num_inputs (), model->num_latches ());
   
   //assume that there is only one output needs to be checked in each aiger model, 
   //which is consistent with the HWMCC format
   assert (model->num_outputs () >= 1);
   
   Checker ch (model, stats, dot_file, greedy, reduce_ratio, forward, inv_next, propagate, evidence, verbose, intersect, minimal_uc, detect_dead_state, relative, relative_full);

   aiger_reset(aig);
   
   bool res = ch.check (res_file);
    
   delete model;
   res_file.close ();
   
   //write the dot file tail
   dot_file << "\n}" << endl;
   dot_file.close ();
   stats.count_total_time_end ();
   stats.print ();
   return;
}


int main (int argc, char ** argv)
{
  signal (SIGINT, signal_handler);
  
  check_aiger (argc, argv);
  
  return 0;
}
