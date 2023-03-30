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

extern "C" {
#include "aigtoaig_forCAR.h"
}
#include "checker.h"
#include "bfschecker.h"
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
ofstream* dot_file = NULL;
Model * model = NULL;
Checker *ch = NULL;

/**
 * @brief The signal handler registered for printing message when interrupted.
 * @param sig_num
 */
void signal_handler(int sig_num) {
  if (ch != NULL) {
    cout << "Last Frame " << endl;
    ch->print_frames_sizes();
    cout << "frame_ size:" << ch->frame_size() << endl;
    delete ch;
    ch = NULL;
  }

  if (model != NULL) {
    delete model;
    model = NULL;
  }
  stats.count_total_time_end();
  stats.print();

  // write the dot file tail
  if (dot_file != NULL) {
    (*dot_file) << "\n}" << endl;
    dot_file->close();
    delete dot_file;
  }
  exit(0);
}

/**
 * @brief Print Command line option messages, and exit.
 */
void print_usage () 
{
  printf ("Usage: simplecar <-f|-b> [-e|-v|-h] <-begin|-end> <-interation|-rotation|-interation -rotation> <aiger file> <output directory>\n");
  printf ("       -f              forward checking (Default = backward checking)\n");
  printf ("       -b              backward checking \n");
  //printf ("       -p          enable propagation (Default = off)\n");
  //printf ("       -g          enable greedy search (Default = off)\n");
  printf ("       -begin          state numeration from begin of the sequence\n");
  printf ("       -end            state numeration from end of the sequence\n");
  printf ("       -interaion      enable intersection heuristic\n");
  printf ("       -rotation       enable rotation heurisitc\n");
  printf ("       -e              print witness (Default = off)\n");
  printf ("       -v              print verbose information (Default = off)\n");
  printf ("       -h              print help information\n");
  printf ("NOTE: -f and -b cannot be used together!\n");
  printf ("NOTE: -begin and -end cannot be used together!\n");
  exit (0);
}

/**
 * @brief Get the exact file name, without prefix and directory trail.
 * 
 * @example ~/validation/simplecar/testcases/test.aag -> "test"
 * @example test.aag -> "test"
 * @example TEST.txt -> Assertion Failed.
 * 
 * @param s the path of file.
 * @return string, the exact file name
 */
string get_file_name (string& s)
{
  // We assume the separator is in UNIX form.
  size_t s_len = s.size();

  assert(s_len > 4 && s[s_len-1] == 'g' && (s[s_len-2] == 'a' || s[s_len-2] == 'i') && s[s_len-3] == 'a' && s[s_len-4] == '.' && "Input should be in aag or aig format");

  size_t start_pos = s.find_last_of("/");
  start_pos = start_pos == string::npos ? 0 : start_pos + 1;

  return s.substr(start_pos,s_len-4-start_pos);
}

/**
 * @brief The entrance of checking. 
 * 
 * @param argc 
 * @param argv 
 */
void check_aiger (int argc, char** argv)
{
   bool forward = false;
   bool verbose = false;
   bool evidence = false;
   bool minimal_uc = false;
   bool gv = false; //to print dot format for graphviz 
   bool ilock = false;
   bool partial = true;
   bool propagate = true;
   bool begin = false;
   bool end = true;
   bool inter = true;
   bool rotate = false;
   int index_to_be_checked = -1;

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
   		else if (strcmp (argv[i], "-v") == 0)
   			verbose = true;
   		else if (strcmp (argv[i], "-e") == 0)
   			evidence = true;
      else if (strcmp (argv[i], "-ilock") == 0)
   			ilock = true;
      else if (strcmp (argv[i], "-i") == 0)
      {
        // get index of output to be verified.
        assert(i+1 < argc && "The index of output should be specified.");
        char *tmp = argv[++i];
        index_to_be_checked = 0;
        for(int j = 0 ; j < strlen(tmp); ++j)
        {
          assert(tmp[j] >= '0' && tmp[j] <='9' && "The index of output to be checked should be legal positive number.");
          index_to_be_checked *= 10;
          index_to_be_checked += tmp[j] - '0';
        }
      }
   		else if (strcmp (argv[i], "-h") == 0)
   			print_usage ();
   		else if (strcmp (argv[i], "-begin") == 0) {
   			if (end) {
   				print_usage ();
   			}
   			begin = true;
   		}
   		else if (strcmp (argv[i], "-end") == 0) {
   			if (begin) {
   				print_usage ();
   			}
   			end = true;
   		}
   		else if (strcmp (argv[i], "-interation") == 0)
   			inter = true;
   		else if (strcmp (argv[i], "-rotation") == 0)
   			rotate = true;
   		else if (!input_set)
   		{
   			input = string (argv[i]);
   			input_set = true;
   		}
   		else if (!output_dir_set)
   		{
   			output_dir = string (argv[i]);
   			output_dir_set = true;
        if (output_dir.at (output_dir.size()-1) != '/')
          output_dir += "/";
   		}
   		else
   			print_usage ();
   }
   if (!input_set || !output_dir_set)
   		print_usage ();
   /**
    * @brief transform aag to aig using aigtoaig in aiger portfolio.
    */
   if (input.size() > 4 && input.substr(input.size() - 4) == ".aag") {
     std::string new_input = input;
     new_input[input.size() - 2] = 'i';
     convert_aigtoaig(input.c_str(), new_input.c_str());
     input = new_input;
   }
  std::string filename = get_file_name (input);
  std::string stdout_filename = output_dir + filename + ".log";
  std::string res_file_name = output_dir + filename + ".res";
  
  if (!verbose)
    auto __placeholder = freopen (stdout_filename.c_str (), "w", stdout);
  ofstream res_file;
  res_file.open (res_file_name.c_str ());
  
  //write the Bad states to dot file
  if (gv)
  {
    std::string dot_file_name = output_dir + filename + ".gv";
    dot_file = new ofstream ();
    dot_file->open (dot_file_name.c_str ());
    //prepare the dot header
    (*dot_file) << "graph system {\n\t\t\tnode [shape = point];\n\t\t\tedge [penwidth = 0.1];\n\t\t\tratio = auto;";
  }
  
  stats.count_total_time_start ();
  //get aiger object
   aiger* aig = aiger_init ();
   aiger_open_and_read_from_file(aig, input.c_str());
   if (aiger_error(aig)) 
   {
     printf ("read aiger file error!\n");
     exit (0);
   }
   if (!aiger_is_reencoded(aig))
     aiger_reencode(aig);
     
   stats.count_model_construct_time_start ();
   model = new Model (aig);
   stats.count_model_construct_time_end ();
   
   if (verbose)
    model->print ();
   
   State::set_num_inputs_and_latches (model->num_inputs (), model->num_latches ());
   
   // if no output is specified, there is nothing to be checked.
   if(model->num_outputs() > 0){

   ch = new Checker (model, stats, dot_file, forward, evidence, partial, propagate, begin, end, inter, rotate, verbose, minimal_uc,ilock);

   aiger_reset(aig);
   bool res = false;
   if (index_to_be_checked == -1)
     res = ch->check(res_file);
   else
     res = ch->check(res_file, index_to_be_checked);
   }
   delete model;
   model = NULL;
   res_file.close ();
   
   //write the dot file tail
   if (dot_file != NULL)
   {
        (*dot_file) << "\n}" << endl;
        dot_file->close ();
        delete dot_file;
        dot_file = NULL;
   }
   stats.count_total_time_end ();
   stats.print ();
   delete ch;
   ch = NULL;
   return;
}


int main (int argc, char ** argv)
{
  signal (SIGINT, signal_handler);
  check_aiger (argc, argv);
  
  return 0;
}
