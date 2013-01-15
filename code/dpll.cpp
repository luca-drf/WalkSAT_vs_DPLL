//**********************************************************************//
// 11/17/2012                                                           //
//                                                                      //
// Natural language SAT solver using DPLL algorithm.                    //
//                                                                      //
// Luca Da Rin Fioretto                            ldarinfi@cs.nmsu.edu //
//**********************************************************************//


#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <unistd.h>
#include <algorithm>

using std::vector;
using std::cout;
using std::endl;
using std::string;
using std::ifstream;

vector< vector<int> > kb;            // Matrix that stores the KB (and the negated query.)
vector<string> labels;               // Variables labels. labels[n] == vars[n+1].
vector<int> vars, mask, pure, buffer;// Variables valuses starts from vars[1] for commodity.
int cl_number; // Number of clauses (considering the query).


#include "io.h"

// Testing function for a solution found by DPLL algorithm.
// This function is only a test and is not used by DPLL.
void test_model ()
{
    bool not_sat = false;
    int var, cl;
    vector<int>::iterator vars_it, li_it;

    for (cl = 0; cl < cl_number; cl++)
        mask[cl] = 0;
    
    for (var = 1, vars_it = vars.begin() + 1; vars_it != vars.end(); vars_it++, var++)
    {
        for (cl = 0; cl < cl_number; cl++)
        {
            if (mask[cl] == 1) continue;

            for (li_it = kb[cl].begin(); li_it != kb[cl].end(); li_it++)
            {
                if (var == abs(*li_it))
                {
                    if ((*vars_it == 0 && *li_it < 0) ||
                        (*vars_it == 1 && *li_it > 0))
                    {
                        mask[cl] = 1;
                        break;
                    }
                }
            }
        }
    }

    for (cl = 0; cl < cl_number; cl++)
    {
        if (mask[cl] == 0)
        {
            cout << "Clause " << cl << " not sat." << endl;
            not_sat = true;
        }
    }

    if (!not_sat) cout << "All good!" << endl;
}


// Function that returns wether a literal is in the pure vector or not.

bool not_in_pure ( int li )
{
    vector<int>::iterator pure_it;

    for (pure_it = pure.begin(); pure_it != pure.end(); pure_it++)
        if (abs(*pure_it) == abs(li)) return false;

    return true;
}


// Function that searches over not yet satisfied clauses
// if a given literal is pure and returns it as an iterator.
// Otherwise it will only return false.

bool find_pure ( vector<int>::iterator & li_it )
{
    if (pure.size() != 0)
    {
        int cl;
        bool stop;
        vector<int>::iterator pure_it, li;

        for (pure_it = pure.begin(); pure_it != pure.end(); pure_it++)
        {
            stop = false;
            for (cl = 0; cl < cl_number; cl++)
            {
                if (stop) break;

                if (mask[cl] > 0)
                    for (li = kb[cl].begin(); li != kb[cl].end(); li++)
                    {
                        if (*pure_it == -(*li)) 
                        {
                            stop = true;
                        }
                        if (cl == (cl_number - 1) && 
                            li == (kb[cl].end() - 1) &&
                            !stop)
                        {
                            li_it = pure_it;
                            return true;
                        }
                        if (stop) break;
                    }
            }
        }
    }
    return false;
}


// Function that counts the non-ground literals for each clause and
// stores this value into mask the "mask" vector.
// Moreover this function fills the "pure" vector with the literals
// that have to be considered in searching for pures.

int propagation ( vector<int>::iterator & li_it )
{
    size_t cl;
    int min = 0, maybe_sat;           // 2 surely sat, 1 maybe, 0 unsat
    vector<int>::iterator li, temp;
    bool initial = true;

    pure.erase( pure.begin(), pure.end() );

    for (cl = 0; cl < cl_number; cl++)
    {
        // cout << "Clause: " << cl << endl;
        mask[cl] = 0;
        maybe_sat = 0;
        li = kb[cl].begin();

        // This loop is iterating over the clause.
        while ((maybe_sat < 2) && (li != kb[cl].end()))
        {
            if (not_in_pure( *li ) &&
               (vars[abs(*li)] == -1) ) buffer.push_back( *li );

            if ((*li < 0 && vars[abs(*li)] == 0) || 
                (*li > 0 && vars[abs(*li)] == 1))
            {
                // cout << "Clause sat" << endl;
                mask[cl] = 0;
                maybe_sat = 2;
                buffer.erase( buffer.begin(), buffer.end() );
            }
            else if (vars[abs(*li)] == -1)
            {
                // cout << "Counting lit: " << *li << endl;
                mask[cl]++;
                temp = li;
                li++;
                maybe_sat = 1;
            }
            else li++;
        }// while
        if (buffer.size() != 0)
        {
            pure.insert( pure.end(), buffer.begin(), buffer.end() );
            buffer.erase( buffer.begin(), buffer.end() );
        }
        if (li == kb[cl].end() && maybe_sat == 0)
        {
            mask[cl] = -1;
            // cout << "Clause false" << endl;
        }
        if (initial && (mask[cl] != 0))
        {
            min = cl;
            li_it = li;
            initial = false;
        }
        if (!initial && (mask[cl] != 0) && (mask[cl] < mask[min] ||
            (mask[cl] == mask[min] && li_it > temp)))
        {
            min = cl;
            li_it = temp;
        }
    }// for
    return min;
}


// DPLL algorithm.

bool DPLL ()
{
    size_t cl;
    int pos, symbol;
    bool good = false, pures = false;
    vector<int>::iterator li_it;

    // cout << "DPLL" << endl;

    cl = propagation( li_it );


    if (mask[cl] < 0) good = false;
    else if (mask[cl] == 0) good = true;
    else if (find_pure( li_it ))
    {
        pos = (*li_it > 0);
        symbol = abs(*li_it);

        vars[symbol] = pos;
        cout << "Found pure symbol: " << print_var( li_it ) << endl;
        good = DPLL();

    }
    else if (mask[cl] > 0)
    {
        pos = (*li_it > 0);
        symbol = abs(*li_it);

        if (mask[cl] == 1)
        {
            vars[symbol] = pos;
            cout << "Found unit clause: " << print_var( li_it ) << endl;
            good = DPLL();
        }
        else{
            vars[symbol] = pos;
            cout << "Non deterministic choice positive: "
                 << print_var( li_it ) << endl;
            good = DPLL();

            if (!good)
            {
                vars[symbol] = 1 - pos;
                cout << "Non deterministic choice negative: "
                     << print_var( li_it ) << endl;
                good = DPLL();
            }
        }
        if (!good) vars[symbol] = -1;
    }
    return good;
}




int main (int argc, char** argv)
{
    char *input_file = NULL;
    char c;
    bool result;

    // Command line parameters processing.
    while ((c = getopt (argc, argv, "i:")) != -1)
      switch (c)
      {
        case 'i':
          input_file = optarg;
          break;
        case '?':
          if (optopt == 'c')
            fprintf (stderr, "Option -%c requires an argument.\n", optopt);
          else if (isprint (optopt))
            fprintf (stderr, "Unknown option `-%c'.\n", optopt);
          else
            fprintf (stderr,
                     "Unknown option character `\\x%x'.\n",
                     optopt);
          return 1;
        default:
          abort ();
        }

    if (input_file == NULL){
        cout << "Usage: -i path/to/some/input_file.txt" << endl;
        return 1;
    }


    vars.push_back(0);

    // This call loads the KB from the input file. The KB is
    // represented as integers in a matrix, each rows contains a clause.
    // Each literal can be positive or negative (negated).
    if (!load_kb( input_file, kb, labels, vars ))
        return 1;

    // In "mask" the number of ground literal for each clause will be stored.
    for (int i = 0; i < cl_number; i++)
        mask.push_back( 0 );

    // Uncomment the following lines to see how the KB is represented.
    // print_kb();
    // print_variables();

    cout << endl;

    result = DPLL();

    cout << endl << "Query is entailed by the KB: ";
    if (result) cout << "NO" << endl;
    else cout << "YES" << endl;

    // Uncomment the following line to test if a true model satisfies
    // the KB.
    // if (result) test_model();

    return 0;
}

