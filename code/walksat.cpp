//**********************************************************************//
// 11/17/2012                                                           //
//                                                                      //
// Natural language SAT solver using WalkSAT algorithm.                 //
//                                                                      //
// Luca Da Rin Fioretto ID: 800533544              ldarinfi@cs.nmsu.edu //
//**********************************************************************//


#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <unistd.h>
#include <algorithm>
#include <cstdlib>
#include <ctime>

using std::vector;
using std::cout;
using std::endl;
using std::string;
using std::ifstream;

vector< vector<int> > kb;         // Matrix that stores the KB (and the negated query.)
vector<string> labels;            // Variables labels. labels[n] == vars[n+1].
vector<int> vars, falses;         // Variables valuses starts from vars[1] for commodity.
vector<bool> true_clause;
int cl_number;                    // Number of clauses (considering the query).


#include "io.h"

// Function returning a pseudo-random integer number in [0, range).
// It is designed to uniformally distribute the pseudo-random numbers
// returned by rand() over the given range.

unsigned int i_rand ( unsigned int range )
{
    unsigned int x = (RAND_MAX + 1u) / range;
    unsigned int y = x * range;
    unsigned int r;

    do
    {
        r = rand();
    }
    while (r >= y);

    return (r / x);
}


// Function returning a pseudo-random float number in [0, 1).

float f_rand ()
{
    return ((float)rand()) / ((float)RAND_MAX + 1.0);
}


// Function returning the ratio positive/negative or negative/positive
// literals for a given variable.

float pos_vs_neg( unsigned int var )
{
    unsigned int pos = 0, neg = 0, cl, li;

    for (cl = 0; cl < cl_number; cl++)
        for (li = 0; li < kb[cl].size(); li++)
        {
            if ((kb[cl][li] > 0) && abs(kb[cl][li]) == var) pos++;
            if ((kb[cl][li] < 0) && abs(kb[cl][li]) == var) neg++;
            // cout << "Lit: " << kb[cl][li] << endl;
        }

    // cout << "Var: " << var
    //      << " Neg: " << neg << " Pos: " << pos << endl;

    if (pos == neg) return 0;
    else if (pos = 0) return -1;
    else if (neg = 0) return 1;
    else if (pos > neg) return neg / pos;
    else if (neg > pos) return -(pos / neg);

}


// Function returning the number of satisfied clauses for the current
// model. The clauses found to be false are saved in falses vector for
// further use.

int test_model ()
{
    bool not_sat = false;
    int var, cl;
    vector<int>::iterator vars_it, li_it;

    for (cl = 0; cl < cl_number; cl++)
        true_clause[cl] = false;
    
    for (var = 1, vars_it = vars.begin() + 1; vars_it != vars.end(); vars_it++, var++)
    {
        for (cl = 0; cl < cl_number; cl++)
        {
            if (true_clause[cl]) continue;

            for (li_it = kb[cl].begin(); li_it != kb[cl].end(); li_it++)
            {
                if (var == abs(*li_it))
                {
                    if ((*vars_it == 0 && *li_it < 0) ||
                        (*vars_it == 1 && *li_it > 0))
                    {
                        true_clause[cl] = true;
                        break;
                    }
                }
            }
        }
    }

    for (cl = 0; cl < cl_number; cl++)
    {
        if (!true_clause[cl])
        {
            falses.push_back( cl );
            not_sat = true;
        }
    }

    if (!not_sat) return cl_number;
    else return cl_number - falses.size();
}


// Function that flip the literal of a given clause that maximizes
// the number of true clauses.

void climb ( unsigned int cl, unsigned int true_clauses )
{
    unsigned int result;
    int best_lit = -1;
    vector<int>::iterator li_it;

    for (li_it = kb[cl].begin(); li_it != kb[cl].end(); li_it++)
    {
        // cout << "Climb clause: " << cl << " ";

        vars[abs(*li_it)] = (vars[abs(*li_it)] + 1) % 2;
        result = test_model();
        vars[abs(*li_it)] = (vars[abs(*li_it)] + 1) % 2;

        if (result > true_clauses)
        {
            best_lit = abs(*li_it);
            true_clauses = result;
        }
    }
    if (best_lit != -1)
    {
        vars[best_lit] = (vars[best_lit] + 1) % 2;
        // cout << "flipped best lit: " << best_lit << endl;
    }
    // else cout << "No best lit" << endl;
}


// Function that flips a random literal of a given clause.

void flip_random_lit ( unsigned int cl )
{
    int lit = abs(kb[cl][i_rand( kb[cl].size() )]);
    vars[lit] = (vars[lit] + 1) % 2;
    // cout << "Clause: " << cl << " ";
    // cout << "random flipped: " << lit << endl;
}


// WalkSAT algorithm.

bool walksat ( int mf, int pr )
{
    unsigned int true_clauses;
    unsigned int clause;

    for (int i = 0; i < mf; i++)
    {
        // cout << i << " iteration" << endl;
        true_clauses = test_model();

        if (true_clauses == cl_number) return true;
        else
        {
            clause = falses[i_rand( falses.size() )];

            if (f_rand() < ((float)pr / ((float)100)))
                    flip_random_lit( clause );
            else climb( clause, true_clauses );
        }
    }
    return false;
}



int main (int argc, char** argv)
{
    char *input_file = NULL;
    char c;
    bool result, h = false;
    int mf = -1, pr = -1;
    unsigned int var;
    float ratio;

    srand((unsigned)time(NULL));

    // Command line parameters processing.
    while ((c = getopt (argc, argv, "i:f:p:H")) != -1)
      switch (c)
      {
        case 'i':
          input_file = optarg;
          break;
        case 'f':
          mf = atoi(optarg);
          break;
        case 'p':
          pr = atof(optarg);
          break;
        case 'H':
          h = true;
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
    if (pr < 0 || pr > 100){
        cout << "Please specify a valid probability." << endl;
        return 1;
    }
    if (mf < 0){
        cout << "Please specify a \"maxflips\" number greater than zero." << endl;
        return 1;
    }

    vars.push_back(0);

    // This call loads the KB from the input file. The KB is
    // represented as integers in a matrix, each rows contains a clause.
    // Each literal can be positive or negative (negated).
    if (!load_kb( input_file, kb, labels, vars ))
        return 1;

    // In "true_clause" the truth value of a clause will be stored.
    for (int i = 0; i < cl_number; i++)
        true_clause.push_back( false );

    // Uncomment the following lines to see how the KB is represented.
    // print_kb();
    // print_variables();

    cout << endl;

    vector<int>::iterator vars_it;

    // User defined choice between random or probabilistic
    // initialization.
    if (!h)
    {
        for (vars_it = vars.begin() + 1; vars_it != vars.end(); vars_it++)
            *vars_it = i_rand( 2 );
    }
    else
    {
        for (var = 1, vars_it = vars.begin() + 1; vars_it != vars.end(); vars_it++, var++)
        {
            ratio = pos_vs_neg( var );

            if (ratio == 0) *vars_it = i_rand( 2 );
            else if (ratio == 1) *vars_it = 1;
            else if (ratio == -1) *vars_it = 0;
            else if (ratio > 0) *vars_it = (f_rand() > ratio ? 1 : 0);
            else *vars_it = (f_rand() > -ratio ? 0 : 1);
        }
    }


    cout << "Initial truth values:" << endl;
    print_model();

    result = walksat( mf, pr );

    cout << endl << "Final truth values:" << endl;
    print_model();

    cout << endl << "Query is entailed by the KB: ";
    if (result) cout << "NO" << endl;
    else cout << "YES" << endl;
    return 0;
}

