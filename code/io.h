#ifndef IO_H_
#define IO_H_

string print_var ( const vector<int>::iterator & li_it )
{
    string name = labels[abs(*li_it) - 1];
    name += ": ";
    
    if (vars[abs(*li_it)] > 0) name += 'T';
    else name += 'F';
    
    return name;
}

string print_var ( unsigned int var )
{
    string name = labels[var - 1];
    name += ": ";
    
    if (vars[var] > 0) name += 'T';
    else name += 'F';
    
    return name;

}

void print_model ()
{
    unsigned int var;
    vector<int>::iterator vars_it;
    // cout << "= Assignment =" << endl;
    for (var = 1, vars_it = vars.begin() + 1; vars_it != vars.end(); var++, vars_it++)
        cout << print_var( var ) << endl;
}

// void print_mask ()
// {
//     vector<int>::iterator cl;
//     cout << "= Mask =" << endl;
//     for (cl = mask.begin(); cl != mask.end(); cl++)
//         cout << *cl << endl;
// }

// void print_true_clause ()
// {
//     vector<bool>::iterator cl;
//     cout << "= True Clauses =" << endl;
//     for (cl = true_clause.begin(); cl != true_clause.end(); cl++)
//         cout << *cl << endl;
// }


void print_kb ()
{
    cout << "= KB =" << endl;
    
    for (size_t row = 0; row <= cl_number; row++)
    {
        for (size_t col = 0; col < kb[row].size(); col++)
            cout << kb[row][col] << " ";
        
        cout << endl;
    }
    cout << endl;
}

void print_variables ()
{
    vector<string>::iterator var_it;
    int v_i;
    
    cout << "= Variables =" << endl;

    for (v_i = 1, var_it = labels.begin(); var_it != labels.end(); var_it++,v_i++)
        cout << v_i << ": " << *var_it << endl;
    cout << endl;
}

int is_in ( const string variable, vector<string> & labels )
{
    vector<string>::iterator c;
    int i;
    for (i = 1, c = labels.begin(); c != labels.end(); c++, i++)
        if(c->compare( variable ) == 0) return i;
    return -1;
}

bool load_kb( const char * input_file,
                    vector< vector<int> > & kb,
                    vector<string> & labels,
                    vector<int> & vars )
{
    string line, variable;
    size_t pos, new_var_pos = 0;
    int row = 1, col = 0;
    short sign;

    ifstream input( input_file );
    if (input.is_open())
    {

        getline( input, line );
        variable = line;
        labels.push_back( variable );      // Insert the query.
        vars.push_back( -1 );              // Insert the query variable as unset.

        getline( input, line );
        cl_number = atoi(line.c_str()) + 1;

        kb.reserve( cl_number + 1 );
        kb[0].push_back( -1 );

        while (input.good())
        {
            getline( input, line );

            while (pos != -1)
            {
                pos = line.rfind( ' ' );
                variable = line.substr( pos + 1 );

                if (variable[0] == '~')
                {
                    sign = -1;
                    variable.erase( variable.begin() );
                }
                else sign = 1;

                new_var_pos = is_in( variable, labels );


                if (new_var_pos == -1)     // If the variable is new..
                {
                    labels.push_back( variable );
                    vars.push_back( -1 );

                    if (kb[row].size() != 0) sign *= -1;
                    kb[row].push_back( (vars.size() - 1) * sign );
                }
                else
                {
                    if (kb[row].size() != 0) sign *= -1;
                    kb[row].push_back( new_var_pos * sign );
                    }

                if (pos != -1)
                    line.erase( line.begin() + pos - 3, line.end() );

                col++;

            }
            pos = 0;
            col = 0;
            row++;
        }
        input.close();
        return 1;
    }
    else{
        cout << "Unable to read input file!" << endl;
        return 0;
    }

}

#endif
