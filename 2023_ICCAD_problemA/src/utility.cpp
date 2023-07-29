#include <iostream>
#include <cstdlib>
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <map>
#include <cstring>
#include <sstream>
#include <set>
#include <ctime>
#include <algorithm>
#include "utility.h"
#include "timer.h"
#include "cadical.hpp"

using namespace std;
int var;
Timer t;
clock_t start_time, current_time;
std::chrono::steady_clock::time_point current_time_2, start_time_2;
fstream * support_set_file, * aig_to_cnf_number_file, * cnf_file_1, * cnf_file_2;
FILE * cnf_file_3;

vector<pair<long long int, string>> circuit_1_structural_support_set_size, circuit_2_structural_support_set_size;
unordered_map<string, long long int> structural_support_set_size_1, structural_support_set_size_2;
unordered_map<string, vector<string>> circuit_1_structural_support_set, circuit_2_structural_support_set;
vector<pair<long long int, string>> circuit_1_functional_support_set_size, circuit_2_functional_support_set_size;
unordered_map<string, long long int> functional_support_set_size_1, functional_support_set_size_2;
unordered_map<string, vector<string>> circuit_1_functional_support_set, circuit_2_functional_support_set;
vector<pair<pair<long long int, long long int>, string>> circuit_1_support_set_size, circuit_2_support_set_size;

unordered_map<string, string> circuit_1_aig_cnf_mapping, circuit_1_aig_cnf_input_mapping, circuit_1_aig_cnf_output_mapping;
unordered_map<string, string> circuit_2_aig_cnf_mapping, circuit_2_aig_cnf_input_mapping, circuit_2_aig_cnf_output_mapping;
unordered_map<string, string> circuit_1_port_cnf_input_mapping, circuit_1_port_cnf_output_mapping;
unordered_map<string, string> circuit_2_port_cnf_input_mapping, circuit_2_port_cnf_output_mapping;
unordered_map<string, string> circuit_1_cnf_port_input_mapping, circuit_1_cnf_port_output_mapping;
unordered_map<string, string> circuit_2_cnf_port_input_mapping, circuit_2_cnf_port_output_mapping;

unordered_map<string, long long int > circuit_1_port_id_input_mapping, circuit_2_port_id_input_mapping;
unordered_map<string, long long int > circuit_1_port_id_output_mapping, circuit_2_port_id_output_mapping;

long long int input_table_number_start, input_table_number_end;
map<pair<string, string>, string> input_pair_table;
string ** input_pair_matrix;
long long int output_table_number_start, output_table_number_end;
map<pair<string, string>, string> output_pair_table;
vector<string> constraint_0;
long long int constraint_1_start, constraint_1_end;
vector<string> constraint_1;
long long int constraint_2_start, constraint_2_end;
vector<string> constraint_2;
map<pair<string, string>, string> bus_pair_table;
long long int constraint_3_start, constraint_3_end;
vector<string> constraint_3;
bool bus_direct_match = false;
long long int constraint_4_start, constraint_4_end;
vector<vector<string>> constraint_4;
long long int constraint_5_start, constraint_5_end;
vector<string> constraint_5;
vector<vector<string>> learned_clause;
vector<vector<string>> circuit_1_output_group, circuit_2_output_group;
fstream *solve_mapping_file, *solve_miter_file, *solve_mapping_file_result, *solve_miter_file_result, *final_file;
vector<bool> solve_mapping_file_result_record, solve_miter_file_result_record;
map<string, vector<pair<bool, string>>> output_group, input_group;
unordered_map<string, bool> buffer_phase;
vector<string> circuit_1_zero_support, circuit_2_zero_support;
unordered_map<string, bool> circuit_1_is_input, circuit_2_is_input;
long long int miter_start, miter_end;
unordered_map<long long int, pair<string, string>> miter_unequal_output;
unordered_map<string, long long int> circuit_1_input_support_size, circuit_2_input_support_size;

//record the support inputs of the current matching outputs 
unordered_map<string, bool> support_input_1, support_input_2;

typedef struct cnf_file cnf_file;
struct cnf_file{
    long long int number_of_variables;
    long long int number_of_clauses;
    vector<string> clauses, clauses2;
} circuit1_cnf, circuit2_cnf, total_cnf;
vector<string> circuit1_cnf_clauses, circuit2_cnf_clauses;
long long int circuit1_cnf_number_of_variables, circuit2_cnf_number_of_variables;
long long int circuit1_cnf_number_of_clauses, circuit2_cnf_number_of_clauses;

inline int MiniSAT(string SAT_input_file, string SAT_output_file){
    string cmd = "./lib/minisat-master/build/dynamic/bin/minisat -verb=0 " + SAT_input_file + " " + SAT_output_file;
    return system(cmd.c_str());
}

bool CaDiCaL_Solver(string file, CaDiCaL::Solver& solver){
    solver.read_dimacs(file.c_str(), var, 0);

    int result = solver.solve();
    // cout << "result: " << result << endl;
    if (result == 10) {
        cout << "SATISFIABLE" << endl;
        return true;
    }else if(result == 20){
        cout << "UNSATISFIABLE" << endl;
        return false;
    }
}

long long int factorial(unsigned int n)
{
    if (n == 0 || n == 1)
        return 1;
    return n * factorial(n - 1);
}
// void* new2d(int h, int w, int size)
// {
//     int i;
//     void **p;

//     p = (void**)new char[h*sizeof(void*) + h*w*size];
//     for(i = 0; i < h; i++)
//         p[i] = ((char *)(p + h)) + i*w*size;

//     return p;
// }
// #define NEW2D(H, W, TYPE) (TYPE **)new2d(H, W, sizeof(TYPE))

void construct_final_result_file(string file_name, vector<pair<bool, pair<string, string>>> output_matching_result){
    final_file = new fstream;
    final_file->open(file_name.c_str(), std::ios::out);
    if(!final_file->is_open()){
        cout << "Open Fail:" << "final_file" << endl;
        exit(1);
    }else{
        //INPUT GROUP
        bool first = true;
        for(long long int i=0; i<circuit_1_number_of_inputs; i++){
            for(long long int j=0; j<circuit_2_number_of_inputs; j++){
                if(solve_mapping_file_result_record[stoll(input_pair_matrix[j][2*i])]){
                    if(first){
                        (*final_file) << "INGROUP" << '\n';
                        (*final_file) << "1 + "<< circuit_1_input[i] << '\n';
                        first = false;
                    }
                    (*final_file) << "2 + " << circuit_2_input[j] << '\n';
                }
                if(solve_mapping_file_result_record[stoll(input_pair_matrix[j][2*i+1])]){
                    if(first){
                        (*final_file) << "INGROUP" << '\n';
                        (*final_file) << "1 + "<< circuit_1_input[i] << '\n';
                        first = false;
                    }
                    (*final_file) << "2 - " << circuit_2_input[j] << '\n';
                }
            }
            if(!first) (*final_file) << "END" << '\n';
            first = true;
        }

        //OUTPUT GROUP
        first = true;
        long long int score = 0;
        for(auto f : circuit_1_output){
            for(auto p : output_matching_result){
                if((p.second).first == f){
                    if(first){
                        (*final_file) << "OUTGROUP" << '\n';
                        (*final_file) << "1 + "<< f << '\n';
                        first = false;
                        score++;
                    }
                    (*final_file) << "2 " << ((p.first)?"+ ":"- ") << (p.second).second << '\n';
                    score++;
                }
            }
            if(!first) (*final_file) << "END" << '\n';
            first = true;
        }
        cout << "SCORE: " << score << endl;

        //CONSTANT GROUP
        first = true;
        //constant 0
        for(long long int i=0; i<circuit_2_number_of_inputs; i++){
            if(solve_mapping_file_result_record[stoll(input_pair_matrix[i][2*circuit_1_number_of_inputs])]){
                if(first){
                    (*final_file) << "CONSTGROUP" << '\n';
                    first = false;
                }
                (*final_file) << "+ " << circuit_2_input[i] << '\n';
            }
        }
        //constant 1
        for(long long int i=0; i<circuit_2_number_of_inputs; i++){
            if(solve_mapping_file_result_record[stoll(input_pair_matrix[i][2*circuit_1_number_of_inputs+1])]){
                if(first){
                    (*final_file) << "CONSTGROUP" << '\n';
                    first = false;
                }
                (*final_file) << "- " << circuit_2_input[i] << '\n';
            }
        }
        if(!first) (*final_file) << "END" << '\n';

        final_file->close();
        final_file->clear();
    }
    // final_file = new fstream;
    // final_file->open(file_name.c_str(), std::ios::out);
    // if(!final_file->is_open()){
    //     cout << "Open Fail:" << "final_file" << endl;
    //     exit(1);
    // }else{
    //     //INPUT GROUP
    //     bool first = true;
    //     for(auto x : circuit_1_input){
    //         for(auto y : circuit_2_input){
    //             if(solve_mapping_file_result_record[stoll(input_pair_table[pair<string, string>(x,y)])].second){
    //                 if(first){
    //                     (*final_file) << "INGROUP" << '\n';
    //                     (*final_file) << "1 + "<< x << '\n';
    //                     first = false;
    //                 }
    //                 (*final_file) << "2 + " << y << '\n';
    //             }
    //             else if(solve_mapping_file_result_record[stoll(input_pair_table[pair<string, string>("-"+x,y)])].second){
    //                 if(first){
    //                     (*final_file) << "INGROUP" << '\n';
    //                     (*final_file) << "1 + "<< x << '\n';
    //                     first = false;
    //                 }
    //                 (*final_file) << "2 - " << y << '\n';
    //             }
    //         }
    //         if(!first) (*final_file) << "END" << '\n';
    //         first = true;
    //     }

    //     //OUTPUT GROUP
    //     first = true;
    //     for(auto f : circuit_1_output){
    //         for(auto p : output_matching_result){
    //             if((p.second).first == f){
    //                 if(first){
    //                     (*final_file) << "OUTGROUP" << '\n';
    //                     (*final_file) << "1 + "<< f << '\n';
    //                     first = false;
    //                 }
    //                 (*final_file) << "2 " << ((p.first)?"+ ":"- ") << (p.second).second << '\n';
    //             }
    //         }
    //         if(!first) (*final_file) << "END" << '\n';
    //         first = true;
    //     }

    //     //CONSTANT GROUP
    //     first = true;
    //     string x = "0";
    //     for(auto y : circuit_2_input){
    //         if(solve_mapping_file_result_record[stoll(input_pair_table[pair<string, string>(x,y)])].second){
    //             if(first){
    //                 (*final_file) << "CONSTGROUP" << '\n';
    //                 first = false;
    //             }
    //             (*final_file) << "+ " << y << '\n';
    //         }
    //     }

    //     x = "1";
    //     for(auto y : circuit_2_input){
    //         if(solve_mapping_file_result_record[stoll(input_pair_table[pair<string, string>(x,y)])].second){
    //             if(first){
    //                 (*final_file) << "CONSTGROUP" << '\n';
    //                 first = false;
    //             }
    //             (*final_file) << "- " << y << '\n';
    //         }
    //     }
    //     if(!first) (*final_file) << "END" << '\n';

    //     final_file->close();
    //     final_file->clear();
    // }
}

void construct_learned_clauses(vector<pair<bool, pair<string, string>>> output_matching_result){
    //get the result from mapping file result
    // string line, res;
    // stringstream ss;
    // solve_miter_file_result = new fstream;
    // solve_miter_file_result->open("solve_miter_file_result.cnf", std::ios::in);
    // solve_miter_file_result_record.clear();

    // getline((*solve_miter_file_result), line);
    // getline((*solve_miter_file_result), line);
    // ss << line;
    // solve_miter_file_result_record.emplace_back(make_pair("0", true));
    // while(getline(ss, res, ' ')){
    //     if(res[0] == '-'){
    //         solve_miter_file_result_record.emplace_back(make_pair(res.substr(1), false));
    //     }
    //     else{
    //         solve_miter_file_result_record.emplace_back(make_pair(res, true));
    //     }
    // }
    // solve_miter_file_result->close();
    // solve_miter_file_result->clear();

    //add learned clause
    for(long long int i=miter_start; i<=miter_end; i++){   
        // if(!(solve_miter_file_result_record[i]).second) continue;
        if(!solve_miter_file_result_record[i]) continue;
        // pair<bool, pair<string, string>> &last_pair = output_matching_result.back();
        pair<bool, pair<string, string>> last_pair = pair<bool, pair<string, string>>(true, miter_unequal_output[i]);
        cout << "miter output: " << (last_pair.second).first << ", " << (last_pair.second).second << endl;
        
        vector<string> &last_learned_clauses = learned_clause.back();
        string clause;
        // cout << "current pair: " << (last_pair.second).first << ", " << (last_pair.second).second << endl;
        // for(auto y : circuit_2_functional_support_set[(last_pair.second).second]){
        //     for(auto x : circuit_1_functional_support_set[(last_pair.second).first]){
        //         // cout << "LEARNED CLAUSE SUPP: " << x << " " << y << endl;
        //         string x_num = circuit_1_port_cnf_input_mapping[x];
        //         string y_num = circuit_2_port_cnf_input_mapping[y];
        //         // cout << x << " = " << (((solve_miter_file_result_record[stoll(x_num)]).second)?"1":"0") << endl;
        //         // cout << y << " = " << (((solve_miter_file_result_record[stoll(y_num)]).second)?"1":"0") << endl;

        //         if((solve_miter_file_result_record[stoll(x_num)]).second && (solve_miter_file_result_record[stoll(y_num)]).second){
        //             clause += input_pair_table[pair<string, string>("-"+x, y)] + " ";
        //         }
        //         else if(!(solve_miter_file_result_record[stoll(x_num)]).second && !(solve_miter_file_result_record[stoll(y_num)]).second){
        //             clause += input_pair_table[pair<string, string>("-"+x, y)] + " ";
        //         }
        //         else if(!(solve_miter_file_result_record[stoll(x_num)]).second && (solve_miter_file_result_record[stoll(y_num)]).second){
        //             clause += input_pair_table[pair<string, string>(x, y)] + " ";
        //         }
        //         else if((solve_miter_file_result_record[stoll(x_num)]).second && !(solve_miter_file_result_record[stoll(y_num)]).second){
        //             clause += input_pair_table[pair<string, string>(x, y)] + " ";
        //         }
        //     }
        // }
        for(auto y : circuit_2_functional_support_set[(last_pair.second).second]){
            for(auto x : circuit_1_functional_support_set[(last_pair.second).first]){
                // cout << "LEARNED CLAUSE SUPP: " << x << " " << y << endl;
                string x_num = circuit_1_port_cnf_input_mapping[x];
                string y_num = circuit_2_port_cnf_input_mapping[y];
                // cout << x << " = " << (((solve_miter_file_result_record[stoll(x_num)]).second)?"1":"0") << endl;
                // cout << y << " = " << (((solve_miter_file_result_record[stoll(y_num)]).second)?"1":"0") << endl;
                // if((CaDiCaL_Result(stoll(x_num)) && CaDiCaL_Result(stoll(y_num))) || (!CaDiCaL_Result(stoll(x_num)) && !CaDiCaL_Result(stoll(y_num)))){
                //     clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_port_id_input_mapping[x]+1] + " ";
                // }
                // else if((!CaDiCaL_Result(stoll(x_num)) && CaDiCaL_Result(stoll(y_num))) || (CaDiCaL_Result(stoll(x_num)) && !CaDiCaL_Result(stoll(y_num)))){
                //     clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_port_id_input_mapping[x]] + " ";
                // }
                if((solve_miter_file_result_record[stoll(x_num)] && solve_miter_file_result_record[stoll(y_num)]) || (!solve_miter_file_result_record[stoll(x_num)] && !solve_miter_file_result_record[stoll(y_num)])){
                    clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_port_id_input_mapping[x]+1] + " ";
                }
                else if((!solve_miter_file_result_record[stoll(x_num)] && solve_miter_file_result_record[stoll(y_num)]) || (solve_miter_file_result_record[stoll(x_num)] && !solve_miter_file_result_record[stoll(y_num)])){
                    clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_port_id_input_mapping[x]] + " ";
                }
                // if((solve_miter_file_result_record[stoll(x_num)]).second && (solve_miter_file_result_record[stoll(y_num)]).second){
                //     clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_port_id_input_mapping[x]+1] + " ";
                // }
                // else if(!(solve_miter_file_result_record[stoll(x_num)]).second && !(solve_miter_file_result_record[stoll(y_num)]).second){
                //     clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_port_id_input_mapping[x]+1] + " ";
                // }
                // else if(!(solve_miter_file_result_record[stoll(x_num)]).second && (solve_miter_file_result_record[stoll(y_num)]).second){
                //     clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_port_id_input_mapping[x]] + " ";
                // }
                // else if((solve_miter_file_result_record[stoll(x_num)]).second && !(solve_miter_file_result_record[stoll(y_num)]).second){
                //     clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_port_id_input_mapping[x]] + " ";
                // }
            }
        }


        // clause += "0";
        // last_learned_clauses.emplace_back(clause);
        // clause.clear();

        // if(functional_support_set_size_1[(last_pair.second).first] < functional_support_set_size_2[(last_pair.second).second])
        // {   
        //     cout << "ADD CONSTANT LEARNED CLAUSE!" << endl;
        //     // cout << "current pair: " << (last_pair.second).first << ", " << (last_pair.second).second << endl;
        //     cout << "support_set_size: (" << functional_support_set_size_1[(last_pair.second).first] << ", " << functional_support_set_size_2[(last_pair.second).second] << ")" << endl;
        //     for(auto y : circuit_2_functional_support_set[(last_pair.second).second]){
        //         string y_num = circuit_2_port_cnf_input_mapping[y];

        //         if((solve_miter_file_result_record[stoll(y_num)]).second){
        //             clause += input_pair_table[pair<string, string>("0", y)] + " ";
        //         }
        //         else if(!(solve_miter_file_result_record[stoll(y_num)]).second){
        //             clause += input_pair_table[pair<string, string>("1", y)] + " ";
        //         }
        //     }
        // }
        if(functional_support_set_size_1[(last_pair.second).first] < functional_support_set_size_2[(last_pair.second).second])
        {   
            cout << "ADD CONSTANT LEARNED CLAUSE!" << endl;
            // cout << "current pair: " << (last_pair.second).first << ", " << (last_pair.second).second << endl;
            cout << "support_set_size: (" << functional_support_set_size_1[(last_pair.second).first] << ", " << functional_support_set_size_2[(last_pair.second).second] << ")" << endl;
            for(auto y : circuit_2_functional_support_set[(last_pair.second).second]){
                string y_num = circuit_2_port_cnf_input_mapping[y];

                if(solve_miter_file_result_record[stoll(y_num)]){
                    clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_number_of_inputs] + " ";
                }
                else if(!solve_miter_file_result_record[stoll(y_num)]){
                    clause += input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_number_of_inputs+1] + " ";
                }
            }
        }
        clause += "0";
        // last_learned_clauses.emplace_back(clause);
        learned_clause[i-miter_start].emplace_back(clause); //test
    }
    
    // for(auto x : circuit_1_input){
    //     for(auto y : circuit_2_input){
    //         // cout << "LEARNED CLAUSE SUPP: " << x << " " << y << endl;
    //         string x_num = circuit_1_port_cnf_input_mapping[x];
    //         string y_num = circuit_2_port_cnf_input_mapping[y];

    //         if((solve_miter_file_result_record[stoll(x_num)]).second && (solve_miter_file_result_record[stoll(y_num)]).second){
    //             clause += input_pair_table[pair<string, string>("-"+x, y)] + " ";
    //         }
    //         else if(!(solve_miter_file_result_record[stoll(x_num)]).second && !(solve_miter_file_result_record[stoll(y_num)]).second){
    //             clause += input_pair_table[pair<string, string>("-"+x, y)] + " ";
    //         }
    //         else if(!(solve_miter_file_result_record[stoll(x_num)]).second && (solve_miter_file_result_record[stoll(y_num)]).second){
    //             clause += input_pair_table[pair<string, string>(x, y)] + " ";
    //         }
    //         else if((solve_miter_file_result_record[stoll(x_num)]).second && !(solve_miter_file_result_record[stoll(y_num)]).second){
    //             clause += input_pair_table[pair<string, string>(x, y)] + " ";
    //         }
    //     }
    // }
    // for(auto y : circuit_2_input){
    //     string y_num = circuit_2_port_cnf_input_mapping[y];

    //     if((solve_miter_file_result_record[stoll(y_num)]).second){
    //         clause += input_pair_table[pair<string, string>("0", y)] + " ";
    //     }
    //     else if(!(solve_miter_file_result_record[stoll(y_num)]).second){
    //         clause += input_pair_table[pair<string, string>("1", y)] + " ";
    //     }
    // }
    // clause += "0";
    // last_learned_clauses.emplace_back(clause);
    // cout << "ADDING LEARNED CLAUSES OF: " << (last_pair.second).first << ", " << (last_pair.second).second << endl;
    // cout << "ADDING LEARNED CLAUSES: " << clause << endl;
}

bool solve_miter(vector<pair<bool, pair<string, string>>> output_matching_result){
    //get the result from mapping file result
    // string line, res;
    // stringstream ss;
    // solve_mapping_file_result = new fstream;
    // solve_mapping_file_result->open("solve_mapping_file_result.cnf", std::ios::in);
    // solve_mapping_file_result_record.clear();

    // getline((*solve_mapping_file_result), line);
    // getline((*solve_mapping_file_result), line);
    // ss << line;
    // solve_mapping_file_result_record.emplace_back(make_pair("0", true));
    // while(getline(ss, res, ' ')){
    //     if(res[0] == '-'){
    //         solve_mapping_file_result_record.emplace_back(make_pair(res.substr(1), false));
    //     }
    //     else{
    //         solve_mapping_file_result_record.emplace_back(make_pair(res, true));
    //     }
    // }
    // cout << "solve_mapping_file_result_record: ";
    // for(long long int i=input_table_number_start; i<=input_table_number_end; i++) cout << ((solve_mapping_file_result_record[i].second)?"":"-")+solve_mapping_file_result_record[i].first << " ";
    // cout << endl;

    // solve_mapping_file_result->close();
    // solve_mapping_file_result->clear();

    //solve the miter
    solve_miter_file = new fstream;
    solve_miter_file->open("solve_miter_file.cnf", std::ios::out);
    if(!solve_miter_file->is_open()){
        cout << "Open Fail:" << "solve_miter_file.cnf" << endl;
        exit(1);
    }else{
        (*solve_miter_file) << "p cnf 0 0" << '\n';

        //circuit
        for(auto line : total_cnf.clauses){
            (*solve_miter_file) << line << '\n';
        }

        //f != g
        miter_end = miter_start = constraint_3_end+1; //TODO:
        string str;
        for(auto r : output_matching_result){
            string f = circuit_1_port_cnf_output_mapping[(r.second).first];
            string g = circuit_2_port_cnf_output_mapping[(r.second).second];
            str += to_string(miter_end) + " ";
            if(r.first){ //positive f
                (*solve_miter_file) << "-"+to_string(miter_end) + " " +  f + " " + g + " 0" << '\n';
                (*solve_miter_file) << "-"+to_string(miter_end) + " " + "-" + f + " -" + g + " 0" << '\n';

                //test
                (*solve_miter_file) << to_string(miter_end) + " " +  f + " -" + g + " 0" << '\n';
                (*solve_miter_file) << to_string(miter_end) + " " + "-" + f + " " + g + " 0" << '\n';
                // cout << "MITER: " << f + " " + g + " 0" << '\n';
                // cout << "MITER: " << "-" + f + " -" + g + " 0" << '\n';
            }else{ //negative f
                (*solve_miter_file)  << "-"+to_string(miter_end) + " " + "-" + f + " " + g + " 0" << '\n';
                (*solve_miter_file) << "-"+to_string(miter_end) + " " + f + " -" + g + " 0" << '\n';
                
                //test
                (*solve_miter_file)  << to_string(miter_end) + " " + "" + f + " " + g + " 0" << '\n';
                (*solve_miter_file) << to_string(miter_end) + " -" + f + " -" + g + " 0" << '\n';
                // cout << "MITER: " << "-" + f + " " + g + " 0" << '\n';
                // cout << "MITER: " << f + " -" + g + " 0" << '\n';
            }
            miter_unequal_output[miter_end] = pair<string,string>((r.second).first, (r.second).second);
            miter_end++;
        }
        miter_end--;
        str += "0";
        (*solve_miter_file) << str << '\n';

        //binding x to y
        for(auto line : constraint_0){
            (*solve_miter_file) << line << '\n';
        }
        // for(auto line : constraint_1){
        //     (*solve_miter_file) << line << '\n';
        // }

        //current mapping
        for(long long int i=input_table_number_start; i<=input_table_number_end; i++){
            // if(CaDiCaL_Result(i)){
            //     (*solve_miter_file) << to_string(i) << " 0" << '\n';
            // }else{
            //     (*solve_miter_file) << "-"+to_string(i) << " 0" << '\n';
            // }
            if(solve_mapping_file_result_record[i]){
                (*solve_miter_file) << to_string(i) << " 0" << '\n';
            }
            else{
                (*solve_miter_file) << "-"+to_string(i) << " 0" << '\n';
            }
        }
        // for(auto learned_vector : learned_clause){
        //     for(auto clause : learned_vector){
        //         (*solve_miter_file) << clause << '\n';
        //     }
        // }
        solve_miter_file->close();
        solve_miter_file->clear();

        CaDiCaL::Solver solver;
        solver.set("quiet", 1);  
        bool res = CaDiCaL_Solver("solve_miter_file.cnf", solver);
        if(res){
            solve_miter_file_result_record.clear();
            solve_miter_file_result_record.emplace_back(true);
            for (int i = 1; i <= solver.vars(); i++) {
                if (solver.val(i) > 0) {
                    solve_miter_file_result_record.emplace_back(true);
                } else {
                    solve_miter_file_result_record.emplace_back(false);
                }
            }
            return true;
        }
        else return false;

        // MiniSAT("solve_miter_file.cnf", "solve_miter_file_result.cnf");
        // solve_miter_file_result = new fstream;
        // solve_miter_file_result->open("solve_miter_file_result.cnf", std::ios::in);
        // getline((*solve_miter_file_result), line);
        // solve_miter_file_result->close();
        // solve_miter_file_result->clear();

        // if(line == "SAT") return true;
        // else return false;
    }
}

bool solve_mapping(vector<pair<bool, pair<string, string>>> output_matching_result){
    string line;
    solve_mapping_file = new fstream;
    solve_mapping_file->open("solve_mapping_file.cnf", std::ios::out);
    if(!solve_mapping_file->is_open()){
        cout << "Open Fail:" << "solve_mapping_file.cnf" << endl;
        exit(1);
    }else{
        (*solve_mapping_file) << "p cnf 0 0" << '\n';
        
        // for(auto line : total_cnf.clauses){
        //     (*solve_mapping_file) << line << '\n';
        // }
        // for(auto r : output_matching_result){
        //     string f = circuit_1_port_cnf_output_mapping[(r.second).first];
        //     string g = circuit_2_port_cnf_output_mapping[(r.second).second];

        //     if(r.first){ //positive f
        //         (*solve_mapping_file) << "-" + f + " " + g + " 0" << '\n';
        //         (*solve_mapping_file) << f + " -" + g + " 0" << '\n';
        //         // cout << "MAPPING: " << "-" + f + " " + g + " 0" << '\n';
        //         // cout << "MAPPING: " << f + " -" + g + " 0" << '\n';
        //     }else{ //negative f
        //         (*solve_mapping_file) << f + " " + g + " 0" << '\n';
        //         (*solve_mapping_file) << "-" + f + " -" + g + " 0" << '\n';
        //         // cout << "MAPPING: " << f + " " + g + " 0" << '\n';
        //         // cout << "MAPPING: " << "-" + f + " -" + g + " 0" << '\n';
        //     }
        // }

        //input one-to-one
        for(auto line : constraint_0){
            (*solve_mapping_file) << line << '\n';
        }
        for(auto line : constraint_1){
            (*solve_mapping_file) << line << '\n';
        }

        // floating variable
        for(auto line : constraint_2){
            (*solve_mapping_file) << line << '\n';
        }

        // bus constraint
        for(auto line : constraint_3){
            (*solve_mapping_file) << line << '\n';
        }

        //disable input projection and constant binding
        for(auto constraint_vector : constraint_4){
            for(auto clause : constraint_vector){
                (*solve_mapping_file) << clause << '\n';
            }
        }

        //input support size constraint
        for(auto line : constraint_5){
            (*solve_mapping_file) << line << '\n';
        }

        //learned clauses
        for(auto learned_vector : learned_clause){
            for(auto clause : learned_vector){
                (*solve_mapping_file) << clause << '\n';
            }
        }
        solve_mapping_file->close();
        solve_mapping_file->clear();

        CaDiCaL::Solver solver;
        solver.set("quiet", 1);  
        bool res = CaDiCaL_Solver("solve_mapping_file.cnf", solver);
        if(res){
            solve_mapping_file_result_record.clear();
            solve_mapping_file_result_record.emplace_back(true);
            for (int i = 1; i <= solver.vars(); i++) {
                if (solver.val(i) > 0) {
                    solve_mapping_file_result_record.emplace_back(true);
                } else {
                    solve_mapping_file_result_record.emplace_back(false);
                }
            }
            return true;
        }
        else return false;

        // MiniSAT("solve_mapping_file.cnf", "solve_mapping_file_result.cnf");
        // solve_mapping_file_result = new fstream;
        // solve_mapping_file_result->open("solve_mapping_file_result.cnf", std::ios::in);
        // getline((*solve_mapping_file_result), line);
        // solve_mapping_file_result->close();
        // solve_mapping_file_result->clear();

        // if(line == "SAT") return true;
        // else return false;
    }
}

//symmetric constraints 3 (Theorem 3-2)
void construct_constraint_8(){

}

//symmetric constraints 2 (Theorem 3-1)
void construct_constraint_7(){

}

//symmetric constraints 1 (hard symmetric group)
void construct_constraint_6(){

}

//binding two input variables only when their support set sizes are the same
void construct_constraint_5(){
    // for(auto y : circuit_2_input){
    //     for(auto x : circuit_1_input){
    //         if(circuit_1_input_support_size[x] != circuit_2_input_support_size[y]){
    //             constraint_5.emplace_back("-"+input_pair_table[pair<string, string>(x,y)] + " 0");
    //             constraint_5.emplace_back("-"+input_pair_table[pair<string, string>("-"+x,y)] + " 0");
    //         }
    //     }
    // }
    for(long long int i=0; i<circuit_2_number_of_inputs; i++){
        for(long long int j=0; j<circuit_1_number_of_inputs; j++){
            if(circuit_1_input_support_size[circuit_1_input[j]] != circuit_2_input_support_size[circuit_2_input[i]]){
                constraint_5.emplace_back("-"+input_pair_matrix[i][2*j] + " 0");
                constraint_5.emplace_back("-"+input_pair_matrix[i][2*j+1] + " 0");
            }
        }
    }
}

//avoid binding input variable to constant or input projection when two inputs' support set sizes are same
void construct_constraint_4(vector<pair<bool, pair<string, string>>> output_matching_result){
    auto & constraint_vector = constraint_4.back();
    auto last_pair = (output_matching_result.back()).second;

    // long long int circuit_1_input_support_size = 0, circuit_2_input_support_size = 0;
    // for(auto x : circuit_1_input){
    //     if(support_input_1[x]) circuit_1_input_support_size++;
    // }
    // for(auto y : circuit_2_input){
    //     if(support_input_2[y]) circuit_2_input_support_size++;
    // }

    // if(circuit_1_input_support_size == circuit_2_input_support_size){
    //     for(auto p: output_matching_result){
    //         string g = (p.second).second;
    //         for(auto y : circuit_2_functional_support_set[g]){
    //             constraint_vector.emplace_back("-"+input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_number_of_inputs] + " 0");
    //             constraint_vector.emplace_back("-"+input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_number_of_inputs+1] + " 0");
    //         }
    //     }
    // }

    // if(functional_support_set_size_1[last_pair.first] == functional_support_set_size_2[last_pair.second]){
    //     for(auto y : circuit_2_functional_support_set[last_pair.second]){
    //         constraint_vector.emplace_back("-"+input_pair_table[pair<string, string>("0",y)] + " 0");
    //         constraint_vector.emplace_back("-"+input_pair_table[pair<string, string>("1",y)] + " 0");
    //     }
    // }
    if(functional_support_set_size_1[last_pair.first] == functional_support_set_size_2[last_pair.second]){
        for(auto y : circuit_2_functional_support_set[last_pair.second]){
            constraint_vector.emplace_back("-"+input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_number_of_inputs] + " 0");
            constraint_vector.emplace_back("-"+input_pair_matrix[circuit_2_port_id_input_mapping[y]][2*circuit_1_number_of_inputs+1] + " 0");
        }

        long long int funcsupp_size = circuit_2_functional_support_set[last_pair.second].size();
        for(auto x : circuit_1_functional_support_set[last_pair.first]){
            for(long long int i=0; i<funcsupp_size; i++){
                for(long long int j=i+1; j<funcsupp_size; j++){
                    string y1 = circuit_2_functional_support_set[last_pair.second][i];
                    string y2 = circuit_2_functional_support_set[last_pair.second][j];

                    constraint_vector.emplace_back("-"+input_pair_matrix[circuit_2_port_id_input_mapping[y1]][2*circuit_1_port_id_input_mapping[x]] + " -" +input_pair_matrix[circuit_2_port_id_input_mapping[y2]][2*circuit_1_port_id_input_mapping[x]] + " 0");
                    constraint_vector.emplace_back("-"+input_pair_matrix[circuit_2_port_id_input_mapping[y1]][2*circuit_1_port_id_input_mapping[x]+1] + " -" +input_pair_matrix[circuit_2_port_id_input_mapping[y2]][2*circuit_1_port_id_input_mapping[x]+1] + " 0");
                    constraint_vector.emplace_back("-"+input_pair_matrix[circuit_2_port_id_input_mapping[y1]][2*circuit_1_port_id_input_mapping[x]+1] + " -" +input_pair_matrix[circuit_2_port_id_input_mapping[y2]][2*circuit_1_port_id_input_mapping[x]] + " 0");
                    constraint_vector.emplace_back("-"+input_pair_matrix[circuit_2_port_id_input_mapping[y1]][2*circuit_1_port_id_input_mapping[x]] + " -" +input_pair_matrix[circuit_2_port_id_input_mapping[y2]][2*circuit_1_port_id_input_mapping[x]+1] + " 0");
                }
            }
        }
    }
}

//floating variable
void construct_constraint_2(vector<pair<bool, pair<string, string>>> output_matching_result){
    constraint_2.clear();
    for(auto x : circuit_1_input) support_input_1[x] = false;
    for(auto y : circuit_2_input) support_input_2[y] = false;

    for(auto p : output_matching_result){
        string f = (p.second).first;
        for(auto x : circuit_1_functional_support_set[f]){
            support_input_1[x] = true;
        }
    }
    for(auto p : output_matching_result){
        string g = (p.second).second;
        for(auto y : circuit_2_functional_support_set[g]){
            support_input_2[y] = true;
        }
    }
    for(auto x : circuit_1_input){
        if(!support_input_1[x]){
            constraint_2.emplace_back("-"+circuit_1_port_cnf_input_mapping[x] + " 0");
        }
    }

    for(long long int i=0; i<circuit_2_number_of_inputs; i++){
        if(!support_input_2[circuit_2_input[i]]){
            constraint_2.emplace_back("-"+circuit_2_port_cnf_input_mapping[circuit_2_input[i]] + " 0");
            // constraint_2.emplace_back(input_pair_matrix[i][2*circuit_1_number_of_inputs] + " 0");
        }
    }
    // for(long long int i=0; i<circuit_1_number_of_inputs; i++){
    //     for(long long int j=0; j<circuit_2_number_of_inputs; j++){
    //         if(support_input_1[circuit_1_input[i]] && !support_input_2[circuit_2_input[j]]){
    //             constraint_2.emplace_back("-"+input_pair_matrix[j][2*i] + " 0");
    //             constraint_2.emplace_back("-"+input_pair_matrix[j][2*i+1] + " 0");
    //         }
    //     }
    // }
}


//bus constraints
unordered_map<long long int, long long int> permute_record;
vector<vector<long long int>>permutation;
map<vector<long long int>, bool> visited;
inline void permute(vector<long long int>p, long long int circuit_1_bus_size, long long int circuit_2_bus_size){
    if(p.size() == circuit_1_bus_size && visited[p] == false){
        visited[p] = true;
        permutation.emplace_back(p);
        cout << "permutation: ";
        for(auto it : p) cout << it << " ";
        cout << endl;
        return;
    }

    for(long long int i=0; i<circuit_1_bus_size; i++){
        if(permute_record[i] == 0){
            permute_record[i] = 1;
            p.emplace_back(i);
            permute(p, circuit_1_bus_size, circuit_2_bus_size);
            p.pop_back();
            permute_record[i] = 0;
        }
    }

}
inline int bus_mode_check(int cir, long long int bus_size){
    //mode -1: no bus
    //mode 0: only one input bus
    //mode 1: bus-lengths are strictly increasing
    //mode 2: bus-lengths are all the same
    //mode 3: bus-lengths are not strictly increasing
    //mode 4: others
    if(bus_size == 0) return -1;
    if(bus_size == 1) return 0;

    if(cir == 1){
        bool same = true;
        bool strictly_increasing = true;
        for(long long int i=1; i<bus_size; i++){
            if(!same && !strictly_increasing) break;

            if(same && (cir1_input_bus_set[i]).first == (cir1_input_bus_set[i-1]).first){
                same = true;
                strictly_increasing = false;
            }else if(same && (cir1_input_bus_set[i]).first > (cir1_input_bus_set[i-1]).first){
                same = false;
            }
            if(strictly_increasing && (cir1_input_bus_set[i]).first > (cir1_input_bus_set[i-1]).first){
                same = false;
                strictly_increasing = true;
            }
            else if(strictly_increasing && (cir1_input_bus_set[i]).first <= (cir1_input_bus_set[i-1]).first){
                strictly_increasing = false;
            }
        }
        if(same) return 2;
        else if(strictly_increasing) return 1;
        else if(!same && !strictly_increasing) return 3;
        else return 4;
    }
    else if(cir == 2){
        bool same = true;
        bool strictly_increasing = true;
        for(long long int i=1; i<bus_size; i++){
            if(!same && !strictly_increasing) break;

            if(same && (cir2_input_bus_set[i]).first == (cir2_input_bus_set[i-1]).first){
                same = true;
                strictly_increasing = false;
            }else if(same && (cir2_input_bus_set[i]).first > (cir2_input_bus_set[i-1]).first){
                same = false;
            }
            if(strictly_increasing && (cir2_input_bus_set[i]).first > (cir2_input_bus_set[i-1]).first){
                same = false;
                strictly_increasing = true;
            }
            else if(strictly_increasing && (cir2_input_bus_set[i]).first <= (cir2_input_bus_set[i-1]).first){
                strictly_increasing = false;
            }
        }
        if(same) return 2;
        else if(strictly_increasing) return 1;
        else if(!same && !strictly_increasing) return 3;
        else return 4;
    }
}
inline bool cmp(const pair<long long int, vector<string>> &a, const pair<long long int, vector<string>> &b){
    return a.first < b.first;
}
void construct_constraint_3(){
    constraint_3_start = constraint_3_end = constraint_1_end+1;

    // sort(cir1_bus_set.begin(), cir1_bus_set.end(), cmp);
    // sort(cir2_bus_set.begin(), cir2_bus_set.end(), cmp);
    // vector<vector<string>>circuit_1_record, circuit_2_record;
    // vector<string>tmp;
    // circuit_1_record.emplace_back(tmp);
    // circuit_2_record.emplace_back(tmp);

    //reserve the input bus only
    long long int circuit_1_bus_size = cir1_bus_set.size();
    for(long long int i=0; i<circuit_1_bus_size; i++){
        auto x = ((cir1_bus_set[i]).second)[0];
        if(circuit_1_is_input[x]){
            cir1_input_bus_set.emplace_back(cir1_bus_set[i]);
        }else{
            cir1_output_bus_set.emplace_back(cir1_bus_set[i]);
        }
    }
    sort(cir1_input_bus_set.begin(), cir1_input_bus_set.end(), cmp);
    sort(cir1_output_bus_set.begin(), cir1_output_bus_set.end(), cmp);
    circuit_1_bus_size = cir1_input_bus_set.size();
    cout << "cir1_input_bus_set.size(): " << circuit_1_bus_size << endl;
    int circuit_1_mode = bus_mode_check(1, circuit_1_bus_size);

    long long int circuit_2_bus_size = cir2_bus_set.size();
    for(long long int i=0; i<circuit_2_bus_size; i++){
        auto x = ((cir2_bus_set[i]).second)[0];
        if(circuit_2_is_input[x]){
            cir2_input_bus_set.emplace_back(cir2_bus_set[i]);
        }else{
            cir2_output_bus_set.emplace_back(cir2_bus_set[i]);
        }
    }
    sort(cir2_input_bus_set.begin(), cir2_input_bus_set.end(), cmp);
    sort(cir2_output_bus_set.begin(), cir2_output_bus_set.end(), cmp);
    circuit_2_bus_size = cir2_input_bus_set.size();
    cout << "cir2_input_bus_set.size(): " << circuit_2_bus_size << endl;
    int circuit_2_mode = bus_mode_check(2, circuit_2_bus_size);
    
    cout << "mode: " << circuit_1_mode << " " << circuit_2_mode << endl;
    if(circuit_1_mode == 1 && circuit_2_mode == 1){
        if(circuit_1_bus_size == circuit_2_bus_size){
            for(long long int i=0; i<circuit_1_bus_size; i++){
                long long int bus_1_length = ((cir1_input_bus_set[i]).second).size();
                long long int bus_2_length = ((cir2_input_bus_set[i]).second).size();
                for(long long int j=0; j<bus_1_length; j++){
                    string str;
                    for(long long int k=0; k<bus_2_length; k++){
                        string x = ((cir1_input_bus_set[i]).second)[j];
                        string y = ((cir2_input_bus_set[i]).second)[k];
                        long long int x_num = circuit_1_port_id_input_mapping[x];
                        long long int y_num = circuit_2_port_id_input_mapping[y];
                        // str += input_pair_table[pair<string, string>(x, y)] + " " + input_pair_table[pair<string, string>("-"+x, y)] + " ";
                        str += input_pair_matrix[y_num][2*x_num] + " " + input_pair_matrix[y_num][2*x_num+1] + " ";
                        for(long long int l=k+1; l<bus_2_length; l++){
                            string str2;
                            string y2 = ((cir2_input_bus_set[i]).second)[l];
                            long long int y2_num = circuit_2_port_id_input_mapping[y2];
                            // str2 = "-" + input_pair_table[pair<string, string>(x, y)] + " -" + input_pair_table[pair<string, string>(x, y2)] + " 0";
                            str2 = "-" + input_pair_matrix[y_num][2*x_num] + " -" + input_pair_matrix[y2_num][2*x_num] + " 0";
                            constraint_3.emplace_back(str2);
                            // str2 = "-" + input_pair_table[pair<string, string>("-"+x, y)] + " -" + input_pair_table[pair<string, string>("-"+x, y2)] + " 0";
                            str2 = "-" + input_pair_matrix[y_num][2*x_num+1] + " -" + input_pair_matrix[y2_num][2*x_num+1] + " 0";
                            constraint_3.emplace_back(str2);
                            // str2 = "-" + input_pair_table[pair<string, string>(x, y)] + " -" + input_pair_table[pair<string, string>("-"+x, y2)] + " 0";
                            str2 = "-" + input_pair_matrix[y_num][2*x_num] + " -" + input_pair_matrix[y2_num][2*x_num+1] + " 0";
                            constraint_3.emplace_back(str2);
                            // str2 = "-" + input_pair_table[pair<string, string>("-"+x, y)] + " -" + input_pair_table[pair<string, string>(x, y2)] + " 0";
                            str2 = "-" + input_pair_matrix[y_num][2*x_num+1] + " -" + input_pair_matrix[y2_num][2*x_num] + " 0";
                            constraint_3.emplace_back(str2);
                        }
                    }
                    str += "0";
                    constraint_3.emplace_back(str);
                }
            }

            for(long long int i=0; i<circuit_2_bus_size; i++){
                for(long long int j=0; j<circuit_1_bus_size; j++){
                    if(i != j){
                        string str;
                        for(auto y : (cir2_input_bus_set[i]).second){
                            for(auto x : (cir1_input_bus_set[j]).second){
                                long long int x_num = circuit_1_port_id_input_mapping[x];
                                long long int y_num = circuit_2_port_id_input_mapping[y];
                                // str = "-"+input_pair_table[pair<string, string>(x, y)] + " 0";
                                str = "-"+input_pair_matrix[y_num][2*x_num] + " 0";
                                constraint_3.emplace_back(str);
                                // str = "-"+input_pair_table[pair<string, string>("-"+x, y)] + " 0";
                                str = "-"+input_pair_matrix[y_num][2*x_num+1] + " 0";
                                constraint_3.emplace_back(str);
                            }
                        }
                    }
                }
            }
        }else return;
    }
    else if(circuit_1_mode == 2 && circuit_2_mode == 2){
        if(circuit_1_bus_size == circuit_2_bus_size){
            string str, str2;
            vector<long long int> tmp;
            for(long long int i=0; i<factorial(circuit_1_bus_size); i++){
                str += to_string(constraint_3_end) + " ";
                constraint_3_end++;
            }
            str += "0";
            constraint_3.emplace_back(str);
            
            // constraint_3_end--;
            for(long long int i=constraint_3_start; i<constraint_3_end; i++){
                for(long long int j=i+1; j<constraint_3_end; j++){
                    str2 = "-"+to_string(i) + " -" + to_string(j) + " 0";
                    constraint_3.emplace_back(str2);
                }
            }
            

            permute(tmp, circuit_1_bus_size, circuit_2_bus_size);
            visited.clear();
            cout << "constraint_3_start: " << constraint_3_start << endl;
            cout << "constraint_3_end: " << constraint_3_end << endl;
            for(long long int m=0; m<constraint_3_end-constraint_3_start; m++){
                for(long long int i=0; i<circuit_1_bus_size; i++){
                    long long int bus_1_length = ((cir1_input_bus_set[i]).second).size();
                    long long int bus_2_length = ((cir2_input_bus_set[permutation[m][i]]).second).size();
                    // for(long long int j=0; j<bus_1_length; j++){
                    //     for(long long int k=0; k<bus_2_length; k++){
                    //         string x = ((cir1_input_bus_set[i]).second)[j];
                    //         string y = ((cir2_input_bus_set[permutation[m][i]]).second)[k];
                    //         for(long long int l=k+1; l<bus_2_length; l++){
                    //             string str2;
                    //             string y2 = ((cir2_input_bus_set[permutation[m][i]]).second)[l];
                    //             str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_table[pair<string, string>(x, y)] + " -" + input_pair_table[pair<string, string>(x, y2)] + " 0";
                    //             constraint_3.emplace_back(str2);
                    //             str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_table[pair<string, string>("-"+x, y)] + " -" + input_pair_table[pair<string, string>("-"+x, y2)] + " 0";
                    //             constraint_3.emplace_back(str2);
                    //             str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_table[pair<string, string>("-"+x, y)] + " -" + input_pair_table[pair<string, string>(x, y2)] + " 0";
                    //             constraint_3.emplace_back(str2);
                    //             str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_table[pair<string, string>(x, y)] + " -" + input_pair_table[pair<string, string>("-"+x, y2)] + " 0";
                    //             constraint_3.emplace_back(str2);
                    //         }
                    //     }
                    // }
                    // for(long long int k=0; k<bus_2_length; k++){
                    //     string str = "-" + to_string(m+constraint_3_start) + " ";
                    //     string y = ((cir2_input_bus_set[permutation[m][i]]).second)[k];
                    //     for(long long int j=0; j<bus_1_length; j++){
                    //         string x = ((cir1_input_bus_set[i]).second)[j];
                    //         str += input_pair_table[pair<string, string>(x, y)] + " " + input_pair_table[pair<string, string>("-"+x, y)] + " ";
                    //     }
                    //     str += input_pair_table[pair<string, string>("0", y)] + " " + input_pair_table[pair<string, string>("1", y)] + " 0";
                    //     constraint_3.emplace_back(str);
                    // }
                    for(long long int j=0; j<bus_1_length; j++){
                        string str = "-" + to_string(m+constraint_3_start) + " ";
                        for(long long int k=0; k<bus_2_length; k++){
                            string x = ((cir1_input_bus_set[i]).second)[j];
                            string y = ((cir2_input_bus_set[permutation[m][i]]).second)[k];
                            // str += input_pair_table[pair<string, string>(x, y)] + " " + input_pair_table[pair<string, string>("-"+x, y)] + " ";
                            long long int x_num = circuit_1_port_id_input_mapping[x];
                            long long int y_num = circuit_2_port_id_input_mapping[y];
                            str += input_pair_matrix[y_num][2*x_num] + " " + input_pair_matrix[y_num][2*x_num+1] + " ";
                            for(long long int l=k+1; l<bus_2_length; l++){
                                string str2;
                                string y2 = ((cir2_input_bus_set[permutation[m][i]]).second)[l];
                                long long int y2_num = circuit_2_port_id_input_mapping[y2];
                                // str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_table[pair<string, string>(x, y)] + " -" + input_pair_table[pair<string, string>(x, y2)] + " 0";
                                str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_matrix[y_num][2*x_num] + " -" + input_pair_matrix[y2_num][2*x_num] + " 0";
                                constraint_3.emplace_back(str2);
                                // str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_table[pair<string, string>("-"+x, y)] + " -" + input_pair_table[pair<string, string>("-"+x, y2)] + " 0";
                                str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_matrix[y_num][2*x_num+1] + " -" + input_pair_matrix[y2_num][2*x_num+1] + " 0";
                                constraint_3.emplace_back(str2);
                                // str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_table[pair<string, string>("-"+x, y)] + " -" + input_pair_table[pair<string, string>(x, y2)] + " 0";
                                str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_matrix[y_num][2*x_num+1] + " -" + input_pair_matrix[y2_num][2*x_num] + " 0";
                                constraint_3.emplace_back(str2);
                                // str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_table[pair<string, string>(x, y)] + " -" + input_pair_table[pair<string, string>("-"+x, y2)] + " 0";
                                str2 = "-" + to_string(m+constraint_3_start) +  " -" + input_pair_matrix[y_num][2*x_num] + " -" + input_pair_matrix[y2_num][2*x_num+1] + " 0";
                                constraint_3.emplace_back(str2);
                            }
                        }
                        str += "0";
                        constraint_3.emplace_back(str);
                    }
                }
                for(long long int i=0; i<circuit_2_bus_size; i++){
                    for(long long int j=0; j<circuit_1_bus_size; j++){
                        if(i != permutation[m][j]){
                            string str;
                            for(auto y : (cir2_input_bus_set[i]).second){
                                for(auto x : (cir1_input_bus_set[j]).second){
                                    long long int x_num = circuit_1_port_id_input_mapping[x];
                                    long long int y_num = circuit_2_port_id_input_mapping[y];
                                    // str = "-" + to_string(m+constraint_3_start) + " -"+input_pair_table[pair<string, string>(x, y)] + " 0";
                                    str = "-" + to_string(m+constraint_3_start) + " -"+input_pair_matrix[y_num][2*x_num] + " 0";
                                    constraint_3.emplace_back(str);
                                    // str = "-" + to_string(m+constraint_3_start) + " -"+input_pair_table[pair<string, string>("-"+x, y)] + " 0";
                                    str = "-" + to_string(m+constraint_3_start) + " -"+input_pair_matrix[y_num][2*x_num+1] + " 0";
                                    constraint_3.emplace_back(str);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    constraint_3_end--;

    // bus_direct_match = true;
    // if(cir1_bus_set.size() == cir2_bus_set.size()){
    //     long long int bus_size = cir1_bus_set.size();
    //     for(long long int i=0; i<bus_size; i++){
    //         if(cir1_bus_set[i].first == cir2_bus_set[i].first){
    //             if(i>0 && cir1_bus_set[i].first == cir1_bus_set[i-1].first){
    //                 for(auto x : (cir1_bus_set[i]).second) (circuit_1_record.back()).emplace_back(x);
    //                 for(auto y : (cir1_bus_set[i]).second) (circuit_2_record.back()).emplace_back(y);
    //             }
    //             else if(i == 0){
    //                 for(auto x : (cir1_bus_set[i]).second) (circuit_1_record.back()).emplace_back(x);
    //                 for(auto y : (cir1_bus_set[i]).second) (circuit_2_record.back()).emplace_back(y);
    //             }
    //             else{
    //                 circuit_1_record.emplace_back(tmp);
    //                 circuit_2_record.emplace_back(tmp);
    //                 for(auto x : (cir1_bus_set[i]).second) (circuit_1_record.back()).emplace_back(x);
    //                 for(auto y : (cir1_bus_set[i]).second) (circuit_2_record.back()).emplace_back(y);
    //             }
    //             bus_direct_match = true;
    //         }else{
    //             bus_direct_match = false;
    //             break;
    //         }
    //     }
    // }else bus_direct_match = false;

    // if(bus_direct_match){
    //     long long int num = circuit_1_record.size();
    //     for(long long int i=0; i<num; i++){
    //         for(auto y : circuit_2_record[i]){
    //             string str;
    //             for(auto x : circuit_1_record[i]){
    //                str += input_pair_table[pair<string, string>(x,y)] + " " + input_pair_table[pair<string, string>("-"+x,y)] + " ";
    //             }
    //             str += "0";
    //             constraint_3.emplace_back(str);
    //         }
    //     }
    // }
}

//constraint 1: one y can be matched to only one x
void construct_constraint_1_matrix_version(){
    constraint_1_start = constraint_1_end = input_table_number_end+1;

    for(long long int i=0; i<circuit_2_number_of_inputs; i++){
        string str;
        string y = circuit_2_input[i];
        for(long long int j=0; j<circuit_1_number_of_inputs; j++){
            string x = circuit_1_input[j];
            str += input_pair_matrix[i][2*j] + " ";
            constraint_0.emplace_back("-"+input_pair_matrix[i][2*j] + " -" + circuit_1_port_cnf_input_mapping[x]  + " " + circuit_2_port_cnf_input_mapping[y] + " 0");
            constraint_0.emplace_back("-"+input_pair_matrix[i][2*j] + " " + circuit_1_port_cnf_input_mapping[x]  + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
            str += input_pair_matrix[i][2*j+1] + " ";
            constraint_0.emplace_back("-"+input_pair_matrix[i][2*j+1] + " " + circuit_1_port_cnf_input_mapping[x]  + " " + circuit_2_port_cnf_input_mapping[y] + " 0");
            constraint_0.emplace_back("-"+input_pair_matrix[i][2*j+1] + " -" + circuit_1_port_cnf_input_mapping[x]  + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");

            constraint_1.emplace_back("-" + input_pair_matrix[i][2*j] + " -" + input_pair_matrix[i][2*j+1] + " 0");
            for(long long int k=j+1; k<circuit_1_number_of_inputs; k++){
                constraint_1.emplace_back("-" + input_pair_matrix[i][2*j] + " -" + input_pair_matrix[i][2*k] + " 0");
                constraint_1.emplace_back("-" + input_pair_matrix[i][2*j] + " -" + input_pair_matrix[i][2*k+1] + " 0");
                constraint_1.emplace_back("-" + input_pair_matrix[i][2*j+1] + " -" + input_pair_matrix[i][2*k] + " 0");
                constraint_1.emplace_back("-" + input_pair_matrix[i][2*j+1] + " -" + input_pair_matrix[i][2*k+1] + " 0");
            }
            constraint_1.emplace_back("-" + input_pair_matrix[i][2*j] + " -" + input_pair_matrix[i][2*circuit_1_number_of_inputs] + " 0");
            constraint_1.emplace_back("-" + input_pair_matrix[i][2*j] + " -" + input_pair_matrix[i][2*circuit_1_number_of_inputs+1] + " 0");
            constraint_1.emplace_back("-" + input_pair_matrix[i][2*j+1] + " -" + input_pair_matrix[i][2*circuit_1_number_of_inputs] + " 0");
            constraint_1.emplace_back("-" + input_pair_matrix[i][2*j+1] + " -" + input_pair_matrix[i][2*circuit_1_number_of_inputs+1] + " 0");
        }
        str += input_pair_matrix[i][2*circuit_1_number_of_inputs] + " ";
        constraint_0.emplace_back("-"+input_pair_matrix[i][2*circuit_1_number_of_inputs] + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
        str += input_pair_matrix[i][2*circuit_1_number_of_inputs+1] + " ";
        constraint_0.emplace_back("-"+input_pair_matrix[i][2*circuit_1_number_of_inputs+1] + " " +  circuit_2_port_cnf_input_mapping[y] + " 0");
        str += "0";
        constraint_1.emplace_back(str);

        constraint_1.emplace_back("-" + input_pair_matrix[i][2*circuit_1_number_of_inputs] + " -" + input_pair_matrix[i][2*circuit_1_number_of_inputs+1] + " 0");
    }

    constraint_1_end--;
}
void construct_constraint_1(){
    constraint_1_start = constraint_1_end = input_table_number_end+1;

    // for(auto y : circuit_2_input){
    //     string str = "";
    //     for(auto x : circuit_1_input){
    //         str += input_pair_table[pair<string, string>(x, y)] + " ";
    //         constraint_0.emplace_back("-"+input_pair_table[pair<string, string>(x, y)] + " -" + circuit_1_port_cnf_input_mapping[x]  + " " + circuit_2_port_cnf_input_mapping[y] + " 0");
    //         constraint_0.emplace_back("-"+input_pair_table[pair<string, string>(x, y)] + " " + circuit_1_port_cnf_input_mapping[x]  + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
    //         // constraint_1.emplace_back("-"+input_pair_table[pair<string, string>(x, y)] + " -" + circuit_1_port_cnf_input_mapping[x]  + " " + circuit_2_port_cnf_input_mapping[y] + " 0");
    //         // constraint_1.emplace_back("-"+input_pair_table[pair<string, string>(x, y)] + " " + circuit_1_port_cnf_input_mapping[x]  + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
    //         str += input_pair_table[pair<string, string>("-"+x, y)] + " ";
    //         constraint_0.emplace_back("-"+input_pair_table[pair<string, string>("-"+x, y)] + " " + circuit_1_port_cnf_input_mapping[x]  + " " + circuit_2_port_cnf_input_mapping[y] + " 0");
    //         constraint_0.emplace_back("-"+input_pair_table[pair<string, string>("-"+x, y)] + " -" + circuit_1_port_cnf_input_mapping[x]  + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
    //         // constraint_1.emplace_back("-"+input_pair_table[pair<string, string>("-"+x, y)] + " " + circuit_1_port_cnf_input_mapping[x]  + " " + circuit_2_port_cnf_input_mapping[y] + " 0");
    //         // constraint_1.emplace_back("-"+input_pair_table[pair<string, string>("-"+x, y)] + " -" + circuit_1_port_cnf_input_mapping[x]  + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
    //     }
    //     str += input_pair_table[pair<string, string>("0", y)] + " ";
    //     constraint_0.emplace_back("-"+input_pair_table[pair<string, string>("0", y)] + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
    //     // constraint_1.emplace_back("-"+input_pair_table[pair<string, string>("0", y)] + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
    //     str += input_pair_table[pair<string, string>("1", y)] + " ";
    //     constraint_0.emplace_back("-"+input_pair_table[pair<string, string>("1", y)] + " " +  circuit_2_port_cnf_input_mapping[y] + " 0");
    //     // constraint_1.emplace_back("-"+input_pair_table[pair<string, string>("1", y)] + " " +  circuit_2_port_cnf_input_mapping[y] + " 0");
    //     str += "0";
    //     constraint_1.emplace_back(str);
    // }
    // cout << "step4.1 done" << endl;
    cout << "step4 start:" << endl;
    for(long long int i=0; i<circuit_2_number_of_inputs; i++){
        string str;
        string y = circuit_2_input[i];
        for(long long int j=0; j<circuit_1_number_of_inputs; j++){
            string x = circuit_1_input[j];
            str += input_pair_table[pair<string, string>(x, y)] + " ";
            constraint_0.emplace_back("-"+input_pair_table[pair<string, string>(x, y)] + " -" + circuit_1_port_cnf_input_mapping[x]  + " " + circuit_2_port_cnf_input_mapping[y] + " 0");
            constraint_0.emplace_back("-"+input_pair_table[pair<string, string>(x, y)] + " " + circuit_1_port_cnf_input_mapping[x]  + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
            str += input_pair_table[pair<string, string>("-"+x, y)] + " ";
            constraint_0.emplace_back("-"+input_pair_table[pair<string, string>("-"+x, y)] + " " + circuit_1_port_cnf_input_mapping[x]  + " " + circuit_2_port_cnf_input_mapping[y] + " 0");
            constraint_0.emplace_back("-"+input_pair_table[pair<string, string>("-"+x, y)] + " -" + circuit_1_port_cnf_input_mapping[x]  + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");

            constraint_1.emplace_back("-" + input_pair_table[pair<string, string>(circuit_1_input[j],  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>("-"+circuit_1_input[j],  circuit_2_input[i])] + " 0");
            for(long long int k=j+1; k<circuit_1_number_of_inputs; k++){
                cout << "i, j, k: " << i << ", " << j << ", " << k << endl;
                constraint_1.emplace_back("-" + input_pair_table[pair<string, string>(circuit_1_input[j],  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>(circuit_1_input[k],  circuit_2_input[i])] + " 0");
                constraint_1.emplace_back("-" + input_pair_table[pair<string, string>(circuit_1_input[j],  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>("-"+circuit_1_input[k],  circuit_2_input[i])] + " 0");
                constraint_1.emplace_back("-" + input_pair_table[pair<string, string>("-"+circuit_1_input[j],  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>(circuit_1_input[k],  circuit_2_input[i])] + " 0");
                constraint_1.emplace_back("-" + input_pair_table[pair<string, string>("-"+circuit_1_input[j],  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>("-"+circuit_1_input[k],  circuit_2_input[i])] + " 0");
            }
            constraint_1.emplace_back("-" + input_pair_table[pair<string, string>(circuit_1_input[j],  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>("0",  circuit_2_input[i])] + " 0");
            constraint_1.emplace_back("-" + input_pair_table[pair<string, string>(circuit_1_input[j],  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>("1",  circuit_2_input[i])] + " 0");
            constraint_1.emplace_back("-" + input_pair_table[pair<string, string>("-"+circuit_1_input[j],  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>("0",  circuit_2_input[i])] + " 0");
            constraint_1.emplace_back("-" + input_pair_table[pair<string, string>("-"+circuit_1_input[j],  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>("1",  circuit_2_input[i])] + " 0");
        }
        str += input_pair_table[pair<string, string>("0", y)] + " ";
        constraint_0.emplace_back("-"+input_pair_table[pair<string, string>("0", y)] + " -" + circuit_2_port_cnf_input_mapping[y] + " 0");
        str += input_pair_table[pair<string, string>("1", y)] + " ";
        constraint_0.emplace_back("-"+input_pair_table[pair<string, string>("1", y)] + " " +  circuit_2_port_cnf_input_mapping[y] + " 0");
        str += "0";
        constraint_1.emplace_back(str);

        constraint_1.emplace_back("-" + input_pair_table[pair<string, string>("0",  circuit_2_input[i])] + " -" + input_pair_table[pair<string, string>("1",  circuit_2_input[i])] + " 0");
    }
    cout << "step4 done!" << endl;
    
    constraint_1_end--;
}

void construct_input_pair_matrix(){
    // input_table_number_start = input_table_number_end = output_table_number_end+1;
    cout << "input_table_number_start: " << input_table_number_start << endl;
    input_table_number_end = input_table_number_start;
    // input_pair_matrix = NEW2D(circuit_2_number_of_inputs, 2*circuit_1_number_of_inputs+2, string);
    long long int i;
    input_pair_matrix = new string*[circuit_2_number_of_inputs];
    for(i = 0; i < circuit_2_number_of_inputs; i++)
        input_pair_matrix[i] = new string[2*circuit_1_number_of_inputs+2];

    for(long long int i=0; i<circuit_2_number_of_inputs; i++){
        for(long long int j=0; j<2*circuit_1_number_of_inputs+2; j++){
            input_pair_matrix[i][j] = to_string(input_table_number_end);
            input_table_number_end++;
        }
    }
    input_table_number_end--;
    cout << "input_table_number_end: " << input_table_number_end << endl;
}
void construct_input_pair_table(){
    // input_table_number_start = input_table_number_end = output_table_number_end+1;
    input_table_number_end = input_table_number_start;

    for(auto y : circuit_2_input){
        for(auto x : circuit_1_input){
            stringstream ss;
            string str;
            ss << input_table_number_end;
            ss >> str;
            input_pair_table.insert(pair<pair<string, string>, string>(make_pair(x,y), str));
            input_table_number_end++;

            stringstream ss2;
            string str2;
            ss2 << input_table_number_end;
            ss2 >> str2;
            input_pair_table.insert(pair<pair<string, string>, string>(make_pair("-"+x,y), str2));
            input_table_number_end++;

            if(circuit_1_input_support_size[x] != circuit_2_input_support_size[y]){
                constraint_5.emplace_back("-"+input_pair_table[pair<string, string>(x,y)] + " 0");
                constraint_5.emplace_back("-"+input_pair_table[pair<string, string>("-"+x,y)] + " 0");
            }
        }
    }
    for(auto y : circuit_2_input){
        stringstream ss;
        string str;
        ss << input_table_number_end;
        ss >> str;
        input_pair_table.insert(pair<pair<string, string>, string>(make_pair("0",y), str));
        input_table_number_end++;

        stringstream ss2;
        string str2;
        ss2 << input_table_number_end;
        ss2 >> str2;
        input_pair_table.insert(pair<pair<string, string>, string>(make_pair("1",y), str2));
        input_table_number_end++;
    }
    input_table_number_end--;
}

void construct_output_pair_table(){
    output_table_number_end = output_table_number_start;

    for(auto y : circuit_2_output){
        for(auto x : circuit_1_output){
            stringstream ss;
            string str;
            ss << output_table_number_end;
            ss >> str;
            output_pair_table.insert(pair<pair<string, string>, string>(make_pair(x,y), str));
            output_table_number_end++;
        }
    }
    for(auto y : circuit_2_output){
        for(auto x : circuit_1_output){
            stringstream ss;
            string str;
            ss << output_table_number_end;
            ss >> str;
            x = "-" + x;
            output_pair_table.insert(pair<pair<string, string>, string>(make_pair(x,y), str));
            output_table_number_end++;
        }
    }
    output_table_number_end--;
}

void get_cnf_file_record(string file_name, int cir){
    if(cir == 1){
        cnf_file_1 = new fstream;
        cnf_file_1->open(file_name.c_str(), std::ios::in);

        string line;
        stringstream ss1;
        getline((*cnf_file_1), line);
        getline((*cnf_file_1), line);
        ss1 << line;
        for(int i=0; i<4; i++){
            stringstream ss2;
            long long int num;
            string str;

            getline(ss1, str,' ');
            if(i == 2){
                ss2 << str;
                ss2 >> num;
                circuit1_cnf.number_of_variables = num;
            }else if(i == 3){
                ss2 << str;
                ss2 >> num;
                circuit1_cnf.number_of_clauses = num;
            }
        }
        while(getline((*cnf_file_1), line)){
            circuit1_cnf.clauses.emplace_back(line);
        }
        cnf_file_1->close();
        cnf_file_1->clear();
    }
    else if(cir == 2){
        cnf_file_2 = new fstream;
        cnf_file_2->open(file_name.c_str(), std::ios::in);

        string line;
        stringstream ss1;
        getline((*cnf_file_2), line);
        getline((*cnf_file_2), line);
        ss1 << line;
        for(int i=0; i<4; i++){
            stringstream ss2;
            long long int num;
            string str;

            getline(ss1, str,' ');
            if(i == 2){
                ss2 << str;
                ss2 >> num;
                circuit2_cnf.number_of_variables = num;
            }else if(i == 3){
                ss2 << str;
                ss2 >> num;
                circuit2_cnf.number_of_clauses = num;
            }
        }
        while(getline((*cnf_file_2), line)){
            circuit2_cnf.clauses.emplace_back(line);
        }
        cnf_file_2->close();
        cnf_file_2->clear();
    }
}

void cnf_file_combine2(string combine_filename){
    long long int total_number_of_variables = circuit1_cnf_number_of_variables + circuit2_cnf_number_of_variables;
    long long int total_number_of_clauses = circuit1_cnf_number_of_clauses + circuit2_cnf_number_of_clauses;
    total_cnf.number_of_clauses = total_number_of_variables;
    total_cnf.number_of_variables = total_number_of_clauses;
    string first_line, totvar, totcla;

    for(auto l : circuit1_cnf_clauses){
        total_cnf.clauses.emplace_back(l);
    }
    
    for(auto & l : circuit_2_port_cnf_input_mapping){
        string str;
        long long int num;

        num = stoll(l.second) + circuit1_cnf_number_of_variables;
        l.second = to_string(num);
    }
    
    for(auto & l : circuit_2_port_cnf_output_mapping){
        string str;
        long long int num;

        num = stoll(l.second) + circuit1_cnf_number_of_variables;
        l.second = to_string(num);
    }
    
    for(auto l : circuit2_cnf_clauses){
        stringstream ss1;
        string str, clauses_revised;

        ss1 << l;
        while(getline(ss1, str,' ')){
            long long int num_var = stoll(str);
            if(num_var > 0) clauses_revised += to_string(num_var+circuit1_cnf_number_of_variables) + " ";
            else if(num_var < 0) clauses_revised += to_string(num_var-circuit1_cnf_number_of_variables) + " ";
            else clauses_revised += "0";
        }
        circuit2_cnf.clauses2.emplace_back(clauses_revised);
        total_cnf.clauses.emplace_back(clauses_revised);
        //fputs((clauses_revised+"\n").c_str(), cnf_file_3);
    }
    
    // output_table_number_start = total_number_of_variables + 1;
    input_table_number_start = total_number_of_variables + 1;
}

void cnf_file_combine(string combine_filename){
    long long int total_number_of_variables = circuit1_cnf.number_of_variables + circuit2_cnf.number_of_variables;
    long long int total_number_of_clauses = circuit1_cnf.number_of_clauses + circuit2_cnf.number_of_clauses;
    total_cnf.number_of_clauses = total_number_of_variables;
    total_cnf.number_of_variables = total_number_of_clauses;
    string first_line, totvar, totcla;

    //cnf_file_3 = fopen(combine_filename.c_str(), "w+");
    first_line = "p cnf " + to_string(total_number_of_variables) + " " + to_string(total_number_of_clauses) + "\n";
    //fputs(first_line.c_str(), cnf_file_3);

    for(auto l : circuit1_cnf.clauses){
        //fputs((l+"\n").c_str(), cnf_file_3);
        total_cnf.clauses.emplace_back(l);
    }

    for(auto & l : circuit_2_port_cnf_input_mapping){
        string str;
        long long int num;

        num = stoll(l.second) + circuit1_cnf.number_of_variables;
        l.second = to_string(num);
    }
    for(auto & l : circuit_2_port_cnf_output_mapping){
        string str;
        long long int num;

        num = stoll(l.second) + circuit1_cnf.number_of_variables;
        l.second = to_string(num);
    }
    // cout <<"*DEBUG: "<< endl;
    // for(auto y : circuit_2_input){
    //     cout << y << ": " << circuit_2_port_cnf_input_mapping[y] << endl;
    // }
    // for(auto y : circuit_2_output){
    //     cout << y << ": " << circuit_2_port_cnf_output_mapping[y] << endl;
    // }

    for(auto l : circuit2_cnf.clauses){
        stringstream ss1;
        string str, clauses_revised;

        ss1 << l;
        while(getline(ss1, str,' ')){
            long long int num_var = stoll(str);
            if(num_var > 0) clauses_revised += to_string(num_var+circuit1_cnf.number_of_variables) + " ";
            else if(num_var < 0) clauses_revised += to_string(num_var-circuit1_cnf.number_of_variables) + " ";
            else clauses_revised += "0";
        }
        circuit2_cnf.clauses2.emplace_back(clauses_revised);
        total_cnf.clauses.emplace_back(clauses_revised);
        //fputs((clauses_revised+"\n").c_str(), cnf_file_3);
    }

    output_table_number_start = total_number_of_variables + 1;

    //fclose(cnf_file_3);
}

void get_support_set(string file_name, int cir){
    cout << "get_support_set DEBUG! " << endl;
    if(cir == 1){
        support_set_file = new fstream;
        support_set_file->open("SUPP_FILE_1", std::ios::in);
        if(!support_set_file->is_open()){
            cout << "Open Fail:" << "SUPP_FILE_1" << endl;
            exit(1);
        }

        string line, output, supp_size, input;

        //structural support
        for(long long int i=0; i<circuit_1_number_of_outputs; i++){
            getline((*support_set_file), line);
            stringstream ss, supp_size_ss;
            long long int supp_size_num;

            ss << line;
            getline(ss, output,' ');
            getline(ss, supp_size,' ');

            supp_size_ss << supp_size;
            supp_size_ss >> supp_size_num;
            structural_support_set_size_1[output] = supp_size_num;
            circuit_1_structural_support_set_size.emplace_back(pair<long long int, string>(supp_size_num, output));
            // cout << output << " *1* " << supp_size_num << endl;
        }
        for(long long int i=0; i<circuit_1_number_of_outputs; i++){
            getline((*support_set_file), line);
            stringstream ss;
            vector<string> tmp_supp_set;

            if(line == ""){
                circuit_1_structural_support_set.insert(pair<string, vector<string>>(circuit_1_structural_support_set_size[i].second, tmp_supp_set));
                continue;
            }else{
                ss << line;
                while(getline(ss, input,' ')) tmp_supp_set.emplace_back(input);
                circuit_1_structural_support_set.insert(pair<string, vector<string>>(circuit_1_structural_support_set_size[i].second, tmp_supp_set));
            }
            
            // cout << "GET SUPPORT SET OF: " <<"output: " << circuit_1_support_set_size[i].second << ", input: ";
            // for(auto it : circuit_1_support_set[circuit_1_support_set_size[i].second]){
            //     cout << it << " ";
            // }
            // cout << endl;
        }

        //functional support
        for(long long int i=0; i<circuit_1_number_of_outputs; i++){
            getline((*support_set_file), line);
            stringstream ss, supp_size_ss;
            long long int supp_size_num;

            ss << line;
            getline(ss, output,' ');
            getline(ss, supp_size,' ');

            supp_size_ss << supp_size;
            supp_size_ss >> supp_size_num;
            functional_support_set_size_1[output] = supp_size_num;
            circuit_1_functional_support_set_size.emplace_back(pair<long long int, string>(supp_size_num, output));
            // cout << output << " *1 functional* " << supp_size_num << endl;
        }
        for(long long int i=0; i<circuit_1_number_of_outputs; i++){
            getline((*support_set_file), line);
            stringstream ss;
            vector<string> tmp_supp_set;

            if(line == ""){
                circuit_1_functional_support_set.insert(pair<string, vector<string>>(circuit_1_functional_support_set_size[i].second, tmp_supp_set));
                continue;
            }else{
                ss << line;
                while(getline(ss, input,' ')){
                    tmp_supp_set.emplace_back(input);
                    circuit_1_input_support_size[input]++;
                }
                circuit_1_functional_support_set.insert(pair<string, vector<string>>(circuit_1_functional_support_set_size[i].second, tmp_supp_set));
            }
            
            // cout << "GET SUPPORT SET OF: " <<"output: " << circuit_1_support_set_size[i].second << ", input: ";
            // for(auto it : circuit_1_support_set[circuit_1_support_set_size[i].second]){
            //     cout << it << " ";
            // }
            // cout << endl;
        }

        for(auto f : circuit_1_output){
            circuit_1_support_set_size.emplace_back(pair<pair<long long int, long long int>, string>(pair<long long int, long long int>(functional_support_set_size_1[f], structural_support_set_size_1[f]), f));
        }

        support_set_file->close();
        support_set_file->clear();
    }else if(cir == 2){
        support_set_file = new fstream;
        support_set_file->open("SUPP_FILE_2", std::ios::in);
        if(!support_set_file->is_open()){
            cout << "Open Fail:" << "SUPP_FILE_2" << endl;
            exit(1);
        }
        string line, output, input, supp_size;

        //structural
        for(long long int i=0; i<circuit_2_number_of_outputs; i++){
            getline((*support_set_file), line);
            stringstream ss, supp_size_ss;
            long long int supp_size_num;

            ss << line;
            getline(ss, output,' ');
            getline(ss, supp_size,' ');

            supp_size_ss << supp_size;
            supp_size_ss >> supp_size_num;
            structural_support_set_size_2[output] = supp_size_num;
            circuit_2_structural_support_set_size.emplace_back(pair<long long int, string>(supp_size_num, output));
            // cout << output << " *2* " << supp_size_num << endl;
        }
        for(long long int i=0; i<circuit_2_number_of_outputs; i++){
            getline((*support_set_file), line);
            stringstream ss;
            vector<string> tmp_supp_set;

            if(line == ""){
                circuit_2_structural_support_set.insert(pair<string, vector<string>>(circuit_2_structural_support_set_size[i].second, tmp_supp_set));
                continue;
            }
            else{
                ss << line;
                while(getline(ss, input,' ')) tmp_supp_set.emplace_back(input);
                circuit_2_structural_support_set.insert(pair<string, vector<string>>(circuit_2_structural_support_set_size[i].second, tmp_supp_set));
            }

            // cout << "GET SUPPORT SET OF: " <<"output: " << circuit_2_support_set_size[i].second << ", input: ";
            // for(auto it : circuit_2_support_set[circuit_2_support_set_size[i].second]){
            //     cout << it << " ";
            // }
            // cout << endl;
        }

        //functional support
        for(long long int i=0; i<circuit_2_number_of_outputs; i++){
            getline((*support_set_file), line);
            stringstream ss, supp_size_ss;
            long long int supp_size_num;

            ss << line;
            getline(ss, output,' ');
            getline(ss, supp_size,' ');

            supp_size_ss << supp_size;
            supp_size_ss >> supp_size_num;
            functional_support_set_size_2[output] = supp_size_num;
            circuit_2_functional_support_set_size.emplace_back(pair<long long int, string>(supp_size_num, output));
            // cout << output << " *1 functional* " << supp_size_num << endl;
        }
        for(long long int i=0; i<circuit_2_number_of_outputs; i++){
            getline((*support_set_file), line);
            stringstream ss;
            vector<string> tmp_supp_set;

            if(line == ""){
                circuit_2_functional_support_set.insert(pair<string, vector<string>>(circuit_2_functional_support_set_size[i].second, tmp_supp_set));
                continue;
            }else{
                ss << line;
                while(getline(ss, input,' ')){
                    tmp_supp_set.emplace_back(input);
                    circuit_2_input_support_size[input]++;
                }
                circuit_2_functional_support_set.insert(pair<string, vector<string>>(circuit_2_functional_support_set_size[i].second, tmp_supp_set));
            }
            
            // cout << "GET SUPPORT SET OF: " <<"output: " << circuit_1_support_set_size[i].second << ", input: ";
            // for(auto it : circuit_1_support_set[circuit_1_support_set_size[i].second]){
            //     cout << it << " ";
            // }
            // cout << endl;
        }

        for(auto g : circuit_2_output){
            circuit_2_support_set_size.emplace_back(pair<pair<long long int, long long int>, string>(pair<long long int, long long int>(functional_support_set_size_2[g], structural_support_set_size_2[g]), g));
        }

        support_set_file->close();
        support_set_file->clear();
    }
}

void aig_to_cnf_number(string file_name, int cir){
    aig_to_cnf_number_file = new fstream;
    aig_to_cnf_number_file->open(file_name.c_str(), std::ios::in);
    if(!aig_to_cnf_number_file->is_open()){
        cout << "Open Fail:" << "aig_to_cnf_number_file" << endl;
        exit(1);
    }else{
        string line, aig_number, cnf_number;
        while(getline((*aig_to_cnf_number_file), line)){
            stringstream ss;
            
            ss << line;
            getline(ss, aig_number,' ');
            getline(ss, cnf_number,' ');

            if(cir == 1) circuit_1_aig_cnf_mapping.insert(pair<string, string>(aig_number, cnf_number));
            else if(cir == 2) circuit_2_aig_cnf_mapping.insert(pair<string, string>(aig_number, cnf_number));
        }
        aig_to_cnf_number_file->close();
        aig_to_cnf_number_file->clear();
    }
}
