#include <iostream>
#include <cstdlib>
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <cstring>
#include <ctime>
#include "utility.h"

using namespace std;

fstream * show_current_group_file;

long long int show_current_group_id = 0, show_current_group_id_tmp = 0;
void show_current_group(bool miter_check){
    show_current_group_file = new fstream;
    if(show_current_group_id_tmp < 500)show_current_group_file->open("show_current_group_file", std::fstream::in | std::fstream::out | std::fstream::app);
    else{
        show_current_group_file->open("show_current_group_file",std::fstream::out);
        show_current_group_id_tmp = 0;
    }
    
    if(!show_current_group_file->is_open()){
        cout << "Open Fail:" << "show_current_group_file" << endl;
        exit(1);
    }else{
        (*show_current_group_file) << "===================" << show_current_group_id++ << ((miter_check)?": miter ":": learned_clause ") << " (" << show_current_group_id_tmp++ << ") " << "===========================" << endl;
        //INPUT GROUP
        bool first = true;
        for(long long int i=0; i<2*circuit_1_number_of_inputs; i++){
            for(long long int j=0; j<circuit_2_number_of_inputs; j++){
                if(i%2==0 && solve_mapping_file_result_record[stoll(input_pair_matrix[j][i])]){
                    if(first){
                        (*show_current_group_file) << "INGROUP" << '\n';
                        (*show_current_group_file) << "1 + "<< circuit_1_input[i/2] << '\n';
                        first = false;
                    }
                    (*show_current_group_file) << "2 + " << circuit_2_input[j] << '\n';
                }
                else if(i%2==1 && solve_mapping_file_result_record[stoll(input_pair_matrix[j][i])]){
                    if(first){
                        (*show_current_group_file) << "INGROUP" << '\n';
                        (*show_current_group_file) << "1 + "<< circuit_1_input[i/2] << '\n';
                        first = false;
                    }
                    (*show_current_group_file) << "2 - " << circuit_2_input[j] << '\n';
                }
            }
            if(!first) (*show_current_group_file) << "END" << '\n';
            first = true;
        }

        //OUTPUT GROUP
        first = true;
        for(auto f : circuit_1_output){
            for(auto p : output_matching_result){
                if((p.second).first == f){
                    if(first){
                        (*show_current_group_file) << "OUTGROUP" << '\n';
                        (*show_current_group_file) << "1 + "<< f << '\n';
                        first = false;
                    }
                    (*show_current_group_file) << "2 " << ((p.first)?"+ ":"- ") << (p.second).second << '\n';
                }
            }
            if(!first) (*show_current_group_file) << "END" << '\n';
            first = true;
        }

        //CONSTANT GROUP
        first = true;
        //constant 0
        for(long long int i=0; i<circuit_2_number_of_inputs; i++){
            if(solve_mapping_file_result_record[stoll(input_pair_matrix[i][2*circuit_1_number_of_inputs])]){
                if(first){
                    (*show_current_group_file) << "CONSTGROUP" << '\n';
                    first = false;
                }
                (*show_current_group_file) << "+ " << circuit_2_input[i] << '\n';
            }
        }
        //constant 1
        for(long long int i=0; i<circuit_2_number_of_inputs; i++){
            if(solve_mapping_file_result_record[stoll(input_pair_matrix[i][2*circuit_1_number_of_inputs+1])]){
                if(first){
                    (*show_current_group_file) << "CONSTGROUP" << '\n';
                    first = false;
                }
                (*show_current_group_file) << "- " << circuit_2_input[i] << '\n';
            }
        }
        if(!first) (*show_current_group_file) << "END" << '\n';

        show_current_group_file->close();
        show_current_group_file->clear();
    }
    // bool first = true;
    // for(auto x : circuit_1_input){
    //     for(auto y : circuit_2_input){
    //         if(solve_mapping_file_result_record[stoll(input_pair_table[pair<string, string>(x,y)])].second){
    //             if(first){
    //                 cout << "INGROUP" << '\n';
    //                 cout << "1 + "<< x << '\n';
    //                 first = false;
    //             }
    //             cout << "2 + " << y << '\n';
    //         }
    //         else if(solve_mapping_file_result_record[stoll(input_pair_table[pair<string, string>("-"+x,y)])].second){
    //             if(first){
    //                 cout << "INGROUP" << '\n';
    //                 cout << "1 + "<< x << '\n';
    //                 first = false;
    //             }
    //             cout << "2 - " << y << '\n';
    //         }
    //     }
    //     if(!first) cout << "END" << '\n';
    //     first = true;
    // }
    // //CONSTANT GROUP
    // first = true;
    // string x = "0";
    // for(auto y : circuit_2_input){
    //     if(solve_mapping_file_result_record[stoll(input_pair_table[pair<string, string>(x,y)])].second){
    //         if(first){
    //             cout << "CONSTGROUP" << '\n';
    //             first = false;
    //         }
    //         cout << "+ " << y << '\n';
    //     }
    // }
    // if(!first) cout << "END" << '\n';

    // first = true;
    // x = "1";
    // for(auto y : circuit_2_input){
    //     if(solve_mapping_file_result_record[stoll(input_pair_table[pair<string, string>(x,y)])].second){
    //         if(first){
    //             cout << "CONSTGROUP" << '\n';
    //             first = false;
    //         }
    //         cout << "- " << y << '\n';
    //     }
    // }
    // if(!first) cout << "END" << '\n';

    // //OUTGROUP
    // first = true;
    // for(auto f : circuit_1_output){
    //     for(auto p : output_matching_result){
    //         if((p.second).first == f){
    //             if(first){
    //                 cout << "OUTGROUP" << '\n';
    //                 cout << "1 + "<< f << '\n';
    //                 first = false;
    //             }
    //             cout << "2 " << ((p.first)?"+ ":"- ") << (p.second).second << '\n';
    //         }
    //     }
    //     if(!first) cout << "END" << '\n';
    //     first = true;
    // }
}

bool input_solver(vector<pair<bool, pair<string, string>>> output_matching_result){ 
    while(1){
        // current_time = clock();
        cout << "CURRENT TIME: " << t.GetElapsedMillseconds()/1000 << "sec" << endl;
        cout << "current output matching: ";
        for(auto p : output_matching_result) 
            cout << "(" << (p.second).first << ", " << (p.second).second << ")";
        cout << endl;

        if(t.GetElapsedMillseconds() > 3500000){
            return false;
            break;
        }
        
        if(!solve_mapping(output_matching_result)){
            return false;
        }
        else{
            if(!solve_miter(output_matching_result)){
                // show_current_group(true);
                return true;
            }
            else{
                // show_current_group(false);
                construct_learned_clauses(output_matching_result);
            }
        }
    }
    return false;
}
