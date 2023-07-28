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
#include "output_solver.h"
#include "input_solver.h"

using namespace std;

bool optimal = false, projection = false,  timeout_stop = false;
bool timeout_reverse = false;
vector<pair<bool, pair<string, string>>> output_matching_result;
long long int number_of_groups=1;
map<string, pair<long long int, long long int>> group_info;  // pair: (group_number, group_index)
map<string, long long int> backtracking_index; //pair: (index/position, from_start)
unordered_map<string, long long int> used_times;
bool from_start = true; //backtracking from start
long long optimal_result_size = 0;

void random_simulation(long long int pattern_length, long long int pattern_size){
    vector<vector<bool>> patterns;
    vector<bool> pattern;

    //all 0 pattern
    for(long long int i=0; i<pattern_length; i++){
        pattern.emplace_back(false);
    }
    patterns.emplace_back(pattern);

    //all 1 pattern
    pattern.clear();
    for(long long int i=0; i<pattern_length; i++){
        pattern.emplace_back(true);
    }
    patterns.emplace_back(pattern);

    //random pattern
    for(long long int i=0; i<pattern_size-2; i++){
        pattern.clear();
        for(long long int j=0; j<pattern_length; j++){
            //TODO:
        }
        patterns.emplace_back(pattern);
    }
    
}

inline bool cmp(const pair<pair<long long int, long long int>, string> &a, const pair<pair<long long int, long long int>, string> &b){
    if((a.first).first < (b.first).first)return (a.first).first < (b.first).first;
    else return (a.first).second < (b.first).second;
}

void backtracking_index_init(){
    for(auto g : circuit_2_output){
        backtracking_index[g] = 0;
    }
}

void Output_grouping(long long int number_of_outputs){
    long long int n = number_of_outputs;
    cout << "Output Grouping" << endl;

    //sort
    sort(circuit_1_support_set_size.begin(), circuit_1_support_set_size.end(), cmp);
    sort(circuit_2_support_set_size.begin(), circuit_2_support_set_size.end(), cmp);

    //initialization
    vector<string> tmp;
    circuit_1_output_group.emplace_back(tmp);
    circuit_2_output_group.emplace_back(tmp);

    //grouping
    for(long long int i=n-1; i>=0; i--){
        vector<string> &f_last = circuit_1_output_group.back();
        vector<string> &g_last = circuit_2_output_group.back();

        f_last.emplace_back(circuit_1_support_set_size[i].second);
        g_last.emplace_back(circuit_2_support_set_size[i].second);
        used_times[circuit_1_support_set_size[i].second] = 0;

        if(i>0 && (circuit_1_support_set_size[i].first).first > (circuit_2_support_set_size[i-1].first).first){
            reverse(f_last.begin(), f_last.end());
            reverse(g_last.begin(), g_last.end());
            circuit_1_output_group.emplace_back(tmp);
            circuit_2_output_group.emplace_back(tmp);
            number_of_groups++;
        }else if(i == 0){
            reverse(f_last.begin(), f_last.end());
            reverse(g_last.begin(), g_last.end());
        }
    }
    reverse(circuit_1_output_group.begin(), circuit_1_output_group.end());
    reverse(circuit_2_output_group.begin(), circuit_2_output_group.end());

    //preprocessing the buffer (support set size = 0)
    // vector<string> &f_front = circuit_1_output_group.front();
    // vector<string> &g_front = circuit_2_output_group.front();
    // for(auto f : f_front){

    // }
    // for(auto g : g_front){

    // }
    // if(f_front.empty()) circuit_1_output_group.erase(circuit_1_output_group.begin());
    // if(g_front.empty()) circuit_2_output_group.erase(circuit_2_output_group.begin());

    cout << "circuit 1 output group: \n"; 
    for(auto it : circuit_1_output_group){
        cout << "( ";
        for(auto it2: it){
            cout << it2 << ", ";
        }
        cout << " )\n";
    }

    long long int group_num = 0, group_id = 0;
    cout << "circuit 2 output group: \n"; 
    for(auto it : circuit_2_output_group){
        cout << "( ";
        group_id = 0;
        for(auto it2: it){
            cout << it2 << ", ";
            group_info[it2] = make_pair(group_num, group_id);
            backtracking_index[it2] = -1;
            group_id ++;
        }
        group_num++;
        cout << " )\n";
    }

    for(auto it : circuit_2_output_group){
        for(auto it2 : it) cout << "group_info: " << it2 << " -> (" << group_info[it2].first << ", " << group_info[it2].second << ")\n"; 
    }
}

//for debug
void show_current_output_matching_result(){
    cout << "Number of groups: " << number_of_groups << endl;
    cout << "Current output matching: " << endl;
    for(auto it : output_matching_result){
        cout << "(" << (it.second).first << ", " << (it.second).second << ")" << endl;
    }
}

pair<bool, pair<string, string>> new_output_pair, last_output_pair;
bool new_pair(bool find_new){

    if((last_output_pair.second).first == "" || (last_output_pair.second).second == ""){
        new_output_pair = make_pair(true, pair<string, string>(circuit_1_output_group[0][0], circuit_2_output_group[0][0]));
        backtracking_index[circuit_2_output_group[0][0]] = 0;
        return true;
    }

    long long int last_group = group_info[(last_output_pair.second).second].first;
    long long int last_index = group_info[(last_output_pair.second).second].second;
    long long int cur_group = (last_index == circuit_2_output_group[last_group].size()-1) ? last_group+1 : last_group;
    long long int cur_index = (cur_group == last_group) ? last_index+1 : 0;
    long long int pos = 0;
    string f, g;

    cout << "DEBUG" << "========" << endl;
    cout << "last_group: " << last_group << endl;
    cout << "last_index: " << last_index << endl;
    cout << "cur_group: " << cur_group << endl;
    cout << "cur_index: " << cur_index << endl;
    cout << "number of groups: " << number_of_groups << endl;
    cout << "projection: " << projection << endl;
    cout << "from start: " << from_start << endl;
    cout << "optimal: " << optimal << endl;
    cout << "DEBUG" << "========" << endl;

    if(cur_group >= number_of_groups){
        optimal = true;
        return true;
    }
    else if(find_new){
        pos = 0;
        if(!projection){
            while(used_times[circuit_1_output_group[cur_group][pos/2]] > 0) pos++;
        }
        if(pos >= 2*circuit_1_output_group[cur_group].size()) return false;
        bool phase = (pos%2 == 0) ? true : false;
        new_output_pair = make_pair(phase, pair<string, string>(circuit_1_output_group[cur_group][pos/2], circuit_2_output_group[cur_group][cur_index]));
        backtracking_index[circuit_2_output_group[cur_group][cur_index]] = pos;
        return true;
    }
    else{
        if(from_start){
            pos = 0;
            if(!projection){
                while(used_times[circuit_1_output_group[last_group][pos/2]] > 0) pos++;
            }
            if(pos >= 2*circuit_1_output_group[cur_group].size()) return false;
            
            bool phase = (pos%2 == 0) ? true : false;
            new_output_pair = make_pair(phase, pair<string, string>(circuit_1_output_group[last_group][pos/2], circuit_2_output_group[last_group][last_index]));
            backtracking_index[circuit_2_output_group[last_group][last_index]] = pos;
            return true;
        }
        else{
            // cout << "pos: " << pos << endl;
            // cout << "backtracking_index: " << backtracking_index[circuit_2_output_group[cur_group][cur_index]] << endl;
            if(backtracking_index[circuit_2_output_group[last_group][last_index]]+1 >= 2*(circuit_1_output_group[cur_group].size())){
                // cout << "return false" << endl;
                return false;
            }
            pos = (backtracking_index[circuit_2_output_group[last_group][last_index]]+1);
            // cout << "pos: " << pos << endl;
            if(!projection){
                while(used_times[circuit_1_output_group[last_group][pos/2]] > 0) pos++;
            }
            if(pos >= 2*circuit_1_output_group[last_group].size()) return false;
            // cout << "pos: " << pos << endl;
            bool phase = (pos%2 == 0) ? true : false;
            new_output_pair = make_pair(phase, pair<string, string>(circuit_1_output_group[last_group][pos/2], circuit_2_output_group[last_group][last_index]));
            backtracking_index[circuit_2_output_group[last_group][last_index]] = pos;
            return true;
        }
    }
    // else if(find_new){
        
    // }
    // else{
    //     if(from_start){
            
    //     }else{

    //     }
    // }
}

//use backtracking_index to record
bool sat = true;
void output_solver(){
    // current_time = clock();
    last_output_pair = make_pair(true, make_pair("", ""));
    vector<string> empty_clause_vector;
    backtracking_index_init();

    while(t.GetElapsedMillseconds()<3600000 && !optimal){
        // cout << "DEBUG" << "========" << endl;
        // cout << "from start: " << from_start << endl;
        // cout << "projection: " << projection << endl;
        // cout << "DEBUG" << "========" << endl;
        // if(!timeout_reverse){
        //     reverse(circuit_1_output_group.begin(), circuit_1_output_group.end());
        //     reverse(circuit_2_output_group.begin(), circuit_2_output_group.end());
        //     timeout_reverse = true;
        // }

        if(new_pair(sat)){
            if(optimal) continue;

            output_matching_result.emplace_back(new_output_pair);
            construct_constraint_2(output_matching_result);
            used_times[(new_output_pair.second).first]++;
            from_start = true;
            learned_clause.emplace_back(empty_clause_vector);
            constraint_4.emplace_back(empty_clause_vector);
            cout << "learned_clause_size: " << learned_clause.size() << endl;
        }
        else{
            if(!projection){
                projection = true;
                from_start = true;
            }
            else{
                // cout << "**********" << endl;
                // cout << "size: " << output_matching_result.size() << endl;
                // for(auto it : backtracking_index) cout << it.second << " ";
                // cout << endl;

                last_output_pair = output_matching_result.back();
                // cout << "last_pair" << (last_output_pair.second).first << " ," << (last_output_pair.second).second << endl;
                if(output_matching_result.size()>0){
                    output_matching_result.pop_back();
                    learned_clause.pop_back();
                    constraint_4.pop_back();
                    // constraint_2.pop_back();
                }
                cout << "learned_clause_size: " << learned_clause.size() << endl;
                used_times[(last_output_pair.second).first]--;
                last_output_pair = output_matching_result.back();
                projection = false;
                from_start = false;
                sat = false;
            }
            continue;
        }

        //for debug
        show_current_output_matching_result();

        sat = input_solver(output_matching_result);
        if(!sat){
            if(output_matching_result.size()>0){
                last_output_pair = output_matching_result.back();
                output_matching_result.pop_back();
                learned_clause.pop_back();
                constraint_4.pop_back();
                // constraint_2.pop_back();
                cout << "learned_clause_size: " << learned_clause.size() << endl;
                cout << "output_matching_result_size: " << output_matching_result.size() << endl;
                used_times[(last_output_pair.second).first]--;
            }
            // if(output_matching_result.size()>0)
            //     last_output_pair = output_matching_result.back();
            from_start = false;
        }
        else{
            last_output_pair = output_matching_result.back();
            if(projection) projection = false;
        }

        // for(auto f : circuit_1_output){
        //     if(used_times[f] <= 1){
        //         optimal = true;
        //     }else{
        //         optimal = false;
        //         break;
        //     }
        // }
        
        if(optimal) cout << "OPTIMAL!" << endl;
        else cout << "NOT OPTIMAL!" << endl;
        // current_time = clock();
        cout << "CURRENT TIME: " << t.GetElapsedMillseconds()/1000 << "sec" << endl;
        if(output_matching_result.size() > optimal_result_size && sat){
            cout << "output_matching_result_size: " << output_matching_result.size() << endl;
            cout << "optimal_result_size: " << optimal_result_size << endl;
            cout << "sat: " << sat << endl;
            optimal_result_size = output_matching_result.size();
            construct_final_result_file(output_file_path, output_matching_result);
        }
    }
}