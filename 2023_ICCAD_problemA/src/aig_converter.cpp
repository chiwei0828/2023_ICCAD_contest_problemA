#include <iostream>
#include <cstdlib>
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <cstring>
#include <sstream>
#include <set>
#include "utility.h"
#include "aig_converter.h"

using namespace std;

//variables for AIG
long long int maximal_variable_index, number_of_inputs, number_of_outputs, number_of_latches, number_of_and_gates, num_tmp;
// unordered_map<long long int, pair<long long int, long long int>> AND_gate;
set<pair<long long int, pair<long long int, long long int>>> AND_gate;
unordered_map<long long int, string> input_mapping, output_mapping;
unordered_map<string, string> circuit1_function, circuit2_function;
vector<string> input_variable, output_variable;
unordered_map<long long int, string> dp;
unordered_map<string, long long int> circuit_1_aig_input_mapping, circuit_1_aig_output_mapping;
unordered_map<string, long long int> circuit_2_aig_input_mapping, circuit_2_aig_output_mapping;
fstream * mapping_file;
long long int circuit_1_number_of_outputs, circuit_2_number_of_outputs;
long long int circuit_1_number_of_inputs, circuit_2_number_of_inputs;
vector<pair<string, long long int>> circuit_1_used_input, circuit_1_unused_input;
vector<pair<string, long long int>> circuit_2_used_input, circuit_2_unused_input;
vector<pair<string, long long int>> circuit_1_used_output, circuit_1_unused_output;
vector<pair<string, long long int>> circuit_2_used_output, circuit_2_unused_output;
vector<string> circuit_1_input, circuit_2_input;
vector<string> circuit_1_output, circuit_2_output;

//used when output is binding to a constant
long long int output_port_replace_index;
long long int output_port_replace_index_start, output_port_replace_index_end;

void IO_File_Preprocessing(fstream * IO_file, int cir){
    string tmp1, tmp2, tmp3, tmp;
    string var, line;
    vector<string> input_tmp, output_tmp;
    stringstream ss;

    getline((*IO_file), line);
    ss << line;
    for(long long int i=0; i<number_of_inputs+4; i++){
        getline(ss, var, ' ');
        if(i >= 4) input_tmp.emplace_back(var);
    }

    ss.clear();
    ss.str(""); 

    getline((*IO_file), line);
    ss << line;
    for(long long int i=0; i<number_of_outputs+3; i++){
        getline(ss, var, ' ');
        if(i >= 3) output_tmp.emplace_back(var);
    }

    ss.clear();
    ss.str(""); 

    //input
    long long int id = 0;
    for(auto it : input_tmp){
        stringstream ss1(it);
        bool use = false;
        while(getline(ss1, tmp, '=')){
            if(!use) use = true;
            else{
                input_variable.emplace_back(tmp);
                if(cir == 1){
                    circuit_1_unused_input.emplace_back(pair<string, long long int>(tmp, 0));
                    circuit_1_input.emplace_back(tmp);
                    circuit_1_port_id_input_mapping[tmp] = id; 
                    circuit_1_is_input[tmp] = true;
                }
                else if(cir == 2){
                    circuit_2_unused_input.emplace_back(pair<string, long long int>(tmp, 0));
                    circuit_2_input.emplace_back(tmp);
                    circuit_2_port_id_input_mapping[tmp] = id; 
                    circuit_2_is_input[tmp] = true;
                }
                //cout << "Preprocessing: " << tmp << endl;
                id++;
                use = false;
            }
        }

    }

    //output
    id = 0;
    for(auto it : output_tmp){
        stringstream ss2(it);
        bool use = false;
        while(getline(ss2, tmp, '=')){
            if(!use) use = true;
            else{
                output_variable.emplace_back(tmp);
                if(cir == 1){
                    circuit_1_unused_output.emplace_back(pair<string, long long int>(tmp, 0));
                    circuit_1_output.emplace_back(tmp);
                    circuit_1_port_id_output_mapping[tmp] = id; 
                    circuit_1_is_input[tmp] = false;
                }
                else if(cir == 2){
                    circuit_2_unused_output.emplace_back(pair<string, long long int>(tmp, 0));
                    circuit_2_output.emplace_back(tmp);
                    circuit_2_port_id_output_mapping[tmp] = id; 
                    circuit_2_is_input[tmp] = false;
                }
                //cout << "Preprocessing: " << tmp << endl;
                id++;
                use = false;
            }
        }

    }
}

// string aig_traverse(long long int gate_){
//     stringstream ssA, ssB, ssC;
//     ostringstream ossA, ossB, ossC;
//     long long int gateA, gateB;
//     bool phaseA=true, phaseB=true;
//     long long int numA=0, numB=0;
//     // cout << "Current Gate*: " << gate_ << endl;
//     auto it = input_mapping.find(gate_);
//     auto dp_it = dp.find(gate_);
//     if(dp_it != dp.end()){
//         return dp[gate_];
//     }
//     else if(it != input_mapping.end()){
//         dp[gate_] = it->second;
//         return dp[gate_];
//     }else{
//         auto it_ = AND_gate.find(gate_);
//         gateA = (it_->second).first; gateB = (it_->second).second;
//         // cout <<"1: "<< "Current Gate A: " << gateA << ", " << "Current Gate B: " << gateB << endl;

//         //gateA
//         //ssA << gateA; ssA >> num;
//         if(gateA % 2 == 0){
//             // ossA << num;
//             // gateA = ossA.str();
//             numA = gateA;
//             phaseA = true;
//         }else if(gateA % 2 == 1){
//             // ossA << (num-1);
//             // gateA = ossA.str();
//             numA= gateA - 1;
//             phaseA = false;
//         }

//         //gateB
//         // ssB << gateB; ssB >> num;
//         if(gateB % 2 == 0){
//             // ossB << num;
//             // gateB = ossB.str();
//             numB = gateB;
//             phaseB = true;
//         }else if(gateB % 2 == 1){
//             // ossB << (num-1);
//             // gateB = ossB.str();
//             numB = gateB - 1;
//             phaseB = false;
//         }
//         // cout <<"2: "<< "Current Gate A: " << gateA << ", " << "Current Gate B: " << gateB << endl;
//         dp[gate_] = ((phaseA)?"(":"-(") + aig_traverse(numA) + ")*" + ((phaseB)?"(":"-(") + aig_traverse(numB) + ")";
//         return dp[gate_];
//     }

// }

void aig_traverse(int cir){
    // problem dp[0] = 1'b0 in aag files
    // for(const auto &it : AND_gate){
    //     auto A = (it.second).first, B = (it.second).second;
    //     bool phaseA = true, phaseB = true;

    //     if(A%2 == 1) phaseA = false, A-=1;
    //     if(B%2 == 1) phaseB = false, B-=1;

    //     dp[it.first] = ((phaseA)?"(":"(-") + dp[A] + "*" + ((phaseB)?"":"-") + dp[B] + ")";
    // }
    cout << "maximal_variable_index: " << maximal_variable_index << endl;
    cout << "output_port_replace_index_start: " << output_port_replace_index_start << endl;
    cout << "output_port_replace_index_end: " << output_port_replace_index_end << endl;
    if(cir == 1){
        circuit1_cnf_number_of_variables = (output_port_replace_index_end > output_port_replace_index_start)?output_port_replace_index_end:output_port_replace_index_start;
        // circuit1_cnf_number_of_variables = 2*maximal_variable_index+2;
        // circuit1_cnf_number_of_variables = 2*maximal_variable_index+1;
        for(const auto &it : AND_gate){
            auto A = (it.second).first, B = (it.second).second;
            bool phaseA = true, phaseB = true;

            if(A%2 == 1) phaseA = false, A-=1;
            if(B%2 == 1) phaseB = false, B-=1;

            circuit1_cnf_clauses.emplace_back("-"+to_string(it.first) + (((phaseA)?" ":" -")+to_string(A)) + " 0");
            circuit1_cnf_clauses.emplace_back("-"+to_string(it.first) + (((phaseB)?" ":" -")+to_string(B)) + " 0");
            circuit1_cnf_clauses.emplace_back(to_string(it.first) + (((phaseA)?" -":" ")+to_string(A)) + (((phaseB)?" -":" ")+to_string(B)) + " 0");
        }
        for(auto f : circuit_1_output){
            if(output_port_replace_index_start <= stoll(circuit_1_port_cnf_output_mapping[f]) && stoll(circuit_1_port_cnf_output_mapping[f]) <= output_port_replace_index_end){
                cout << "1 debug input binding constant: " << f << " -> " << ((buffer_phase[f])?"1":"0") << endl;
                if(!buffer_phase[f])circuit1_cnf_clauses.emplace_back("-"+circuit_1_port_cnf_output_mapping[f] + " 0");
                else if(buffer_phase[f])circuit1_cnf_clauses.emplace_back(circuit_1_port_cnf_output_mapping[f] + " 0");
            }
            else if(stoll(circuit_1_port_cnf_output_mapping[f])%2==1){
                cout << "aig debug 1: " << f << endl;
                string A = circuit_1_port_cnf_output_mapping[f];
                string B = to_string(stoll(circuit_1_port_cnf_output_mapping[f])-1);
                circuit1_cnf_clauses.emplace_back("-"+A + " -"+B + " 0");
                circuit1_cnf_clauses.emplace_back(A + " " + B + " 0");
            }
        }
        circuit1_cnf_number_of_clauses = circuit1_cnf_clauses.size();
    }
    else if(cir == 2){
        circuit2_cnf_number_of_variables = (output_port_replace_index_end > output_port_replace_index_start)?output_port_replace_index_end:output_port_replace_index_start;
        // circuit2_cnf_number_of_variables = 2*maximal_variable_index+2;
        // circuit2_cnf_number_of_variables = 2*maximal_variable_index+1;
        for(const auto &it : AND_gate){
            auto A = (it.second).first, B = (it.second).second;
            bool phaseA = true, phaseB = true;

            if(A%2 == 1) phaseA = false, A-=1;
            if(B%2 == 1) phaseB = false, B-=1;

            circuit2_cnf_clauses.emplace_back("-"+to_string(it.first) + (((phaseA)?" ":" -")+to_string(A)) + " 0");
            circuit2_cnf_clauses.emplace_back("-"+to_string(it.first) + (((phaseB)?" ":" -")+to_string(B)) + " 0");
            circuit2_cnf_clauses.emplace_back(to_string(it.first) + (((phaseA)?" -":" ")+to_string(A)) + (((phaseB)?" -":" ")+to_string(B)) + " 0");
        }
        for(auto g : circuit_2_output){
            if(output_port_replace_index_start <= stoll(circuit_2_port_cnf_output_mapping[g]) && stoll(circuit_2_port_cnf_output_mapping[g]) <= output_port_replace_index_end){
                cout << "2 debug input binding constant: " << g << " -> " << ((buffer_phase[g])?"1":"0") << endl;
                if(!buffer_phase[g])circuit2_cnf_clauses.emplace_back("-"+circuit_2_port_cnf_output_mapping[g] + " 0");
                else if(buffer_phase[g])circuit2_cnf_clauses.emplace_back(circuit_2_port_cnf_output_mapping[g] + " 0");
            }
            else if(stoll(circuit_2_port_cnf_output_mapping[g])%2==1){
                cout << "aig debug 2: " << g << endl;
                string A = circuit_2_port_cnf_output_mapping[g];
                string B = to_string(stoll(circuit_2_port_cnf_output_mapping[g])-1);
                circuit2_cnf_clauses.emplace_back("-"+A + " -"+B + " 0");
                circuit2_cnf_clauses.emplace_back(A + " " + B + " 0");
            }
        }
        circuit2_cnf_number_of_clauses = circuit2_cnf_clauses.size();
    }
}

int aig_to_pos(fstream * AIG_file, fstream * IO_file, int cir){
    if(!AIG_file->is_open()){
        cout << "Open Fail:" << " AIG File" << endl;
        exit(1);
    }else if(!IO_file->is_open()){
        cout << "Open Fail:" << " IO_file " << endl;
        exit(1);
    }else{
        mapping_file = new fstream;
        if(cir == 1)mapping_file->open("mapping_file_1", std::ios::out);
        if(cir == 2)mapping_file->open("mapping_file_2", std::ios::out);
        if(!mapping_file->is_open()){
            cout << "Open Fail:" << "mapping_file" << endl;
            exit(1);
        }

        //(*AIG_file) >> tmp >>  maximal_variable_index >> number_of_inputs >> number_of_latches >> number_of_outputs >> number_of_and_gates;
        string line, tmp;
        getline((*AIG_file), line);
        stringstream ss;
        int cur_state = 0;

        ss << line;
        while(getline(ss, tmp, ' ')){
            stringstream ss_;
            //cout << tmp << endl;
            if(cur_state == 1){
                ss_ << tmp;
                ss_ >> maximal_variable_index;
                output_port_replace_index = 2*maximal_variable_index+2;
                output_port_replace_index_end = output_port_replace_index_start = output_port_replace_index;
            }else if(cur_state == 2){
                ss_ << tmp;
                ss_ >> number_of_inputs;
                if(cir == 1) circuit_1_number_of_inputs = number_of_inputs;
                else if(cir == 2) circuit_2_number_of_inputs = number_of_inputs;
            }else if(cur_state == 3){
                ss_ << tmp;
                ss_ >> number_of_latches;
            }else if(cur_state == 4){
                ss_ << tmp;
                ss_ >> number_of_outputs;
                if(cir == 1) circuit_1_number_of_outputs = number_of_outputs;
                else if(cir == 2) circuit_2_number_of_outputs = number_of_outputs;
            }else if(cur_state == 5){
                ss_ << tmp;
                ss_ >> number_of_and_gates;
            }
            cur_state++;
        }
        
        IO_File_Preprocessing(IO_file, cir);

        //input
        for(long long int i=0; i<number_of_inputs; i++){
            string gate1, gate2, gate3;
            stringstream ss_tmp, ss_tmp2;
            getline((*AIG_file), gate1);
            ss_tmp << gate1; ss_tmp >> num_tmp;
            if(cir == 1){
                circuit_1_aig_input_mapping.insert(pair<string, long long int>(input_variable[i], num_tmp));
                
                // long long int num_tmp2 = num_tmp/2;
                long long int num_tmp2 = num_tmp;
                ss_tmp2 << num_tmp2;
                ss_tmp2 >> gate1;
                // circuit_1_port_cnf_input_mapping.insert(pair<string, string>(input_variable[i], circuit_1_aig_cnf_mapping[gate1]));
                // circuit_1_cnf_port_input_mapping.insert(pair<string, string>(circuit_1_aig_cnf_mapping[gate1], input_variable[i]));
                //20230704 revised:
                circuit_1_port_cnf_input_mapping.insert(pair<string, string>(input_variable[i], gate1));
                circuit_1_cnf_port_input_mapping.insert(pair<string, string>(gate1, input_variable[i]));
            }
            else if(cir == 2){
                circuit_2_aig_input_mapping.insert(pair<string, long long int>(input_variable[i], num_tmp));

                // long long int num_tmp2 = num_tmp/2;
                long long int num_tmp2 = num_tmp;
                ss_tmp2 << num_tmp2;
                ss_tmp2 >> gate1;
                // circuit_2_port_cnf_input_mapping.insert(pair<string, string>(input_variable[i], circuit_2_aig_cnf_mapping[gate1]));
                // circuit_2_cnf_port_input_mapping.insert(pair<string, string>(circuit_2_aig_cnf_mapping[gate1], input_variable[i]));
                //20230704 revised:
                circuit_2_port_cnf_input_mapping.insert(pair<string, string>(input_variable[i], gate1));
                circuit_2_cnf_port_input_mapping.insert(pair<string, string>(gate1, input_variable[i]));
            }
            input_mapping.insert(pair<long long int, string>(num_tmp, input_variable[i]));

            dp[num_tmp] = input_variable[i];
        }   
        //output
        for(long long int i=0; i<number_of_outputs; i++){
            string gate1, gate2, gate3;
            stringstream ss_tmp, ss_tmp2;
            getline((*AIG_file), gate1);
            ss_tmp << gate1; ss_tmp >> num_tmp;
            if(cir == 1){
                circuit_1_aig_output_mapping.insert(pair<string, long long int>(output_variable[i], num_tmp));

                // long long int num_tmp2 = num_tmp/2;
                // long long int num_tmp2 = num_tmp;
                // ss_tmp2 << num_tmp2;
                // ss_tmp2 >> gate1;
                // circuit_1_port_cnf_output_mapping.insert(pair<string, string>(output_variable[i], circuit_1_aig_cnf_mapping[gate1]));
                // circuit_1_cnf_port_output_mapping.insert(pair<string, string>(circuit_1_aig_cnf_mapping[gate1], output_variable[i]));
                //20230704 revised:
                if(gate1 == "0"){
                    ss_tmp2 << output_port_replace_index_end;
                    ss_tmp2 >> gate1;
                    output_port_replace_index_end += 2;
                    circuit_1_port_cnf_output_mapping.insert(pair<string, string>(output_variable[i], gate1));
                    circuit_1_cnf_port_output_mapping.insert(pair<string, string>(gate1, output_variable[i]));
                    buffer_phase[output_variable[i]] = false;
                }
                else if(gate1 == "1"){
                    ss_tmp2 << output_port_replace_index_end;
                    ss_tmp2 >> gate1;
                    output_port_replace_index_end += 2;
                    circuit_1_port_cnf_output_mapping.insert(pair<string, string>(output_variable[i], gate1));
                    circuit_1_cnf_port_output_mapping.insert(pair<string, string>(gate1, output_variable[i]));
                    buffer_phase[output_variable[i]] = true;
                }
                else{
                    long long int num_tmp2 = num_tmp;
                    ss_tmp2 << num_tmp2;
                    ss_tmp2 >> gate1;
                    circuit_1_port_cnf_output_mapping.insert(pair<string, string>(output_variable[i], gate1));
                    circuit_1_cnf_port_output_mapping.insert(pair<string, string>(gate1, output_variable[i]));
                }
            }
            else if(cir == 2){
                circuit_2_aig_output_mapping.insert(pair<string, long long int>(output_variable[i], num_tmp));

                // long long int num_tmp2 = num_tmp/2;
                // long long int num_tmp2 = num_tmp;
                // ss_tmp2 << num_tmp2;
                // ss_tmp2 >> gate1;
                // circuit_2_port_cnf_output_mapping.insert(pair<string, string>(output_variable[i], circuit_2_aig_cnf_mapping[gate1]));
                // circuit_2_cnf_port_output_mapping.insert(pair<string, string>(circuit_2_aig_cnf_mapping[gate1], output_variable[i]));
                //20230704 revised:
                if(gate1 == "0"){
                    ss_tmp2 << output_port_replace_index_end;
                    ss_tmp2 >> gate1;
                    output_port_replace_index_end += 2;
                    circuit_2_port_cnf_output_mapping.insert(pair<string, string>(output_variable[i], gate1));
                    circuit_2_cnf_port_output_mapping.insert(pair<string, string>(gate1, output_variable[i]));
                    buffer_phase[output_variable[i]] = false;
                }
                else if(gate1 == "1"){
                    ss_tmp2 << output_port_replace_index_end;
                    ss_tmp2 >> gate1;
                    output_port_replace_index_end += 2;
                    circuit_2_port_cnf_output_mapping.insert(pair<string, string>(output_variable[i], gate1));
                    circuit_2_cnf_port_output_mapping.insert(pair<string, string>(gate1, output_variable[i]));
                    buffer_phase[output_variable[i]] = true;
                }
                else{
                    long long int num_tmp2 = num_tmp;
                    ss_tmp2 << num_tmp2;
                    ss_tmp2 >> gate1;
                    circuit_2_port_cnf_output_mapping.insert(pair<string, string>(output_variable[i], gate1));
                    circuit_2_cnf_port_output_mapping.insert(pair<string, string>(gate1, output_variable[i]));
                }
            }
            output_mapping.insert(pair<long long int, string>(num_tmp, output_variable[i]));

            //Equal set
            if(cir == 1){
                //TODO:
            }else if(cir == 2){
                //TODO:
            }
        }
        output_port_replace_index_end -= 2;
        // output_port_replace_index_end = output_port_replace_index;

        //AND gate
        string tmp_1, tmp_2;

        while(getline((*AIG_file), tmp_1)){
            if(tmp_1 == "c")  break;
                
            long long int gate1, gate2, gate3;
            stringstream ss_;
            ss_ << tmp_1;

            cur_state = 1;
            while(getline(ss_, tmp_2, ' ')){
                stringstream ss_tmp;
                if(cur_state == 1){
                    ss_tmp << tmp_2;
                    ss_tmp >> gate1;
                }else if(cur_state == 2){
                    ss_tmp << tmp_2;
                    ss_tmp >> gate2;
                }else if(cur_state == 3){
                    ss_tmp << tmp_2;
                    ss_tmp >> gate3;
                }
                cur_state++;
            }
            AND_gate.insert(pair<long long int, pair<long long int, long long int>>(gate1, pair<long long int, long long int>(gate2, gate3)));
        }
        
        // for(auto j = input_mapping.begin(); j!=input_mapping.end(); j++){
        //     cout << "INPUT: " <<"first: " << j->first << ", second: " << j->second << endl;
        // }
        // for(auto j = output_mapping.begin(); j!=output_mapping.end(); j++){
        //     cout << "OUTPUT: " << "first: " << j->first << ", second: " << j->second << endl;
        // }
            
        //transformation
        aig_traverse(cir);
        // for(auto it = output_mapping.begin(); it != output_mapping.end(); it++){
        //     long long int output_number = it->first;
        //     string output_representation;
        //     string output_port = it->second, equal_symbol = "=", function;
        //     stringstream ss;
        //     ostringstream oss;
        //     string gate, gateA, gateB;
        //     bool phase;
        //     long long int num;
        //     // cout << "Current Output Gate: " << output_representation << endl;
        //     // ss << output_number; ss >> num;
        //     if(output_number % 2 == 0){
        //         // oss << output_number;
        //         // gate = oss.str();
        //         num = output_number;
        //         phase = true;
        //     }else if(output_number % 2 == 1){
        //         // oss << (output_number-1);
        //         // gate = oss.str();
        //         num = output_number - 1;
        //         phase = false;
        //     }
            
        //     auto it_ = input_mapping.find(num);
        //     // cout << "Current Gate: " << gate << endl;

        //     if(it_ != input_mapping.end()){
        //         function = ((phase)?"":"-") + it_->second;
        //     }else{
        //         // function = ((phase)?"(":"-(") + aig_traverse(num) + ")";
        //         function = ((phase)?"":"-") +dp[num];
        //     }
        //     if(cir == 1){
        //         circuit1_function.insert(pair<string, string>(output_port, function));
        //         // for(auto it = circuit1_function.begin(); it!=circuit1_function.end(); it++){
        //         //     cout << "CIRCUIT1: " <<"output: " << it->first << ", function: " << it->second << endl;
        //         // }
        //     }else if(cir == 2){
        //         circuit2_function.insert(pair<string, string>(output_port, function));
        //         // for(auto it = circuit2_function.begin(); it!=circuit2_function.end(); it++){
        //         //     cout << "CIRCUIT2: " <<"output: " << it->first << ", function: " << it->second << endl;
        //         // }
        //     }

        //     //(*mapping_file) << output_port + " " + equal_symbol + " " + function << '\n';
        //     (*mapping_file) << function << '\n';
        // }

        mapping_file->close();
        mapping_file->clear();
        input_variable.clear();
        output_variable.clear();
        input_mapping.clear();
        output_mapping.clear();
        AND_gate.clear();
        dp.clear();
    }
    return 0;
}