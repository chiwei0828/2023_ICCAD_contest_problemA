#include <iostream>
#include <cstdlib>
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <cstring>
#include <cstdio>
#include <stdio.h>
#include <ctime>
#include "utility.h"
#include "aig_converter.h"
#include "output_solver.h"
#include "input_solver.h"
// #include "../lib/sequential-solvers/Kissat_MAB-HyWalk/src/kissat.h"
// #include "../lib/sequential-solvers/Kissat_MAB-HyWalk/src/report.h"
#include "aiger.h"
// #include "../lib/sequential-solvers/CaDiCaL_DVDL_V1/build/cadical/src/cadical.hpp"
// #include "../lib/cadical/src/cadical.hpp"
#include "cadical.hpp"

#define ReadInputFile_check false
using namespace std;

// run main
// ./main input.txt output.txt

// Abc_ObjFaninNum
// Abc_NtkToLogic
// Abc_CommandLogic
// Io_Read //ioUtil.c
// Sim_ComputeFunSupp
// CaDiCal
// Abc_NtkVerifySimulatePattern

// ./testcase/2016_ICCAD_contest_testcase/case0/cir1.v
// ./testcase/2016_ICCAD_contest_testcase/case0/cir2.v

//SAT solver
// MiniSAT("sat_testcase.cnf", "sat_testcase_result");
// Kissat("sat_testcase.cnf");
//./lib/SAT-Solver/sat <mapping_file_1>mapping_file_1.out 

string input_file_path, output_file_path, cir1_file_path, cir2_file_path;
fstream * input_file, * cir1_file, * cir2_file, * AIG_file, * IO_file;
string cir1_bus_num, cir2_bus_num;
// vector<vector<string>> cir1_bus_set, cir2_bus_set;
// unordered_map<string, pair<long long int, vector<string>>> cir1_bus_set, cir2_bus_set;
vector<pair<long long int, vector<string>>> cir1_bus_set, cir2_bus_set;
vector<pair<long long int, vector<string>>> cir1_input_bus_set, cir2_input_bus_set;
vector<pair<long long int, vector<string>>> cir1_output_bus_set, cir2_output_bus_set;
Abc_Frame_t * pAbc;
Abc_Ntk_t * pNtk1, * pNtk2;
Abc_Obj_t * pObj;
Cnf_Dat_t * pCnfDat;
Cnf_Man_t_ * pCnfMan;
Gia_Man_t_ * pGiaMan;
FILE *fp, *fp2, *fErr;
char * aig_file[2];
int pfDelete1, pfDelete2;
char Command[1000];


//Berkeley ABC
inline void Read_Input_File(){
    input_file = new fstream;
    input_file->open(input_file_path, std::ios::in);

    if(!input_file->is_open()){
        cout << "Open Fail:" << input_file_path << endl;
        exit(1);
    }else{
        string bus_size;
        string port, line;

        //Read the first circuit
        // (*input_file) >> cir1_file_path >> cir1_bus_num;
        getline((*input_file), cir1_file_path);
        getline((*input_file), cir1_bus_num);
        // ss1 << line; ss1 >> cir1_bus_num;
        long long int cir1_bus_num_ = stoll(cir1_bus_num);
        for(int i=0; i<cir1_bus_num_; i++){
            stringstream ss;
            getline((*input_file), line);
            ss << line;
            getline(ss, bus_size, ' ');

            vector<string> bus;
            // cout << bus_size << endl;
            long long int bus_size_ = stoll(bus_size);

            for(int j=0; j<bus_size_; j++){
                getline(ss, port, ' ');
                bus.emplace_back(port);
            }
            // for(auto it: bus){
            //     cir1_bus_set.emplace_back(pair<long long int, vector<string>>(bus_size_, bus));
            // }
            cir1_bus_set.emplace_back(pair<long long int, vector<string>>(bus_size_, bus));
        }

        //Read the second circuit
        // (*input_file) >> cir2_file_path >> cir2_bus_num;
        getline((*input_file), cir2_file_path);
        getline((*input_file), cir2_bus_num);
        long long int cir2_bus_num_ = stoll(cir2_bus_num);
        for(int i=0; i<cir2_bus_num_; i++){
            stringstream ss;
            getline((*input_file), line);
            ss << line;
            getline(ss, bus_size, ' ');

            vector<string> bus;
            // cout << bus_size << endl;
            long long int bus_size_ = stoll(bus_size);

            for(int j=0; j<bus_size_; j++){
                getline(ss, port, ' ');
                bus.emplace_back(port);
            }
            // for(auto it: bus){
            //     cir1_bus_set.emplace_back(pair<long long int, vector<string>>(bus_size_, bus));
            // }
            cir2_bus_set.emplace_back(pair<long long int, vector<string>>(bus_size_, bus));
        }

        //Check
        if(ReadInputFile_check){
            cout << cir1_file_path << endl;
            cout << cir2_file_path << endl;
            for(auto it: cir1_bus_set){
                cout << it.first << endl;
                for(auto it2: (it.second)){
                    cout << " " << it2;
                }
                cout << endl;
            }
            for(auto it: cir2_bus_set){
                cout << it.first << endl;
                for(auto it2: (it.second)){
                    cout << " " << it2;
                }
                cout << endl;
            }
        }

        input_file->close();
        // delete input_file;
        input_file->clear();
    }

    return;
}
inline int ABC_Read(string file){
    sprintf( Command, "read %s", file.c_str());
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }

    return 0;
}
inline int ABC_Write(string format, string file_name){
    sprintf( Command, "%s %s",format.c_str(), file_name.c_str());
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    return 0;
}
inline int ABC_Fraig(){
    sprintf( Command, "fraig_clean");
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    sprintf( Command, "fraig");
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    return 0;
}
inline int ABC_Memory_Empty(){
    sprintf( Command, "empty");
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    return 0;
}
inline int ABC_Balance(){
    sprintf( Command, "balance");
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    return 0;
}
inline void ABC_Get_IO(string file_name, int cir){
    if(cir == 1){
        pNtk1 = Abc_FrameReadNtk(pAbc);
        fp = fopen(file_name.c_str(), "w+");
        if(fp != NULL){
            Abc_NtkPrintIo(fp, pNtk1, 0);
            // Abc_NtkPrintIo(stdout, pNtk, 0);
            // for (int i = 0; (i < Abc_NtkPiNum(pNtk)) && (((pObj) = Abc_NtkPi(pNtk, i)), 1); i++ )
            //     fprintf( fp, "%s ",Abc_ObjName(pObj) );
            // fprintf( fp, "\n" );
            fclose(fp);
        }
    } else if(cir == 2){
        pNtk2 = Abc_FrameReadNtk(pAbc);
        fp = fopen(file_name.c_str(), "w+");
        if(fp != NULL){
            Abc_NtkPrintIo(fp, pNtk2, 0);
            // Abc_NtkPrintIo(stdout, pNtk, 0);
            // for (int i = 0; (i < Abc_NtkPiNum(pNtk)) && (((pObj) = Abc_NtkPi(pNtk, i)), 1); i++ )
            //     fprintf( fp, "%s ",Abc_ObjName(pObj) );
            // fprintf( fp, "\n" );
            fclose(fp);
        }
    }
}
inline void ABC_Get_SupportSet_Info(string file_name, int cir){
    //Print Support Set information
    if(cir == 1){
        string str;
        pNtk1 = Abc_FrameReadNtk(pAbc);
        fp2 = fopen(file_name.c_str(), "w+");
        if(fp2 != NULL){
            Abc_NtkPrintStrSupports(pNtk1, 1, fp2);
            fclose(fp2);
        }
    }else if(cir == 2){
        string str;
        pNtk2 = Abc_FrameReadNtk(pAbc);
        fp2 = fopen(file_name.c_str(), "w+");
        if(fp2 != NULL){
            Abc_NtkPrintStrSupports(pNtk2, 1, fp2);
            fclose(fp2);
        }
    }
}
inline int ABC_to_gia(string file_name){
    sprintf( Command, "&get %s", file_name.c_str());
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    return 0;
}
inline int ABC_Cleanup(){
    sprintf( Command, "cleanup");
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    return 0;
}
inline int ABC_Symmetry_Property(){
    sprintf( Command, "print_symm");
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    return 0;
}
inline int ABC_Strash(string module_name){
    sprintf( Command, "strash %s", module_name.c_str());
    if ( Cmd_CommandExecute( pAbc, Command ) )
    {
        fprintf( stdout, "Cannot execute command \"%s\".\n", Command );
        return 1;
    }
    return 0;
}

//Aiger
FILE* file, * file2;
inline void Aiger_Transformation(string file_name){
    aiger* aig_file_pointer;
    aig_file_pointer = aiger_init();
    aiger_open_and_read_from_file(aig_file_pointer, (file_name+".aig").c_str());
    aiger_open_and_write_to_file (aig_file_pointer, (file_name+".aag").c_str());
    aiger_reset (aig_file_pointer);
    return;
}

//SAT solver
inline int Kissat(string SAT_input_file){
    string cmd = "./lib/sequential-solvers/Kissat_MAB-HyWalk/build/kissat " + SAT_input_file;
    return system(cmd.c_str());
}

int main(int argc, char* argv[]){

    t.Reset();

    if(argc == 3){
        input_file_path = argv[1];
        output_file_path = argv[2];
    }

    //Read input file
    Read_Input_File();

    Abc_Start();
    pAbc = Abc_FrameGetGlobalFrame();
    // pNtk = Abc_FrameReadNtk(pAbc);
    // cout << "pAbc: " << pAbc << endl;
    // cout << "pNtk: " << pNtk << endl;

    AIG_file = new fstream;
    IO_file = new fstream;

    // cir1_file_path = "testcase/release/case05/circuit_1.v";
    // cir2_file_path = "testcase/release/case05/circuit_2.v";

    //Read circuit 1 file
    ABC_Memory_Empty();
    ABC_Read(cir1_file_path);
    ABC_Fraig();
    // ABC_Balance();
    cout << "===== Symmetry Property =====" << endl;
    // ABC_Symmetry_Property();
    cout << "===== Symmetry Property =====" << endl;
    ABC_Write("write_aiger", "circuit_1.aig");
    ABC_to_gia("circuit_1.aig");
    // ABC_Write("&write_cnf -i ", "circuit_1.cnf");
    ABC_Write("write_cnf", "circuit_1.cnf");

    aig_to_cnf_number("aig_number_to_cnf_number", 1);
    Aiger_Transformation("circuit_1");

    ABC_Get_IO("IO_FILE_1", 1);
    AIG_file->open("circuit_1.aag", std::ios::in);
    IO_file->open("IO_FILE_1", std::ios::in);
    aig_to_pos(AIG_file, IO_file, 1);
    AIG_file->close();
    IO_file->close();
    ABC_Get_SupportSet_Info("SUPP_FILE_1", 1);
    get_support_set("SUPP_FILE_1", 1);

    //===============================================================================================/

    //Read circuit 2 file
    ABC_Memory_Empty();
    ABC_Read(cir2_file_path);
    ABC_Fraig();
    // ABC_Balance();
    cout << "===== Symmetry Property =====" << endl;
    // ABC_Symmetry_Property();
    cout << "===== Symmetry Property =====" << endl;
    ABC_Write("write_aiger", "circuit_2.aig");
    ABC_to_gia("circuit_2.aig");
    // ABC_Write("&write_cnf -i ", "circuit_2.cnf");
    ABC_Write("write_cnf", "circuit_2.cnf");
    
    aig_to_cnf_number("aig_number_to_cnf_number", 2);
    Aiger_Transformation("circuit_2");

    ABC_Get_IO("IO_FILE_2", 2);
    AIG_file->open("circuit_2.aag", std::ios::in);
    IO_file->open("IO_FILE_2", std::ios::in);
    aig_to_pos(AIG_file, IO_file, 2);
    AIG_file->close();
    AIG_file->clear();
    IO_file->close();
    IO_file->clear();
    ABC_Get_SupportSet_Info("SUPP_FILE_2", 2);
    get_support_set("SUPP_FILE_2", 2);


    // cout <<"SUPPORT SET SIZE DEBUG:" << endl;
    // for(auto f : circuit_1_output){
    //     cout << f << ": " << support_set_size_1[f] << endl;
    // }
    // for(auto g : circuit_2_output){
    //     cout << g << ": " << support_set_size_2[g] << endl;
    // }

    // get_cnf_file_record("circuit_1.cnf", 1);
    // get_cnf_file_record("circuit_2.cnf", 2);
    // cnf_file_combine("circuit_combined.cnf");
    // cout << "cnf_file_combine2" << endl;
    cnf_file_combine2("circuit_combined.cnf");
    // construct_output_pair_table();
    // construct_input_pair_table();
    construct_input_pair_matrix();
    // construct_constraint_1();
    construct_constraint_1_matrix_version();
    construct_constraint_3();
    // if(circuit_1_number_of_inputs == circuit_2_number_of_inputs)
        construct_constraint_5();
    // cout << "constraint_3.size(): " << constraint_3.size() << endl;
    // cout << "step5 done" << endl;
    Output_grouping(circuit_2_number_of_outputs);

    // cout <<"SUPPORT SET SIZE DEBUG:" << endl;
    // for(auto f : circuit_1_output){
    //     cout << f << ": " << support_set_size_1[f] << endl;
    // }
    // for(auto g : circuit_2_output){
    //     cout << g << ": " << support_set_size_2[g] << endl;
    // }
    output_solver();
    
    //===============================================================================================/

    // cout << "cir1 output num: " << circuit_1_number_of_outputs << endl;
    // cout << "cir2 output num: " << circuit_2_number_of_outputs << endl;

    // cout << "circuit_1_port_cnf_input_mapping: \n";
    // for(auto it : circuit_1_port_cnf_input_mapping){
    //     cout << it.first << " -> " << it.second << endl;
    // }
    // cout << "circuit_1_port_cnf_output_mapping: \n";
    // for(auto it : circuit_1_port_cnf_output_mapping){
    //     cout << it.first << " -> " << it.second << endl;
    // }
    // cout << "circuit_2_port_cnf_input_mapping: \n";
    // for(auto it : circuit_2_port_cnf_input_mapping){
    //     cout << it.first << " -> " << it.second << endl;
    // }
    // cout << "circuit_2_port_cnf_output_mapping: \n";
    // for(auto it : circuit_2_port_cnf_output_mapping){
    //     cout << it.first << " -> " << it.second << endl;
    // }

    // cout << "constraint1: " << endl;
    // for(auto it : constraint_1){
    //     cout << it << endl;
    // }
    // for(auto it = circuit1_function.begin(); it!=circuit1_function.end(); it++){
    //     cout << "CIRCUIT1: " <<"output: " << it->first << ", function: " << it->second << endl;
    // }
    // for(auto it = circuit2_function.begin(); it!=circuit2_function.end(); it++){
    //     cout << "CIRCUIT2: " << "output: " << it->first << ", function: " << it->second << endl;
    // }
    // for(auto it=circuit_1_aig_input_mapping.begin(); it!=circuit_1_aig_input_mapping.end(); it++){
    //     cout << "circuit_1_aig_input_mapping: " << it->first << " " << it->second << endl;
    // }
    // for(auto it=circuit_1_aig_output_mapping.begin(); it!=circuit_1_aig_output_mapping.end(); it++){
    //     cout << "circuit_1_aig_output_mapping: " << it->first << " " << it->second << endl;
    // }
    // for(auto it=circuit_2_aig_input_mapping.begin(); it!=circuit_2_aig_input_mapping.end(); it++){
    //     cout << "circuit_2_aig_input_mapping: " << it->first << " " << it->second << endl;
    // }
    // for(auto it=circuit_2_aig_output_mapping.begin(); it!=circuit_2_aig_output_mapping.end(); it++){
    //     cout << "circuit_2_aig_output_mapping: " << it->first << " " << it->second << endl;
    // }

    //test
    // ABC_Read(cir2_file_path);
    // sprintf( Command, "print_status -o");
    // Cmd_CommandExecute( pAbc, Command );
    // sprintf( Command, "dsd");
    // Cmd_CommandExecute( pAbc, Command );
    // // sprintf( Command, "print_auto");
    // // Cmd_CommandExecute( pAbc, Command );
    // sprintf( Command, "logic");
    // Cmd_CommandExecute( pAbc, Command );
    // sprintf( Command, "sop");
    // Cmd_CommandExecute( pAbc, Command );
    // // sprintf( Command, "print_auto");
    // // Cmd_CommandExecute( pAbc, Command );
    // ABC_Write("_pla", "test_2");
    // pCnfDat = Cnf_DataReadFromFile("circuit_2.cnf");
    // Cnf_DataPrint(pCnfDat, 1); 

    //prepare two ntk
    // aig_file[0] = "circuit_1.aig";
    // aig_file[1] = "circuit_2.aig";
    // Abc_NtkPrepareTwoNtks( fErr, pNtk2, aig_file, 2, &pNtk1, &pNtk2, &pfDelete1, &pfDelete2, 1);
    // cout << pNtk1 << " " << pNtk2 << endl;

    Abc_Stop();

    // current_time = clock();
    // cout << "TIME: " << double(current_time - start_time)/CLOCKS_PER_SEC << "s" << endl;
    cout << "TIME: " << t.GetElapsedMillseconds()/1000 << "sec" << endl;
    // construct_final_result_file(output_file_path, output_matching_result);

    return 0;
}