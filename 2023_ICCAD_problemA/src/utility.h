#include <iostream>
#include <string>
#include <fstream>
#include <vector>
#include <cstring>
#include <unordered_map>
#include <map>
#include <set>
#include <ctime>
#include "timer.h"
// #include "../lib/sequential-solvers/CaDiCaL_DVDL_V1/build/cadical/src/cadical.hpp"
#include "cadical.hpp"

using namespace std;

// ifstream* readFile(string fileName);
// ofstream* writeFile();
extern Timer t;
extern int var;


// extern int aigtoaig_api(int argc, char **argv);

extern void get_support_set(string file_name, int cir);
extern void aig_to_cnf_number(string file_name, int cir);
extern pair<string, string> add_input_matching_clause(string a, string b);
extern void get_cnf_file_record(string file_name, int cir);
extern void cnf_file_combine(string combine_filename);
extern void cnf_file_combine2(string combine_filename);
extern void construct_output_pair_table();
extern void construct_input_pair_table();
extern void construct_input_pair_matrix();
extern void construct_constraint_1();
extern void construct_constraint_1_matrix_version();
extern void construct_constraint_2(vector<pair<bool, pair<string, string>>> output_matching_result);
extern void construct_constraint_3();
extern void construct_constraint_4(vector<pair<bool, pair<string, string>>> output_matching_result);
extern void construct_constraint_5();
extern int MiniSAT(string SAT_input_file, string SAT_output_file);
extern bool CaDiCaL_Solver(string file, CaDiCaL::Solver& solver);
extern bool solve_mapping(vector<pair<bool, pair<string, string>>> output_matching_result);
extern void construct_learned_clauses(vector<pair<bool, pair<string, string>>> output_matching_result);
extern bool solve_miter(vector<pair<bool, pair<string, string>>> output_matching_result);
extern void construct_final_result_file(string file_name, vector<pair<bool, pair<string, string>>> output_matching_result);
extern fstream *solve_mapping_file, *solve_miter_file;
extern vector<bool> solve_mapping_file_result_record, solve_miter_file_result_record;
extern string input_file_path, output_file_path, cir1_file_path, cir2_file_path;

extern unordered_map<string, string> circuit1_function, circuit2_function;
extern fstream * mapping_file;
extern clock_t start_time, current_time;
// extern std::chrono::steady_clock::time_point start_time_2, current_time_2;

extern vector<pair<long long int, string>> circuit_1_structural_support_set_size, circuit_2_structural_support_set_size;
extern unordered_map<string, long long int> structural_support_set_size_1, structural_support_set_size_2;
extern unordered_map<string, vector<string>> circuit_1_structural_support_set, circuit_2_structural_support_set;
extern vector<pair<long long int, string>> circuit_1_functional_support_set_size, circuit_2_functional_support_set_size;
extern unordered_map<string, long long int> functional_support_set_size_1, functional_support_set_size_2;
extern unordered_map<string, vector<string>> circuit_1_functional_support_set, circuit_2_functional_support_set;
extern vector<pair<pair<long long int, long long int>, string>> circuit_1_support_set_size, circuit_2_support_set_size;

extern long long int circuit_1_number_of_outputs, circuit_2_number_of_outputs;
extern long long int circuit_1_number_of_inputs, circuit_2_number_of_inputs;

extern vector<pair<string, long long int>> circuit_1_used_input, circuit_1_unused_input;
extern vector<pair<string, long long int>> circuit_2_used_input, circuit_2_unused_input;
extern vector<pair<string, long long int>> circuit_1_used_output, circuit_1_unused_output;
extern vector<pair<string, long long int>> circuit_2_used_output, circuit_2_unused_output;
extern vector<string> circuit_1_input, circuit_2_input;
extern vector<string> circuit_1_output, circuit_2_output;

//aig -> cnf number mapping
extern unordered_map<string, string> circuit_1_aig_cnf_mapping, circuit_1_aig_cnf_input_mapping, circuit_1_aig_cnf_output_mapping;
extern unordered_map<string, string> circuit_2_aig_cnf_mapping, circuit_2_aig_cnf_input_mapping, circuit_2_aig_cnf_output_mapping;

//port string -> cnf number mapping
extern unordered_map<string, string> circuit_1_port_cnf_input_mapping, circuit_1_port_cnf_output_mapping;
extern unordered_map<string, string> circuit_2_port_cnf_input_mapping, circuit_2_port_cnf_output_mapping;
//cnf -> port string number mapping
extern unordered_map<string, string> circuit_1_cnf_port_input_mapping, circuit_1_cnf_port_output_mapping;
extern unordered_map<string, string> circuit_2_cnf_port_input_mapping, circuit_2_cnf_port_output_mapping;
//port -> id
extern unordered_map<string, long long int> circuit_1_port_id_input_mapping, circuit_2_port_id_input_mapping;
extern unordered_map<string, long long int> circuit_1_port_id_output_mapping, circuit_2_port_id_output_mapping;


//matrix table
extern long long int input_table_number_start, input_table_number_end;
extern map<pair<string, string>, string> input_pair_table;
extern long long int output_table_number_start, output_table_number_end;
extern map<pair<string, string>, string> output_pair_table;
extern string ** input_pair_matrix;

//equal set: definition 4 of 2-step search engine
extern vector<vector<string>> circuit_1_equal, circuit_2_equal;

//output group
extern vector<vector<string>> circuit_1_output_group, circuit_2_output_group;

//constraint
extern vector<string> constraint_1;
extern long long int constraint_1_start, constraint_1_end;
extern vector<string> constraint_1;
extern long long int constraint_2_start, constraint_2_end;
extern vector<string> constraint_2;
extern long long int constraint_3_start, constraint_3_end;
extern vector<string> constraint_3;
extern vector<vector<string>> constraint_4;

//learned clause
extern vector<vector<string>> learned_clause;

//output matching result R
extern vector<pair<bool, pair<string, string>>> output_matching_result;

//cnf file
typedef struct cnf_file cnf_file;
extern cnf_file circuit1_cnf, circuit2_cnf, total_cnf;
extern vector<string> circuit1_cnf_clauses, circuit2_cnf_clauses;
extern long long int circuit1_cnf_number_of_variables, circuit2_cnf_number_of_variables;
extern long long int circuit1_cnf_number_of_clauses, circuit2_cnf_number_of_clauses;

extern long long int output_port_replace_index;
extern long long int output_port_replace_index_start, output_port_replace_index_end;

//bus
extern vector<pair<long long int, vector<string>>> cir1_bus_set, cir2_bus_set;
extern map<pair<string, string>, string> bus_pair_table;
extern unordered_map<string, bool> circuit_1_is_input, circuit_2_is_input;
extern vector<pair<long long int, vector<string>>> cir1_input_bus_set, cir2_input_bus_set;
extern vector<pair<long long int, vector<string>>> cir1_output_bus_set, cir2_output_bus_set;

//buffer
extern unordered_map<string, bool> buffer_phase;
extern vector<string> circuit_1_zero_support, circuit_2_zero_support;

//input support
extern unordered_map<string, long long int> circuit_1_input_support_size, circuit_2_input_support_size;

#if defined(ABC_NAMESPACE)
namespace ABC_NAMESPACE
{
#elif defined(__cplusplus)
extern "C"
{
#endif

// procedures to start and stop the ABC framework
// (should be called before and after the ABC procedures are called)
void   Abc_Start();
void   Abc_Stop();

// procedures to get the ABC framework and execute commands in it
typedef struct Abc_Frame_t_ Abc_Frame_t;
typedef struct Abc_Ntk_t Abc_Ntk_t;
typedef struct Abc_Obj_t Abc_Obj_t;
typedef struct Cnf_Man_t_            Cnf_Man_t;
typedef struct Cnf_Dat_t_            Cnf_Dat_t;
typedef struct Cnf_Cut_t_            Cnf_Cut_t;
typedef struct Gia_Man_t_ Gia_Man_t;

Abc_Frame_t * Abc_FrameGetGlobalFrame();
Abc_Ntk_t * Abc_FrameReadNtk(Abc_Frame_t * p);
void Abc_NtkPrintIo( FILE * pFile, Abc_Ntk_t * pNtk, int fPrintFlops );
// inline Abc_Obj_t * Abc_NtkPi( Abc_Ntk_t * pNtk, int i );
// inline int Abc_NtkPoNum( Abc_Ntk_t * pNtk );
// inline Abc_Obj_t * Abc_NtkPo( Abc_Ntk_t * pNtk, int i );
// inline int Abc_NtkPiNum( Abc_Ntk_t * pNtk );
int Cmd_CommandExecute( Abc_Frame_t * pAbc, const char * sCommand );
char *  Abc_ObjName( Abc_Obj_t * pNode );
void Abc_NtkPrintStrSupports( Abc_Ntk_t * pNtk, int fMatrix , FILE* file);
void            Cnf_ManPrepare();
Cnf_Man_t *     Cnf_ManRead();
void            Cnf_ManFree();
Cnf_Dat_t *     Cnf_DataReadFromFile( char * pFileName );
void            Cnf_DataPrint( Cnf_Dat_t * p, int fReadable );
int      Abc_NtkPrepareTwoNtks( FILE * pErr, Abc_Ntk_t * pNtk, char ** argv, int argc, Abc_Ntk_t ** ppNtk1, Abc_Ntk_t ** ppNtk2, int * pfDelete1, int * pfDelete2, int fCheck );
void     Abc_FrameReplaceCurrentNetwork( Abc_Frame_t * p, Abc_Ntk_t * pNet );
void     Abc_NtkOrderObjsByName( Abc_Ntk_t * pNtk, int fComb );
Gia_Man_t *        Abc_NtkAigToGia( Abc_Ntk_t * p, int fGiaSimple );
#if defined(ABC_NAMESPACE)
}
using namespace ABC_NAMESPACE;
#elif defined(__cplusplus)
}
#endif
extern Abc_Frame_t * pAbc;
extern Abc_Ntk_t * pNtk1, * pNtk2;
extern Abc_Obj_t * pObj;
extern Cnf_Dat_t * pCnfDat;
extern Cnf_Man_t_ * pCnfMan;
extern Cnf_Cut_t_ * pCnfCut;
extern Gia_Man_t * pGiaMan;
// extern Abc_Ntk_t * Abc_FrameReadNtk( Abc_Frame_t * p );
// extern void Abc_NtkPrintIo( FILE * pFile, Abc_Ntk_t * pNtk, int fPrintFlops );


