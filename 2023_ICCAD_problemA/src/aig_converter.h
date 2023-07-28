#include <iostream>
#include <cstdlib>
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <cstring>
#include <sstream>
#include "utility.h"

using namespace std;

extern long long int circuit_1_number_of_outputs, circuit_2_number_of_outputs;
extern long long int circuit_1_number_of_inputs, circuit_2_number_of_inputs;

extern int aig_to_pos(fstream * AIG_file, fstream * IO_file, int cir);