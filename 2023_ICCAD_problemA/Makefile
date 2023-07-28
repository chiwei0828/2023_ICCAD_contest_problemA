CC := g++
#CC := clang
exe := main
CFLAGS := -std=c++17 -O2 -Wall -Wextra -fsanitize=undefined -fsanitize=address 
LINK := -lm -ldl -lreadline -lpthread
LIB := lib/libabc.a
CAD_LIB := lib/libcadical.a
SAT := lib/libkissat.a
src_dir = ./src
obj_dir = ./obj
CADICAL_DIR := /lib/sequential-solvers/CaDiCaL_DVDL_V1/build/cadical
INC_FLAGS = -I$(CADICAL_DIR)/src
LIB_FLAGS = -L$(CADICAL_DIR)/build -lcadical

src = $(wildcard $(src_dir)/*.cpp)
obj = $(patsubst $(src_dir)/%.cpp, $(obj_dir)/%.o, $(src))

all:$(obj) $(LIB) lib/libcadical.a
	mkdir -p $(obj_dir)
	$(CC) $(CFLAGS) -o $(exe) $(obj) ./obj/aiger.o $(LIB) lib/libcadical.a $(LINK)
#	cd ./lib/yosys && make config-gcc && make
#   cd ./lib/sequential-solvers/Kissat_MAB-HyWalk && ./configure && make kissat
#	cd ./lib/aiger  && ./configure.sh && make
#   cd ./lib/SAT-Solver && make
# rm -rf circuit_1_aigs
# rm -rf circuit_2_aigs
# mkdir circuit_1_aigs
# mkdir circuit_2_aigs

# rm -rf circuit_1_cnfs
# rm -rf circuit_2_cnfs
# mkdir circuit_1_cnfs
# mkdir circuit_2_cnfs

$(obj_dir)/%.o: $(src_dir)/%.cpp
	$(CC) $(CFLAGS) -c $< -o $@


lib/libabc.a:
	cd lib/abc/ && make -j 20 libabc.a
	mv lib/abc/libabc.a lib/


# lib/libkissat.a:
# 	cd ./lib/sequential-solvers/Kissat_MAB-HyWalk/build/ && make libkissat.a
# 	mv	lib/sequential-solvers/Kissat_MAB-HyWalk/build/libkissat.a lib/

clean:remove
	rm -rf $(obj) $(exe)
	rm -rf ./lib/libabc.a
remove:
	rm -f nCir* output-*