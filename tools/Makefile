# Update the paths below according to your directory structure
HCMPATH=..
MINISAT=../minisat

# required for adding code of minisat to your program
MINISAT_OBJS=$(MINISAT)/core/Solver.o $(MINISAT)/utils/Options.o $(MINISAT)/utils/System.o

CXXFLAGS=-ggdb -O0 -fPIC -I$(HCMPATH)/include -I$(MINISAT)
CFLAGS=-ggdb -O0 -fPIC -I$(HCMPATH)/include -I$(MINISAT)
CC=g++
LDFLAGS= $(MINISAT_OBJS) -L$(HCMPATH)/src -lhcm -Wl,-rpath=$(HCMPATH)/src 

all: minisat_api_example

minisat_api_example: minisat_api_example.o 
	g++ -o $@ $^ $(LDFLAGS)

main.o: minisat_api_example.cpp

clean: 
	@ rm *.o minisat_api_example
