CSOURCES = aiger.c picosat/picosat.c

CPPSOURCES = checker.cpp carsolver.cpp mainsolver.cpp model.cpp utility.cpp data_structure.cpp main.cpp \
	minisat/core/Solver.cc minisat/utils/Options.cc minisat/utils/System.cc
#CSOURCES = aiger.c picosat/picosat.c
#CPPSOURCES = bfschecker.cpp checker.cpp carsolver.cpp mainsolver.cpp model.cpp utility.cpp data_structure.cpp main.cpp \
	glucose/core/Solver.cc glucose/utils/Options.cc glucose/utils/System.cc

OBJS = checker.o carsolver.o mainsolver.o model.o main.o utility.o data_structure.o aiger.o\
	Solver.o Options.o System.o picosat.o

CFLAG = -I../ -I./minisat -D__STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -c -g -fpermissive -O3
#CFLAG = -I../ -I./glucose -D__STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -c -g 

LFLAG = -g -lz -lpthread 

GCC = gcc

GXX = g++

simplecar: $(CSOURCES) $(CPPSOURCES)
	$(GCC) $(CFLAG) $(CSOURCES)
	$(GCC) $(CFLAG) -std=c++11 $(CPPSOURCES)
	$(GXX) -o simplecar $(OBJS) $(LFLAG)
	rm *.o

picosat: $(CSOURCES) $(CPPSOURCES)
	$(GCC) $(CFLAG) $(CSOURCES)
	$(GCC) $(CFLAG) -D ENABLE_PICOSAT -std=c++11 $(CPPSOURCES)
	$(GXX) -o simplecar $(OBJS) $(LFLAG)
	rm *.o


clean: 
	rm simplecar
	
.PHONY: simplecar
