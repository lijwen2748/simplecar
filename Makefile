#SOURCES = aiger.c checker.cpp carsolver.cpp mainsolver.cpp model.cpp utility.cpp data_structure.cpp main.cpp \
#	minisat/core/Solver.cc minisat/utils/Options.cc minisat/utils/System.cc
SOURCES = aiger.c checker.cpp carsolver.cpp mainsolver.cpp model.cpp utility.cpp data_structure.cpp main.cpp \
	glucose/core/Solver.cc glucose/utils/Options.cc glucose/utils/System.cc

OBJS = checker.o carsolver.o mainsolver.o model.o main.o utility.o data_structure.o aiger.o\
	Solver.o Options.o System.o

#CFLAG = -I../ -I./minisat -D__STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -c -g 
CFLAG = -I../ -I./glucose -D__STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -c -g 

LFLAG = -g -lz -lpthread 

GCC = gcc

GXX = g++

simplecar: $(SOURCES)
	$(GCC) $(CFLAG) $(SOURCES)
	$(GXX) -o simplecar $(OBJS) $(LFLAG)
	rm *.o

clean: 
	rm simplecar
	
.PHONY: simplecar
