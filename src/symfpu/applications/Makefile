include ../flags
CXXFLAGS+=-I../
ALL=test.o cbmcverification.o generate.o

.PHONY : all

all : $(ALL)

%.o : %.cpp
	$(CXX) $(CXXFLAGS) -c $^ -o $@

