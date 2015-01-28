include ../flags
CXXFLAGS+=-I../
ALL=nondet.o
.PHONY : all

all : $(ALL)

%.o : %.cpp
	$(CXX) $(CXXFLAGS) -c $^ -o $@

