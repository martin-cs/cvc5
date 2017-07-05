include ../flags
CXXFLAGS+=-I../
ALL=simpleExecutable.o print.o

.PHONY : all

all : $(ALL)

%.o : %.cpp
	$(CXX) $(CXXFLAGS) -c $^ -o $@

