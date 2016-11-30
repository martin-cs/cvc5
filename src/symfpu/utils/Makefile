include ../flags
CXXFLAGS+=-I../
ALL=common.o
.PHONY : all

all : $(ALL)

%.o : %.cpp
	$(CXX) $(CXXFLAGS) -c $^ -o $@

