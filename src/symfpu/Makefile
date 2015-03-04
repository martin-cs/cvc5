CXXFLAGS+=-Wall -W -frounding-math -fsignaling-nans -ffp-contract=off -msse2 -mfpmath=sse -pedantic
SUBDIRS=applications/ utils/ baseTypes/ core/
OBJECTFILES=utils/common.o baseTypes/simpleExecutable.o core/nondet.o
LIBFILES=symfpu.a
PROGS=test cbmcverification


.PHONY: all subdirs $(SUBDIRS) clean $(PROGS)

all : subdirs $(LIBFILES) $(PROGS)

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

symfpu.a : $(OBJECTFILES)
	ar rcs $@ $^

clean :
	find . -name '*.o' -exec rm {} \;
	rm -f $(LIBFILES) $(PROGS)

test : applications/test.o $(LIBFILES)
	$(CXX) $(CXXFLAGS) $^ -o $@

cbmcverification : applications/cbmcverification.o $(LIBFILES)
	$(CXX) $(CXXFLAGS) $^ -o $@



