AM_CPPFLAGS = \
	-D__BUILDING_CVC4LIB \
	-I@builddir@/../.. -I@srcdir@/../../include -I@srcdir@/../..
AM_CXXFLAGS = -Wall -Wno-unknown-pragmas $(FLAG_VISIBILITY_HIDDEN)

noinst_LTLIBRARIES = libfp.la

libfp_la_SOURCES = \
	theory_fp.h \
	theory_fp.cpp \
	theory_fp_rewriter.h \
	theory_fp_rewriter.cpp \
	theory_fp_type_rules.h \
	trp_integration.h \
	trp_integration.cpp

EXTRA_DIST = \
	kinds \
	options_handlers.h
