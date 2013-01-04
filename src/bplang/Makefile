include ../config.inc
include ../common

SRC = bp_language.cpp bp_parser.cpp bp_typecheck.cpp expr2bp.cpp \
      y.tab.cpp lex.yy.cpp bp_parse_tree.cpp bp_typecheck_code.cpp \
      bp_typecheck_expr.cpp bp_util.cpp

INCLUDES= -I $(CBMC)/src -I $(CBMC)/src/util

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CLEANFILES = bplang$(LIBEXT) \
	y.tab.h y.tab.cpp lex.yy.cpp \
	y.tab.cpp.output y.output

all: bplang$(LIBEXT)

###############################################################################

bplang$(LIBEXT): $(OBJ)
	$(LINKLIB)

y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyybp -d parser.y -o y.tab.cpp

y.tab.h: y.tab.cpp
	if [ -e y.tab.hpp ] ; then mv y.tab.hpp y.tab.h ; else \
        mv y.tab.cpp.h y.tab.h ; fi

lex.yy.cpp: scanner.l
	$(LEX) -Pyybp -olex.yy.cpp scanner.l

# extra dependencies
y.tab$(OBJEXT): y.tab.cpp y.tab.h
lex.yy$(OBJEXT): y.tab.cpp lex.yy.cpp y.tab.h

