SRC = main.cpp \
      parseoptions.cpp \
      loop_summarizer.cpp \
      string_summarization.cpp \
      summary.cpp \
      string_utils.cpp \
      pointer_expr.cpp \
      value_set_duplication_adaptor.cpp \
      symex_assertion.cpp \
      replace_malloc.cpp \
      memstat.cpp \
      program_compression.cpp \
      conditional_goto_copy.cpp \
      invariant_propagation_adaptor.cpp \
      check_claims.cpp \
      local_slicer.cpp \
      localized_inlining.cpp \
      loopstore.cpp \
      leaping_goto_program.cpp \
      transform_loops.cpp \
      inlined_claims.cpp \
      summarization.cpp \
      value_set_alloc_adaptor.cpp \
      ../termination/replace_identifier.cpp \
      languages.cpp

OBJ = $(SRC:.cpp=$(OBJEXT)) \
      invariants/invariants.o \
      ../big-int/bigint$(OBJEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../ansi-c/ansi-c$(LIBEXT)

INCLUDES= -I ../$(CHAFF) -I .. -I ../util

LIBS =

include ../config.inc
include ../common

all: loopfrog$(EXEEXT)

ifdef MODULE_CPP
  OBJ += ../cpp/cpp$(LIBEXT)
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc$(LIBEXT)
endif

###############################################################################

.invariants:
	$(MAKE) $(MAKEARGS) -C invariants

loopfrog$(EXEEXT): .invariants $(OBJ)
	$(CXX) $(LINKFLAGS) -o $@ $(OBJ) $(LIBS)

clean:
	$(MAKE) $(MAKEARGS) -C invariants clean
	rm -f *.o loopfrog$(EXEEXT)
