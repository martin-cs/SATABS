include ../config.inc
include ../common

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
      languages.cpp \
      invariants/invariant_test.cpp \
      invariants/zero_termination.cpp \
      invariants/iterator_bounds.cpp \
      invariants/iterator_bounds2.cpp \
      invariants/string_length.cpp \
      invariants/null_pointer.cpp \
      invariants/pointer_offset.cpp \
      invariants/constant_tracker.cpp \
      invariants/pointer_object.cpp \
      invariants/strong_bounds.cpp \
      invariants/decreasing_length.cpp \
      invariants/equalities.cpp \
      invariants/inequalities.cpp \
      invariants/disequalities.cpp  \
      invariants/variable_relations_base.cpp \
      invariants/ti_less_greater_all.cpp \
      invariants/ti_less_greater_numeric.cpp \
      invariants/ti_or_less_greater_all.cpp \
      invariants/ti_max_less_greater.cpp \
      invariants/ti_sum_less_greater.cpp \
      invariants/sti_gzero_implies_less_greater_all.cpp \
      invariants/sti_gzero_implies_or_less_greater_all.cpp 

OBJ = $(SRC:.cpp=$(OBJEXT)) \
      $(CBMC)/src/big-int/bigint$(OBJEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CBMC)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CBMC)/src/analyses/analyses$(LIBEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
      $(CBMC)/src/assembler/assembler$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/ansi-c/ansi-c$(LIBEXT)

INCLUDES= -I $(CBMC)/src -I $(CBMC)/src/util

LIBS =

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

all: loopfrog$(EXEEXT)

###############################################################################

loopfrog$(EXEEXT): $(OBJ)
	$(LINKBIN)

