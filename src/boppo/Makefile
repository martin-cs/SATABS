include ../config.inc
include ../common

SRC = main.cpp parseoptions.cpp convert_to_promela.cpp \
      formula.cpp program_formula.cpp convert_to_program_formula.cpp \
      simulator.cpp partial_order_reduction.cpp simulator_base.cpp \
      execute_thread.cpp history.cpp dump_trace.cpp solver.cpp \
      compute_trace.cpp synchronization.cpp compare_states.cpp \
      statistics.cpp state.cpp state_projection.cpp \
      slam_trace.cpp loop_detection.cpp qbf_cache.cpp \
      simulator_ct.cpp execute_thread_ct.cpp recurrence_check.cpp \
      simulator_ct_queue.cpp

OBJ+= $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/assembler/assembler$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/big-int/bigint$(OBJEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
      ../bplang/bplang$(LIBEXT)

INCLUDES= -I $(CBMC)/src -I $(CBMC)/src/util -I ..

LIBS =

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

all: boppo$(EXEEXT)

###############################################################################

boppo$(EXEEXT): $(OBJ)
	$(LINKBIN)

