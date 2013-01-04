SRC = main.cpp parseoptions.cpp convert_to_promela.cpp \
      formula.cpp program_formula.cpp convert_to_program_formula.cpp \
      simulator.cpp partial_order_reduction.cpp simulator_base.cpp \
      execute_thread.cpp history.cpp dump_trace.cpp solver.cpp \
      compute_trace.cpp synchronization.cpp compare_states.cpp \
      statistics.cpp state.cpp state_projection.cpp \
      slam_trace.cpp loop_detection.cpp qbf_cache.cpp \
      simulator_ct.cpp execute_thread_ct.cpp recurrence_check.cpp \
      simulator_ct_queue.cpp

OBJ+= ../util/util$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../big-int/bigint$(OBJEXT) \
      ../bplang/bplang$(LIBEXT) \
      ../linking/linking$(LIBEXT)

INCLUDES= -I .. -I ../util

LIBS =

include ../config.inc
include ../common

all: boppo$(EXEEXT)

###############################################################################

boppo$(EXEEXT): $(OBJ)
	$(LINKBIN)

