include ../config.inc
include ../common

SRC = find_symbols_rw.cpp instrumentation.cpp rankfunction_typecheck.cpp \
      ranking_base.cpp ranking.cpp ranking_qbf_bitwise.cpp \
      ranking_qbf_complete.cpp ranking_qbf.cpp ranking_rankfinder.cpp \
      ranking_sat.cpp ranking_seneschal.cpp ranking_tools.cpp \
      replace_identifier.cpp termination_base.cpp termination_bre.cpp \
      termination_main.cpp termination_cta.cpp termination_slicer.cpp \
      ranking_relation_cache.cpp termination_direct.cpp \
      termination_path_enumeration.cpp ranking_smt.cpp \
      expr2seneschal.cpp transform_loops.cpp

ifdef MODULE_INTERPOLATION
SRC += termination_ita.cpp
endif

ifdef MODULE_INTERPOLATION
OBJ += ../ivt/symex_wolver.o ../ivt/wolver.o ../ivt/wolver_slice.o ../ivt/program_unwinding.o ../ivt/select_interpolator.o ../ivt/wolver_interpolator.o ../ivt/princess_interpolator.o ../ivt/princess_interface.o ../ivt/princess_dec.o ../ivt/piped_process.o ../ivt/interpolator/interpolator.o
CXXFLAGS += -DHAVE_INTERPOLATION
endif

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src -I $(CBMC)/src/util -I ../

all: termination$(LIBEXT)

ifneq ($(SQUOLEM2),)
  CXXFLAGS += -DHAVE_QBF_CORE
else
ifneq ($(CUDD),)
  CXXFLAGS += -DHAVE_QBF_CORE
endif
endif

###############################################################################

termination$(LIBEXT): $(OBJ)
	$(LINKLIB)

