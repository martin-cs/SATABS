include ../config.inc
include ../common

SRC = main.cpp \
      tan_parseoptions.cpp \
      tan_languages.cpp

OBJ = $(SRC:.cpp=.o) \
      $(CBMC)/src/big-int/big-int$(LIBEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/assembler/assembler$(LIBEXT) \
      $(CBMC)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CBMC)/src/analyses/analyses$(LIBEXT) \
      $(CBMC)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/path-symex/path-symex$(LIBEXT) \
      $(CBMC)/src/util/util$(LIBEXT) \
      ../termination/termination$(LIBEXT) \
      \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/cpp/cpp$(LIBEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
			$(CBMC)/src/goto-instrument/reachability_slicer$(OBJEXT) \
      \
      ../satabs/cmdline_options.o \
      ../satabs/satabs_safety_checker.o \
      ../satabs/prepare/*.o \
      ../satabs/refiner/*.o \
      ../satabs/modelchecker/*.o \
      ../satabs/abstractor/*.o \
      ../satabs/simulator/*.o

INCLUDES= -I $(CBMC)/src -I ../

LIBS =

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

all: tan$(EXEEXT)

###############################################################################

tan$(EXEEXT): $(OBJ)
	$(LINKBIN)
