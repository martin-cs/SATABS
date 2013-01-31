include ../config.inc
CBMC ?= ../..

SRC = satabs.cpp cmdline_options.cpp \
      satabs_safety_checker.cpp \
      \
      $(CBMC)/src/cbmc/xml_interface.cpp \
      \
      prepare/get_predicates.cpp \
      prepare/prepare.cpp \
      prepare/map_vars.cpp \
      prepare/concrete_model.cpp \
      prepare/languages.cpp \
      prepare/prepare_functions.cpp \
      prepare/satabs_inline.cpp \
      \
      refiner/add_invariants.cpp \
      refiner/substitute_invariants.cpp \
      refiner/refiner.cpp \
      refiner/refiner_wp.cpp \
      refiner/refiner_wp_async.cpp \
      refiner/refiner_lifter.cpp \
      refiner/transition_refiner.cpp \
      refiner/transition_cache.cpp \
      refiner/select_refiner.cpp \
      \
      modelchecker/modelchecker.cpp \
      \
      abstractor/predicates.cpp \
      abstractor/abstract_program.cpp \
      abstractor/abstractor.cpp \
      abstractor/abstractor_wp.cpp \
      abstractor/abstractor_wp_cartesian.cpp \
      abstractor/abstractor_satqe.cpp \
      abstractor/abstractor_prover.cpp \
      abstractor/check_redundancy.cpp \
      abstractor/discover_predicates.cpp \
      abstractor/canonicalize.cpp \
      abstractor/abstract_expression.cpp \
      abstractor/predabs_aux.cpp \
      abstractor/lift_if.cpp \
      abstractor/initial_abstraction.cpp \
      abstractor/abstract_dynamic_objects.cpp \
      abstractor/abstract_model.cpp \
      abstractor/select_abstractor.cpp \
      abstractor/concurrency_aware_abstract_transition_relation.cpp \
      abstractor/concurrency_aware_abstractor.cpp \
      abstractor/locations_of_expressions.cpp \
      \
      modelchecker/abstract_counterexample.cpp \
      modelchecker/abstract_state.cpp \
      modelchecker/tts_builder.cpp \
      modelchecker/modelchecker_boolean_program.cpp \
      modelchecker/select_modelchecker.cpp \
      modelchecker/modelchecker_smv.cpp \
      modelchecker/modelchecker_spin.cpp \
      \
      simulator/select_simulator.cpp \
      simulator/simulator_symex.cpp \
      simulator/concrete_counterexample.cpp \
      simulator/simulator_loop_detection.cpp \
      simulator/recurrence_solver.cpp \
      simulator/path_slicer.cpp

OBJ += \
      $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
      $(CBMC)/src/big-int/bigint$(OBJEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CBMC)/src/analyses/analyses$(LIBEXT) \
      $(CBMC)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      $(CBMC)/src/assembler/assembler$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/util/util$(LIBEXT)


include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CLEANFILES = satabs$(EXEEXT)

all: satabs$(EXEEXT)

ifneq ($(SQUOLEM2),)
CP_CXXFLAGS += -DHAVE_QBF_CORE
else
ifneq ($(CUDD),)
CP_CXXFLAGS += -DHAVE_QBF_CORE
endif
endif

INCLUDES= -I $(CBMC)/src -I $(CBMC)/src/util

#ifneq ($(wildcard ../prover/Makefile),)
#  CP_CXXFLAGS += -DHAVE_PROVER
#  OBJ += ../prover/prover$(LIBEXT)
#  SRC += abstractor/predicate_image_prover.cpp
#endif

#ifneq ($(wildcard ../ipp/Makefile),)
#  CP_CXXFLAGS += -DHAVE_IPP
#  OBJ += ../ipp/ipp$(LIBEXT)
#  SRC += refiner/refiner_ipp.cpp simulator/simulator_ipp.cpp
#endif

#ifneq ($(wildcard ../satqe/Makefile),)
#  CP_CXXFLAGS += -DHAVE_SATQE
#  SRC += abstractor/predicate_image_satqe.cpp
#  OBJ += ../satqe/satqe$(LIBEXT)
#endif

ifneq ($(wildcard $(CBMC)/src/cpp/Makefile),)
  OBJ += $(CBMC)/src/cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard $(CBMC)/src/specc/Makefile),)
  OBJ += $(CBMC)/src/specc/specc$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_SPECC
endif

###############################################################################

satabs$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: satabs-mac-signed

satabs-mac-signed: satabs$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) satabs$(EXEEXT)
	
