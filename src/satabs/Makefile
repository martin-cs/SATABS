SRC = satabs.cpp cmdline_options.cpp cegar_loop.cpp \
      safety.cpp satabs_safety_checker.cpp check_redundancy.cpp \
      \
      ../cbmc/xml_interface.cpp \
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

OBJ = $(SRC:.cpp=$(OBJEXT)) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../big-int/bigint$(OBJEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../intrep/intrep$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../smvlang/smvlang$(LIBEXT) \
      ../bplang/bplang$(LIBEXT) \
      ../promela/promela$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../langapi/langapi$(LIBEXT)

LIBS =

include ../config.inc
include ../common

all: satabs$(EXEEXT)

ifneq ($(SQUOLEM2),)
CXXFLAGS += -DHAVE_QBF_CORE
else
ifneq ($(CUDD),)
CXXFLAGS += -DHAVE_QBF_CORE
endif
endif

INCLUDES= -I .. -I ../util

ifdef MODULE_PROVER
  CXXFLAGS += -DHAVE_PROVER
  OBJ += ../prover/prover$(LIBEXT)
  SRC += abstractor/predicate_image_prover.cpp
endif

ifdef MODULE_IPP
  CXXFLAGS += -DHAVE_IPP
  OBJ += ../ipp/ipp$(LIBEXT)
  SRC += refiner/refiner_ipp.cpp simulator/simulator_ipp.cpp
endif

ifdef MODULE_SATQE
  CXXFLAGS += -DHAVE_SATQE
  SRC += abstractor/predicate_image_satqe.cpp
  OBJ += ../satqe/satqe.a
endif

ifdef MODULE_CPP
  OBJ += ../cpp/cpp$(LIBEXT)
  CXXFLAGS += -DHAVE_CPP
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc$(LIBEXT)
  CXXFLAGS += -DHAVE_SPECC
endif

ifdef MODULE_PHP
  OBJ += ../php/php$(LIBEXT)
  CXXFLAGS += -DHAVE_PHP
endif

ifdef MODULE_QBF_CORE
  CXXFLAGS += -DQBF_CORE
endif

###############################################################################

satabs$(EXEEXT): $(OBJ)
	$(CXX) $(LINKFLAGS) -o $@ $(OBJ) $(LIBS) 

clean:
	rm -f $(SRC:.cpp=$(OBJEXT)) satabs$(EXEEXT)
