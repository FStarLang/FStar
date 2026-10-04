FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

# This so that we don't get warnings about:
# 241: "unable to load checked file"
# 247: "checked file was not written"
# 333: "unable to read hints"
OTHERFLAGS+=--warn_error -241-247-333-274+240

# Remove --query_stats from this subdir, since
# they output timing info.
OTHERFLAGS := $(filter-out --query_stats, $(OTHERFLAGS))
OTHERFLAGS += --ext fstar:no_absolute_paths

# For these tests, we check that the resugared output
# matches the expected file. We have to repeat the lines for
# json_output, sadly.
$(OUTPUT_DIR)/Bug1997.fst.json_output  : OTHERFLAGS+=--dump_module Bug1997
$(OUTPUT_DIR)/Bug1997.fst.output       : OTHERFLAGS+=--dump_module Bug1997
$(OUTPUT_DIR)/Bug2820.fst.json_output  : OTHERFLAGS+=--dump_module Bug2820
$(OUTPUT_DIR)/Bug2820.fst.output       : OTHERFLAGS+=--dump_module Bug2820
$(OUTPUT_DIR)/Bug3145.fst.json_output  : OTHERFLAGS+=--dump_module Bug3145
$(OUTPUT_DIR)/Bug3145.fst.output       : OTHERFLAGS+=--dump_module Bug3145
$(OUTPUT_DIR)/Bug3227.fst.json_output  : OTHERFLAGS+=--dump_module Bug3227
$(OUTPUT_DIR)/Bug3227.fst.output       : OTHERFLAGS+=--dump_module Bug3227
$(OUTPUT_DIR)/Bug3292.fst.json_output  : OTHERFLAGS+=--dump_module Bug3292
$(OUTPUT_DIR)/Bug3292.fst.output       : OTHERFLAGS+=--dump_module Bug3292
$(OUTPUT_DIR)/Bug3530.fst.json_output  : OTHERFLAGS+=--dump_module Bug3530
$(OUTPUT_DIR)/Bug3530.fst.output       : OTHERFLAGS+=--dump_module Bug3530
$(OUTPUT_DIR)/CalcImpl.fst.json_output : OTHERFLAGS+=--dump_module CalcImpl
$(OUTPUT_DIR)/CalcImpl.fst.output      : OTHERFLAGS+=--dump_module CalcImpl
$(OUTPUT_DIR)/DTuples.fst.json_output  : OTHERFLAGS+=--dump_module DTuples
$(OUTPUT_DIR)/DTuples.fst.output       : OTHERFLAGS+=--dump_module DTuples
$(OUTPUT_DIR)/SeqLit.fst.json_output   : OTHERFLAGS+=--dump_module SeqLit
$(OUTPUT_DIR)/SeqLit.fst.output        : OTHERFLAGS+=--dump_module SeqLit
$(OUTPUT_DIR)/PatImps.fst.json_output  : OTHERFLAGS+=--dump_module PatImps
$(OUTPUT_DIR)/PatImps.fst.output       : OTHERFLAGS+=--dump_module PatImps
$(OUTPUT_DIR)/TuplePat.fst.json_output : OTHERFLAGS+=--dump_module TuplePat
$(OUTPUT_DIR)/TuplePat.fst.output      : OTHERFLAGS+=--dump_module TuplePat
$(OUTPUT_DIR)/Monoid.fst.json_output   : OTHERFLAGS+=--dump_module Monoid
$(OUTPUT_DIR)/Monoid.fst.output        : OTHERFLAGS+=--dump_module Monoid
# These two dump the module after type checking, which is phase 2's
# elaboration: with --ext phase2_core, phase 1's, which lacks the result
# ascriptions TcTerm puts on matches (TuplePat) and uses fewer fresh names
# (Monoid). See doc/ref/phase2_core.md.
$(OUTPUT_DIR)/TuplePat.fst.json_output : OTHERFLAGS+=--ext phase2_core=off
$(OUTPUT_DIR)/TuplePat.fst.output      : OTHERFLAGS+=--ext phase2_core=off
$(OUTPUT_DIR)/Monoid.fst.json_output   : OTHERFLAGS+=--ext phase2_core=off
$(OUTPUT_DIR)/Monoid.fst.output        : OTHERFLAGS+=--ext phase2_core=off
$(OUTPUT_DIR)/InfixImps.fst.json_output: OTHERFLAGS+=--dump_module InfixImps --print_implicits
$(OUTPUT_DIR)/InfixImps.fst.output     : OTHERFLAGS+=--dump_module InfixImps --print_implicits
# With --ext phase2_core, Core's VCs are not TcTerm's, so for these the
# failures reported (though as precise) differ from the expected output.
# See doc/ref/phase2_core.md, "Error reporting".
# - ShortCircuiting, Coercions: Core's VC carries more facts, e.g. the
#   refinement of [bad (x-1)], or the definition [f = fun n -> n], and so
#   they are in the context of a failed goal;
# - Test.FunctionalExtensionality: Core relates two applications by
#   unfolding or argument-wise, and a failure reports the disjunction;
# - PatAnnot: Core reports the failed annotation of a pattern binder as a
#   subtyping failure at the binder, not as a failed assertion;
# - Calc: the obligation of a proof step is located at the step;
# - TestErrorLocations: in test_elim_exists, Core proves the assertion
#   from the postcondition of indefinite_description1, so only its
#   precondition fails.
PHASE2_CORE_OFF := NegativeTests.ShortCircuiting Coercions Test.FunctionalExtensionality PatAnnot Calc TestErrorLocations
$(foreach m,$(PHASE2_CORE_OFF),$(eval $(OUTPUT_DIR)/$(m).fst.output      : OTHERFLAGS+=--ext phase2_core=off))
$(foreach m,$(PHASE2_CORE_OFF),$(eval $(OUTPUT_DIR)/$(m).fst.json_output : OTHERFLAGS+=--ext phase2_core=off))
$(foreach m,$(PHASE2_CORE_OFF),$(eval $(CACHE_DIR)/$(m).fst.checked      : OTHERFLAGS+=--ext phase2_core=off))
