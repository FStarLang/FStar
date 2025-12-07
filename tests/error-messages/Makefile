FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

# This so that we don't get warnings about:
# 241: "unable to load checked file"
# 247: "checked file was not written"
# 333: "unable to read hints"
OTHERFLAGS+=--warn_error -241-247-333-274+240

# Remove --query_stats and --hint_info from this subdir, since
# they output timing info.
OTHERFLAGS := $(filter-out --query_stats, $(OTHERFLAGS))
OTHERFLAGS := $(filter-out --hint_info, $(OTHERFLAGS))
OTHERFLAGS += --ext fstar:no_absolute_paths
OTHERFLAGS += --ext fly_deps

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
$(OUTPUT_DIR)/InfixImps.fst.json_output: OTHERFLAGS+=--dump_module InfixImps --print_implicits
$(OUTPUT_DIR)/InfixImps.fst.output     : OTHERFLAGS+=--dump_module InfixImps --print_implicits
