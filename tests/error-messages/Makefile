FSTAR_HOME=../..
all: check-all

FSTAR_FILES=$(wildcard *.fst)

# This so that we don't get warnings about:
# 241: "unable to load checked file"
# 247: "checked file was not written"
# 333: "unable to read hints"
OTHERFLAGS+=--warn_error -241-247-333-274+240

# Sorry, without this we can get noise in error locations.
# See issue #1993. Also, warnings from dependencies would
# pollute the output.
OTHERFLAGS+=--already_cached 'Prims FStar'

# Remove --query_stats and --hint_info from this subdir, since
# they output timing info.
OTHERFLAGS := $(filter-out --query_stats, $(OTHERFLAGS))
OTHERFLAGS := $(filter-out --hint_info, $(OTHERFLAGS))
OTHERFLAGS += --ext fstar:no_absolute_paths

check-all: $(addsuffix .human_check, $(FSTAR_FILES)) \
           $(addsuffix .json_check, $(FSTAR_FILES))

# For these tests, we check that the resugared output
# matches the expected file. We have to repeat the lines for
# json_output, sadly.
Bug1997.fst.json_output  : OTHERFLAGS+=--dump_module Bug1997
Bug1997.fst.output       : OTHERFLAGS+=--dump_module Bug1997
Bug2820.fst.json_output  : OTHERFLAGS+=--dump_module Bug2820
Bug2820.fst.output       : OTHERFLAGS+=--dump_module Bug2820
Bug3145.fst.json_output  : OTHERFLAGS+=--dump_module Bug3145
Bug3145.fst.output       : OTHERFLAGS+=--dump_module Bug3145
Bug3227.fst.json_output  : OTHERFLAGS+=--dump_module Bug3227
Bug3227.fst.output       : OTHERFLAGS+=--dump_module Bug3227
Bug3292.fst.json_output  : OTHERFLAGS+=--dump_module Bug3292
Bug3292.fst.output       : OTHERFLAGS+=--dump_module Bug3292
Bug3530.fst.json_output  : OTHERFLAGS+=--dump_module Bug3530
Bug3530.fst.output       : OTHERFLAGS+=--dump_module Bug3530
CalcImpl.fst.json_output : OTHERFLAGS+=--dump_module CalcImpl
CalcImpl.fst.output      : OTHERFLAGS+=--dump_module CalcImpl
DTuples.fst.json_output  : OTHERFLAGS+=--dump_module DTuples
DTuples.fst.output       : OTHERFLAGS+=--dump_module DTuples
SeqLit.fst.json_output   : OTHERFLAGS+=--dump_module SeqLit
SeqLit.fst.output        : OTHERFLAGS+=--dump_module SeqLit
PatImps.fst.json_output  : OTHERFLAGS+=--dump_module PatImps
PatImps.fst.output       : OTHERFLAGS+=--dump_module PatImps
TuplePat.fst.json_output : OTHERFLAGS+=--dump_module TuplePat
TuplePat.fst.output      : OTHERFLAGS+=--dump_module TuplePat
Monoid.fst.json_output   : OTHERFLAGS+=--dump_module Monoid
Monoid.fst.output        : OTHERFLAGS+=--dump_module Monoid

include $(FSTAR_HOME)/examples/Makefile.common

.PHONY: %.human_check
%.human_check: %.expected %.output
	$(Q)diff -u --strip-trailing-cr $^
	$(Q)touch $@

.PHONY: %.json_check
%.json_check: %.json_expected %.json_output
	$(Q)diff -u --strip-trailing-cr $^
	$(Q)touch $@

.PHONY: %.accept
%.accept: %.output %.json_output
	$(Q)R=$(patsubst %.output,%,$<)			&& \
		cp $$R.output $$R.expected		&& \
		cp $$R.json_output $$R.json_expected

.PHONY: %.clean
clean:
	$(call msg, "CLEAN", $<)
	$(Q)rm -f .depend
	$(Q)rm -f *.output
	$(Q)rm -f *.json_output
	$(Q)rm -rf _output
	$(Q)rm -rf _cache

.PHONY: accept
accept: $(addsuffix .accept, $(FSTAR_FILES))

# Re-do all tests
.PHONY: re
re: clean all

# Keep the output files so we can look at them easily
.SECONDARY: $(patsubst %,%.output,$(FSTAR_FILES))
.SECONDARY: $(patsubst %,%.json_output,$(FSTAR_FILES))
