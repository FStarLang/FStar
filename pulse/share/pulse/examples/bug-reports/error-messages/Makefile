PULSE_HOME ?= ../../../../..
PULSE_SHARE = $(PULSE_HOME)/share/pulse

SRC_DIRS = .
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
FSTAR_FILES=$(wildcard *.fst)

# This so that we don't get warnings about:
# 241: "unable to load checked file"
# 247: "checked file was not written"
# 333: "unable to read hints"
OTHERFLAGS+=--warn_error -241-247-333-274+240

# Sorry, without this we can get noise in error locations.
# See issue #1993. Also, warnings from dependencies would
# pollute the output.
OTHERFLAGS+=--already_cached 'Prims FStar Pulse PulseCore'

# Remove --query_stats and --hint_info from this subdir, since
# they output timing info.
OTHERFLAGS := $(filter-out --query_stats, $(OTHERFLAGS))
OTHERFLAGS := $(filter-out --hint_info, $(OTHERFLAGS))

all: check-all

check-all: $(addsuffix .check, $(FSTAR_FILES))

include $(PULSE_SHARE)/Makefile.include

%.check: %.expected %.output
	$(Q)diff -u --strip-trailing-cr $^
	$(Q)touch $@

%.fst.output: %.fst
	$(call msg, "OUTPUT", $(basename $(notdir $@)))
	$(FSTAR) -f --print_expected_failures $< >$@ 2>&1

%.accept: %.output
	$(Q)cp $< $(patsubst %.output,%.expected,$<)

accept: $(addsuffix .accept, $(FSTAR_FILES))

clean:
	$(Q)rm -f .depend
	$(Q)rm -f *.check
	$(Q)rm -f *.output
	$(Q)rm -rf _output
	$(Q)rm -rf _cache
