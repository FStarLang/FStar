FSTAR_HOME=../..

FSTAR_FILES=$(wildcard *.fst)

# This so that we don't get warnings about:
# 241: "unable to load checked file"
# 247: "checked file was not written"
# 333: "unable to read hints"
OTHERFLAGS+=--warn_error -241-247-333

# Sorry, without this we can get noise in error locations.
# See issue #1993. Also, warnings from dependencies would
# pollute the output.
OTHERFLAGS+=--already_cached 'Prims FStar'

# Remove --query_stats and --hint_info from this subdir, since
# they output timing info.
OTHERFLAGS := $(filter-out --query_stats, $(OTHERFLAGS))
OTHERFLAGS := $(filter-out --hint_info, $(OTHERFLAGS))

check-all: $(addsuffix .check, $(FSTAR_FILES))
all: check-all

Bug1997.fst.output: OTHERFLAGS+=--dump_module Bug1997

include $(FSTAR_HOME)/examples/Makefile.common

%.check: %.expected %.output
	$(Q)diff -u --strip-trailing-cr $^
	$(Q)touch $@

%.accept: %.output
	$(Q)cp $< $(patsubst %.output,%.expected,$<)

clean:
	@echo "[CLEAN]"
	$(Q)rm -f .depend
	$(Q)rm -f *.check
	$(Q)rm -f *.output
	$(Q)rm -rf _output
	$(Q)rm -rf _cache

accept: $(addsuffix .accept, $(FSTAR_FILES))

.PHONY: %.check

# Re-do all tests
re: clean all

# Keep the output files so we can look at them easily
.SECONDARY: $(patsubst %,%.output,$(FSTAR_FILES))
