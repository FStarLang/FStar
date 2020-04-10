FSTAR_HOME=../..

FSTAR_FILES=$(wildcard *.fst)

# This so that we don't get warnings about:
# 241: "unable to load checked file"
# 247: "checked file was not written"
# 333: "unable to read hints"
OTHERFLAGS+=--warn_error -241-247-333

# Remove --query_stats from this subdir, since
# it outputs timing info.
OTHERFLAGS := $(filter-out --query_stats, $(OTHERFLAGS))

all: verify-all

include $(FSTAR_HOME)/examples/Makefile.common

verify-all: $(addsuffix .check, $(FSTAR_FILES))

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
