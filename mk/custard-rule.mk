# Section 34: the dependency closure of the rule test, checked by the
# Custard-built compiler.
#
# This is a separate makefile only because the dependency graph has to be
# *generated* by that compiler and then included, and a recipe cannot include
# a file it just wrote.  It is called from mk/custard.mk's `plugin' target.
#
# The closure has to be rechecked here rather than reused: section 12.10's
# limitation is that a Custard-built compiler cannot read .checked files
# written by a dune-built one, and $(CACHE) holds the latter.  --lax is
# enough -- what is under test is the extraction, and ulib is verified
# everywhere else -- and makes the 37 modules take about fifteen seconds.

include $(RULE_DEPEND)

%.checked:
	$(RULE_FSTAR) -c $< -o $@

all: $(ALL_CHECKED_FILES)
.PHONY: all
