FSTAR_HOME = ../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
EXCLUDED_FILES=
include $(FSTAR_HOME)/.common.mk

BASES=$(filter-out $(EXCLUDED_FILES), $(wildcard *.fst))

TESTS=$(patsubst %.fst, .%.test.print, $(BASES))
TESTS_IN_PLACE=$(patsubst %.fst, .%.test.inplace, $(BASES))

# GM: Do we really want to test the --print_in_place feature for every
# base file? It seems unlikely this will ever regress. But it doesn't
# take a lot of time, so no big deal.
all: $(TESTS) $(TESTS_IN_PLACE)

inplace:
	$(Q)mkdir -p $@

printed:
	$(Q)mkdir -p $@

printed/%.fst: %.fst | printed
	$(call msg, "PPRINT", $(basename $(notdir $@)))
	$(Q)$(FSTAR) $(SIL) --print $< > $@

inplace/%.fst: %.fst | inplace
	$(call msg, "PPRINT", $(basename $(notdir $@)))
	$(Q)cp $< $@
	$(Q)$(FSTAR) $(SIL) --print_in_place $@


# Note how these two rules make an empty touch file for 
# the target so we don't keep running diff uselessly.
.%.test.print: %.fst.expected printed/%.fst
	$(Q)diff -w -u --strip-trailing-cr $^
	$(Q)touch $@

.%.test.inplace: %.fst.expected inplace/%.fst
	$(Q)diff -w -u --strip-trailing-cr $^
	$(Q)touch $@

%.fst.accept: printed/%.fst
	cp $< $(patsubst printed/%.fst,%.fst.expected, $<)

accept: $(patsubst %, %.accept, $(BASES))

clean:
	$(call msg, "CLEAN")
	$(Q)rm -rf printed inplace
	$(Q)rm -f .*.test.print
	$(Q)rm -f .*.test.inplace

.PHONY: accept clean

# Keep the printed fst files so we can look at them easily
# Sigh, .SECONDARY does not take patterns
.SECONDARY: $(patsubst %,printed/%,$(BASES))
.SECONDARY: $(patsubst %,inplace/%,$(BASES))

# This is so that, e.g., if the --print call fails then make will delete
# the printed file, which is anyway created by bash (and will likely
# be empty). Otherwise, we will get an empty printed/Blah.fst and,
# confusingly, see a diff with all the lines in it.
.DELETE_ON_ERROR:
