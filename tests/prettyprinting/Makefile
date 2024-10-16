FSTAR_ROOT ?= ../..
NODEPEND=1
include $(FSTAR_ROOT)/mk/test.mk

EXCLUDED_FILES=
FSTAR_FILES=$(filter-out $(EXCLUDED_FILES), $(wildcard *.fst))

TESTS=$(patsubst %.fst, .%.test.print, $(FSTAR_FILES))
TESTS_IN_PLACE=$(patsubst %.fst, .%.test.inplace, $(FSTAR_FILES))

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
	$(Q)$(FSTAR) --print $< > $@

inplace/%.fst: %.fst | inplace
	$(call msg, "PPRINT INPLACE", $(basename $(notdir $@)))
	$(Q)cp $< $@
	$(Q)$(FSTAR) --print_in_place $@

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

accept: $(patsubst %, %.accept, $(FSTAR_FILES))

.PHONY: accept clean

# Keep the printed fst files so we can look at them easily
# Sigh, .SECONDARY does not take patterns
.SECONDARY: $(patsubst %,printed/%,$(FSTAR_FILES))
.SECONDARY: $(patsubst %,inplace/%,$(FSTAR_FILES))

# This is so that, e.g., if the --print call fails then make will delete
# the printed file, which is anyway created by bash (and will likely
# be empty). Otherwise, we will get an empty printed/Blah.fst and,
# confusingly, see a diff with all the lines in it.
.DELETE_ON_ERROR:
