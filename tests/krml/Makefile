FSTAR_HOME=../..
FSTAR_FILES = $(wildcard *.fst)
OTHERFLAGS += --warn_error -321 # I don't understand this error, really

CACHE_DIR=_cache
OUTPUT_DIRECTORY=_output

KRML=$(KRML_HOME)/krml

all: compare-all

# FIXME: the rules from Makefile.common interact poorly with the rules
# here and we end up checking each module twice.

include $(FSTAR_HOME)/examples/Makefile.common

FILES := $(wildcard *.fst)

compare-all: $(patsubst %.fst,%.cmp,$(FILES))

accept: $(patsubst %.fst,%.accept,$(FILES))

verify-all: # _cache/Inline.fst.checked

%.c: $(OUTPUT_DIRECTORY)/%.krml
	$(call msg, "KRML", $@)
	$(Q)krml -silent -header /dev/null -skip-compilation -skip-makefiles $<

# We check and extract in one pass.
$(OUTPUT_DIRECTORY)/%.krml: %.fst
	$(call msg, "CHECK", $@)
	$(Q)$(FSTAR) $(SIL) $(OTHERFLAGS) --extract $(subst .fst,,$<) --codegen krml --krmloutput $@ $<

%.cmp: %.c %.c.expected
	$(call msg, "DIFF", $<)
	$(Q)diff -u --strip-trailing-cr $<.expected $<
	$(Q)touch $@

%.accept: %.c
	$(call msg, "ACCEPT", $<)
	$(Q)cp $<.expected $<

clean:
	rm -f .depend
	rm -rf _cache
	rm -rf _output

.PRECIOUS: %.c %.krml
