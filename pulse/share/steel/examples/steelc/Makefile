all: verify test

# assuming share/steel/examples/steelc
STEEL_HOME ?= ../../../..

FSTAR_OPTIONS += --include $(STEEL_HOME)/lib/steel/c

ifneq (,$(KRML_HOME))
# We need to add some Low* files to the dependency roots, because
# of C._zero_for_deref
FSTAR_FILES += $(KRML_HOME)/krmllib/C.fst
KRML_EXE = $(KRML_HOME)/krml
FSTAR_OPTIONS += --include $(KRML_HOME)/krmllib --include $(KRML_HOME)/krmllib/obj
endif

include $(STEEL_HOME)/share/steel/Makefile.include

ifneq (,$(KRML_HOME))

FILTERED_KRML_FILES=$(filter-out FStar_NMST.krml Steel_%.krml,$(ALL_KRML_FILES))

# NOTE: this is NOT a phony rule
extract: $(FILTERED_KRML_FILES)
	$(KRML_EXE) -skip-compilation -skip-makefiles -bundle 'FStar.\*,Steel.\*,C' -add-include '"steel_c.h"' $^
	touch $@

ALL_MODULE_NAMES=$(basename $(wildcard *.fst))
ALL_C_FILES=$(addsuffix .c,$(ALL_MODULE_NAMES))

$(ALL_C_FILES): %.c: extract
	test -f $@
	touch $@

ALL_O_FILES=$(subst .c,.o,$(ALL_C_FILES))

$(ALL_O_FILES): %.o: %.c
	$(CC) $(CFLAGS) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal -I $(STEEL_HOME)/include/steel -o $@ -c $<

test: $(ALL_O_FILES)

clean::
	rm -f *.c *.h *.o extract

else # no KRML_HOME

test:
	echo KaRaMeL is not installed, skipping test

endif # KRML_HOME

.PHONY: test
