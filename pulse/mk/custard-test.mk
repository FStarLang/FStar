# Custard extraction for the Pulse test suite.
#
# Include this *after* mk/test.mk.  It replaces that file's OCaml, krml and C
# rules with the Custard pipeline, and leaves everything else -- checking,
# expected-output diffing, subdirectory recursion -- exactly as it was.
#
# The three differences that matter to a client makefile:
#
#  * Custard is whole-program, so there is no per-module dependency graph to
#    hand to karamel: no -bundle, no -library, and none of the extra .krml
#    prerequisites the old rules needed.  One .fst goes in, one translation
#    unit comes out, with everything it reaches inlined into it.
#
#  * A test module has no single entry point; it is a handful of functions
#    that exist to be looked at.  --custard_entry_module makes all of them
#    roots, so a function added to a test is extracted without anyone having
#    to name it -- which is the property an expected-output test needs.
#
#  * C is emitted by Custard itself, not by karamel, and the result is
#    compiled with the warnings on.  A module the direct backend cannot take
#    -- in practice one whose interface mentions Prims.int, which is unbounded
#    and so has no C representation -- is listed in CUSTARD_KRML_C and goes
#    through karamel instead, which represents it as a checked 64-bit integer.
#
# Per-module extra flags go in CUSTARD_FLAGS_<Module>, with the module's real
# name (dots and all), not the underscored file name.

# Every module in the directory.  The .expected files decide which of these
# are actually extracted; this list only exists to recover a module name from
# a file name, which no amount of $(subst) can do.
CUSTARD_MODULES := $(basename $(wildcard *.fst))

CUSTARD_KRML_C ?=

# Shared by all three backends.  The tests are extracted from .checked files
# and never re-verify, so warnings that only a checker can raise are off.
CUSTARD = --codegen Custard

# OCaml.  Overrides the rule in test.mk; the prerequisites still come from
# .depend, so $< is the module's own .checked file and $* is its underscored
# name.
$(OUTPUT_DIR)/$(subst .,_,%).ml:
	$(call msg, "CUSTARD", $(basename $(notdir $@)))
	$(FSTAR) $< $(CUSTARD) \
	  --custard_entry_module $(basename $(basename $(notdir $<))) \
	  $(CUSTARD_FLAGS_$(basename $(basename $(notdir $<)))) -o $@

# karamel's input.  Whole-program, so --extract_module is meaningless here.
$(OUTPUT_DIR)/$(subst .,_,%).krml:
	$(call msg, "CUSTARD-KRML", $(basename $(notdir $@)))
	$(FSTAR) $< $(CUSTARD) --custard_backend Krml \
	  --custard_entry_module $(basename $(basename $(notdir $<))) \
	  $(CUSTARD_FLAGS_$(basename $(basename $(notdir $<)))) -o $@

# The C rules are generated per module rather than written as patterns,
# because the direct and the karamel path need different prerequisites and
# because the recipe needs the module's dotted name.

# $(1) is the dotted module name.  ALL_CHECKED_FILES is coarse -- a
# whole-program extraction reads far more than the module's own .checked file,
# and .depend does not describe a target Custard invented -- but a test suite
# can afford to re-extract when any of its modules changes.
define custard_c_direct
$(OUTPUT_DIR)/$(subst .,_,$(1)).c: $(CACHE_DIR)/$(1).fst.checked $$(ALL_CHECKED_FILES)
	$$(call msg, "CUSTARD-C", $(1))
	$$(FSTAR) $$< $$(CUSTARD) --custard_backend C \
	  --custard_monomorphize_types true --custard_entry_module $(1) \
	  $$(CUSTARD_FLAGS_$(1)) -o $$@
	$$(Q)$$(call custard_no_empty_blocks,$$@)
endef

# A whole-program krml file holds exactly one module, named Custard, so there
# is nothing to bundle and karamel writes Custard.c whatever the test is
# called.  It is built in a directory of its own -- karamel compiles it there,
# which is the other half of the test -- and the translation unit is then
# copied out under the test's name for the expected-output diff.
define custard_c_krml
$(OUTPUT_DIR)/$(subst .,_,$(1)).c: $(OUTPUT_DIR)/$(subst .,_,$(1)).krml
	$$(call msg, "KRML", $(1))
	$$(Q)if ! which $$(KRML_EXE) >/dev/null; then \
	  echo "krml ($$(KRML_EXE)) not found" >&2; false; fi
	$$(KRML_EXE) $$(KRML_FLAGS) -skip-makefiles -header=$$(PULSE_ROOT)/mk/krmlheader \
	  -no-prefix Custard -skip-linking $$< -tmpdir $$(OUTPUT_DIR)/$(subst .,_,$(1)).krmlout
	$$(Q)cp $$(OUTPUT_DIR)/$(subst .,_,$(1)).krmlout/Custard.c $$@
endef

$(foreach m,$(CUSTARD_MODULES),\
  $(eval $(call $(if $(filter $(m),$(CUSTARD_KRML_C)),custard_c_krml,custard_c_direct),$(m))))

# The same invariant tests/custard holds every C test to: a block with nothing
# in it is a branch the backend failed to notice was empty.  Stated once, for
# every test, rather than as a list of the shapes that have violated it.
define custard_no_empty_blocks
awk '/\{$$/ { open = NR; next } \
     /^[ \t]*\}/ && open == NR - 1 { print NR; found = 1 } \
     { open = 0 } END { exit found }' $(1) \
  || { echo "ERROR: $(1) has an empty block, at the lines above"; exit 1; }
endef

# The direct backend's output is a self-contained translation unit over the C
# standard headers, so compiling it needs no include path and no krmllib.
# -Werror is part of the test: an unused variable or a missing cast is a bug
# in the backend, not a style question.  A client may add to CUSTARD_CFLAGS
# before this file is included; the base flags are prepended to whatever it
# set.
CUSTARD_CFLAGS := -std=c11 -Wall -Wextra -Werror $(CUSTARD_CFLAGS)

$(OUTPUT_DIR)/%.o: $(OUTPUT_DIR)/%.c
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) $(CUSTARD_CFLAGS) -c $< -o $@

# Compile every C test that the direct backend produced.  The karamel ones are
# already compiled by krml itself, as part of -skip-linking.
CUSTARD_C_EXPECTED := $(patsubst %.c.expected,%,$(wildcard *.c.expected))
CUSTARD_C_DIRECT   := $(filter-out $(foreach m,$(CUSTARD_KRML_C),$(subst .,_,$(m))),\
                        $(CUSTARD_C_EXPECTED))

__custard_cc: $(patsubst %,$(OUTPUT_DIR)/%.o,$(CUSTARD_C_DIRECT))
all: __custard_cc
.PHONY: __custard_cc
