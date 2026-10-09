# This is copied from $FSTAR/mk/custard-extract.mk

# Whole-program extraction of the compiler with Custard.
#
# See doc/ref/custard.md, section 12.10.  Custard is whole-program: it reads
# the checked files of the entire program at once and writes one .ml per F*
# module plus a .cui describing the unit, so there is a single rule, its
# prerequisite is every checked file, and it rewrites the whole output
# directory.
#
# Rewriting is not as expensive as it sounds: dune keys recompilation on the
# contents of a file rather than on its timestamp, so the modules the change
# did not reach are written identically and not rebuilt.
#
# The caller sets:
#   CUSTARD_UNIT   -- the name of the link unit (also the .cui's name)
#   CUSTARD_ROOT   -- the F* file(s) holding the entry points
#   CUSTARD_ENTRIES -- --custard_entry / --custard_entrypoints flags
# and optionally:
#   CUSTARD_LINK     -- .cui files of the units this one is loaded into,
#                       in dependency order (section 13)
#   CUSTARD_DEPS     -- extra files the extraction depends on
#   CUSTARD_CODEGEN  -- the flags selecting the OCaml backend, for a
#                       stage0 that spells them differently

CUSTARD_FLAGS += --lax
CUSTARD_CODEGEN ?= --codegen OCaml
CUSTARD_FLAGS += $(CUSTARD_CODEGEN)
CUSTARD_FLAGS += --custard_split
CUSTARD_FLAGS += --custard_unit $(CUSTARD_UNIT)
CUSTARD_FLAGS += $(CUSTARD_ENTRIES)
CUSTARD_FLAGS += $(patsubst %,--custard_link %,$(CUSTARD_LINK))
# -321 unused warning about interface-less modules, -274 deprecation,
# -272 top-level effect, -241 stale dependencies: the same set `make custard'
# uses, and all four are about the corpus rather than about the extraction.
CUSTARD_FLAGS += --warn_error -321-274-272-241

CUSTARD_STAMP := $(OUTPUT_DIR)/.custard.touch

$(CUSTARD_STAMP): $(ALL_CHECKED_FILES) $(CUSTARD_LINK) $(CUSTARD_DEPS)
	$(call msg, "CUSTARD", $(CUSTARD_UNIT))
	rm -rf $(OUTPUT_DIR)
	mkdir -p $(OUTPUT_DIR)
	$(FSTAR) --already_cached ',*' $(CUSTARD_FLAGS) $(CUSTARD_ROOT)
	touch $@
	$(maybe_touch)

.PHONY: custard
custard: $(CUSTARD_STAMP)
