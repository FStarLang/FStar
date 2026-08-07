FSTAR_ROOT ?= ../..

# Each of these modules is extracted with --codegen Custard, starting from its
# 'main' entry point, then compiled and run; the output is compared against
# the corresponding .out.expected file.
CUSTARD_TESTS += Hello
CUSTARD_TESTS += Recursion
CUSTARD_TESTS += Datatypes
CUSTARD_TESTS += Typeclass
CUSTARD_TESTS += Unroll
CUSTARD_TESTS += Layouts
CUSTARD_TESTS += Effects
CUSTARD_TESTS += Curried
CUSTARD_TESTS += Implicits
CUSTARD_TESTS += MachineInts
CUSTARD_TESTS += Externs
CUSTARD_TESTS += Combinators
CUSTARD_TESTS += Mutual
CUSTARD_TESTS += Anf

# GREP_<name>/NOGREP_<name> additionally assert on the generated .ml.  For
# Combinators (section 3.9) the *shape* of the output is the point: one
# function per (combinator, method) pair, and no record built at runtime, so
# neither the bundle type nor its projectors survive.
GREP_Combinators   = combinators_parse__t combinators_parse__tuple2 \
                     combinators_serialize__t combinators_serialize__tuple2
NOGREP_Combinators = parser_combinator __proj__

# The SCC pass must group each cycle and must *not* mark anything else 'rec'.
GREP_Mutual   = "and mutual_tree" "and mutual_size_t" "and mutual_a"
NOGREP_Mutual = "let rec mutual_main"

# Pass 1 must fix the order of the two impure siblings in 'sum', which F*
# leaves nested because it classifies them as Tot (section 7.2).  Left nested,
# OCaml would evaluate them right to left and print "ba".
GREP_Anf = "let tmp1 = (anf_tick \"a\"" "let tmp2 = (anf_tick \"b\""

# Each of these is extracted with --custard_backend Krml, run through karamel
# to produce C, compiled and run; the program must exit 0.  Skipped when
# karamel is not installed.
KRML_TESTS += KrmlBasic

# Each of these is extracted with --custard_entry and *no* --custard_main, as a
# library would be: the generated .ml must contain every GREP_<name> pattern
# and none of the NOGREP_<name> ones.
ROOT_TESTS += Library
ROOTS_Library  = scale
GREP_Library   = library_scale library_double
NOGREP_Library = library_unused "let _ ="

# Extraction of each of these must fail with the given error code: they are
# the diagnostics of sections 3.2 and 3.6.
REJECT_TESTS += MonoPoly
REJECT_TESTS += MonoPartial
REJECT_TESTS += MonoFuel
CODE_MonoPoly    = 363
CODE_MonoPartial = 363
CODE_MonoFuel    = 364

include $(FSTAR_ROOT)/mk/test.mk

# Override the default OCaml extraction rule from test.mk: we drive the Custard
# pipeline instead, which is whole-program and hence keyed on an entry point.
$(OUTPUT_DIR)/%.ml:
	$(call msg, "CUSTARD", $(basename $(notdir $@)))
	$(FSTAR) --codegen Custard --custard_main $*.main $< -o $@
	$(Q)for p in $(GREP_$*); do \
	  grep -q -- "$$p" $@ \
	    || { echo "ERROR: $* output is missing $$p"; exit 1; }; done
	$(Q)for p in $(NOGREP_$*); do \
	  grep -q -- "$$p" $@ \
	    && { echo "ERROR: $* output should not contain $$p"; exit 1; }; done; true

$(OUTPUT_DIR)/%.rejected: $(CACHE_DIR)/%.fst.checked
	$(call msg, "REJECT", $(basename $(notdir $@)))
	@mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --message_format human --codegen Custard --custard_main $*.main \
	  $< >$(OUTPUT_DIR)/$*.err 2>&1 || true
	$(Q)grep -q "Error $(CODE_$*)" $(OUTPUT_DIR)/$*.err \
	  || { echo "ERROR: expected error $(CODE_$*) from $*"; cat $(OUTPUT_DIR)/$*.err; false; }
	$(Q)touch $@

$(OUTPUT_DIR)/%.roots: $(CACHE_DIR)/%.fst.checked
	$(call msg, "ROOTS", $(basename $(notdir $@)))
	@mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard \
	  $(foreach r,$(ROOTS_$*),--custard_entry $*.$(r)) \
	  $(patsubst %,%.fst,$*) -o $(OUTPUT_DIR)/$*.ml
	$(Q)for p in $(GREP_$*); do \
	  grep -q -- "$$p" $(OUTPUT_DIR)/$*.ml \
	    || { echo "ERROR: $* output is missing $$p"; exit 1; }; done
	$(Q)for p in $(NOGREP_$*); do \
	  grep -q -- "$$p" $(OUTPUT_DIR)/$*.ml \
	    && { echo "ERROR: $* output should not contain $$p"; exit 1; }; done; true
	$(Q)touch $@

$(OUTPUT_DIR)/%.krml:
	$(call msg, "CUSTARD-KRML", $(basename $(notdir $@)))
	$(FSTAR) --codegen Custard --custard_backend Krml --custard_main $*.main $< -o $@

# karamel emits its own compile_flags.txt, which is the only portable way to
# learn where krmllib's headers live.
$(OUTPUT_DIR)/%.cexe: $(OUTPUT_DIR)/%.krml
	$(call msg, "KRML", $(basename $(notdir $@)))
	$(Q)krml -silent -skip-linking -no-prefix $* -tmpdir $(OUTPUT_DIR)/$*_c $<
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) $$(tr '\n' ' ' < $(OUTPUT_DIR)/$*_c/compile_flags.txt) \
	  $(OUTPUT_DIR)/$*_c/Custard.c -o $@

$(OUTPUT_DIR)/%.cran: $(OUTPUT_DIR)/%.cexe
	$(call msg, "RUN-C", $(basename $(notdir $@)))
	$(Q)$<
	$(Q)touch $@

all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .out.diff, $(CUSTARD_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .rejected, $(REJECT_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .roots, $(ROOT_TESTS)))

# Only when karamel is on the PATH: the OCaml backend is always testable, the
# C one needs a toolchain.
ifneq ($(shell command -v krml 2>/dev/null),)
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .cran, $(KRML_TESTS)))
endif
