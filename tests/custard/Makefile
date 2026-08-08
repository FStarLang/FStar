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
CUSTARD_TESTS += Phantom
CUSTARD_TESTS += ShortCircuit
CUSTARD_TESTS += MonoTypes
CUSTARD_TESTS += InlineFields
CUSTARD_TESTS += KeyNames
CUSTARD_TESTS += Refs
CUSTARD_TESTS += Exceptions
CUSTARD_TESTS += LocalRec
CUSTARD_TESTS += NewtypeInline
CUSTARD_TESTS += SortBy
CUSTARD_TESTS += LocalPoly
CUSTARD_TESTS += MonoHoles
CUSTARD_TESTS += DepParams

# FLAGS_<name> are extra options for that test's extraction.
FLAGS_MonoTypes = --custard_monomorphize_types true
# Section 12.3: --ugly is what made the old key printer collapse the two
# 'tweak's into one key, so the test runs with it on.  A specialization key
# must not depend on a printing option at all.
FLAGS_KeyNames = --ugly

# Section 5.0: with type monomorphization on, nothing polymorphic may survive
# -- no type variable anywhere in the file -- and each instantiation must be
# its own declaration, including the nested one and the two that are only
# spelled differently ('pair_of_ints' is 'both int', and 'nat' is 'int').
# The record recovery of section 5.5 also shows up here: 'both' arrives from
# extraction as a one-constructor variant and has to come out as a record, with
# its field reads as projections rather than as a match.
GREP_MonoTypes   = "type monoTypes_both__int" "type monoTypes_both__bool" \
                   "monoTypes_tree__int" "monoTypes_tree__string" \
                   "type prims_list__int" "type prims_list__list_int" \
                   "monoTypes_via_abbrev (p : monoTypes_both__int)" \
                   "type monoTypes_both__int = { fst : Prims.int; snd : Prims.int }" \
                   "{ fst = (p).snd; snd = (p).fst }"
NOGREP_MonoTypes = "'" "Mkboth" "match p with"

# Section 12.3: the two 'tweak's must get separate specializations, which they
# only do if the key printer distinguishes them.  The run itself is the real
# assertion (the output is "abAB", not "abab"); this checks the shape.
GREP_KeyNames = "keyNames_apply__tweak" "keyNames_apply__tweak_1" \
                "FStar_String.lowercase" "FStar_String.uppercase"

# Section 8.4: a garbage-collected reference is an OCaml 'ref', not a
# one-element array, and it is never freed.
GREP_Refs   = "(Prims.int ref)" "(ref (Prims.parse_int \"0\"))" "(!(r))" "(r) := "
NOGREP_Refs = "Array.make" "free"

# Section 8.5: each exception constructor is its own declaration, raising is
# a control-flow node rather than a call, and try_with becomes a real
# 'try ... with' whose single branch hands the value to the handler.
GREP_Exceptions   = "exception Exceptions_Empty" "exception Exceptions_Bad of" \
                    "raise Exceptions_Empty" "(try " "with" "Exceptions_Empty ->"
NOGREP_Exceptions = "FStar_All.try_with" "FStar_All.raise" "Prims.exn"

# Local [let rec]s are lambda-lifted to top-level declarations (section 5.10).
GREP_LocalRec     = "let rec localRec_rev1__aux" "let rec localRec_sum_upto__go" \
                    "let rec localRec_parity__even" "and localRec_parity__odd" \
                    "localRec_sum_upto__go n"
NOGREP_LocalRec   = "let rec aux" "let rec go"

# The collapsed newtype is the pair itself, and no [inline] marker escapes.
GREP_NewtypeInline   = "(bool, string) fStar_Pervasives_Native_tuple2"
NOGREP_NewtypeInline = "newtypeInline_step" "inline"

# The dictionary built behind a local [let] is specialized away entirely, so
# each of the two orderings gets its own copy of [sort] and no [ord] record is
# ever built at run time.
GREP_SortBy     = "sortBy_sort_by__int" "sortBy_sort_desc__int" "sortBy_cmp__int_1"
NOGREP_SortBy   = "sortBy_Mkord" "type .*sortBy_ord"

# The local polymorphic helper is substituted at its uses, so the specializing
# function it calls gets one copy per type and no dictionary survives.
GREP_LocalPoly     = "localPoly_try_unembed__int" "localPoly_try_unembed__bool" \
                     "localPoly_un__int" "localPoly_un__bool"
NOGREP_LocalPoly   = "localPoly_Mkemb" "localPoly_e_int" "localPoly_e_bool"
# ... but a *monomorphic* local helper is left alone.  Inlining it would buy
# nothing (it has no type argument to make concrete) and cost 2^n on the
# nested, twice-used helpers in [nested].
GREP_LocalPoly    += "let a = (fun y" "let b = (fun y" "let c = (fun y"

# A dependent inductive parameter list ({| printable a |} after a:Type) has to
# be opened before its sorts are looked at.
GREP_DepParams     = "type .a depParams_labelled = { tag : string; value : .a }"
NOGREP_DepParams   = "p_int"

# Section 3.2c: a Mono argument that mentions a runtime value is specialized
# on its *shape*, with the runtime parts passed as extra parameters.  The
# dictionary's code is static (p_int's printer is called directly, and the
# record never appears at runtime) and its data is not (the tag arrives as an
# argument).  The closure case is the same mechanism and leaves no closure at
# all.
GREP_MonoHoles     = "monoHoles_render__0" "monoHoles_twice__0"
NOGREP_MonoHoles   = "set_tag" "fun y"

# Issue #4382: a tuple field lives in the constructor, not behind a pointer to
# a pair; [@@@custard_inline_field] asks for the same on a named record.
GREP_InlineFields   = "InlineFields_Bar of bool \* string" \
                      "InlineFields_W of bool \* string" \
                      "InlineFields_W (pa, pb)) -> (if pa then pb else " \
                      "keep = { p : inlineFields_pair; n : Prims.int }"
NOGREP_InlineFields = "tuple2" "Mktuple2" "let p = {"

# GREP_<name>/NOGREP_<name> additionally assert on the generated .ml.  For
# Combinators (section 3.9) the *shape* of the output is the point: one
# function per (combinator, method) pair, and no record built at runtime, so
# neither the bundle type nor its projectors survive.
GREP_Combinators   = combinators_parse__t combinators_parse__tuple2 \
                     combinators_serialize__t combinators_serialize__tuple2
NOGREP_Combinators = parser_combinator __proj__

# The connectives must come out infix, so that the emitted file says what it
# means; 'logand' is the bitwise one and must stay a call.  F* has already
# turned the effectful ones into an 'if', so no EOp survives for those.
GREP_ShortCircuit   = ") && (" ") || (" "FStar_UInt32.logand"
NOGREP_ShortCircuit = "(&&)" "(||)"

# The SCC pass must group each cycle and must *not* mark anything else 'rec'.
GREP_Mutual   = "and mutual_tree" "and mutual_size_t" "and mutual_a"
NOGREP_Mutual = "let rec mutual_main"

# Pass 1 must fix the order of the two impure siblings in 'sum', which F*
# leaves nested because it classifies them as Tot (section 7.2).  Left nested,
# OCaml would evaluate them right to left and print "ba".
GREP_Anf = "let tmp1 = (anf_tick \"a\"" "let tmp2 = (anf_tick \"b\""

# Rule 1 deletes a unit-shaped proof binder from the signature and from every
# call site -- except where the type cannot distinguish it from a thunk.
GREP_Implicits   = "implicits_clamp (x : Prims.int) : Prims.int" \
                   "implicits_clampi (x : Prims.int) : Prims.int" \
                   "implicits_only_proof (tmp : unit)" \
                   "implicits_thunk (x : Prims.int) (tmp : unit)"
NOGREP_Implicits = "implicits_clamp (Prims.parse_int \"3\") ()"

# Pass 7 must drop every phantom parameter, including the ones that are only
# reachable through another declaration's phantom position.  Each surviving
# declaration therefore takes exactly one parameter.
GREP_Phantom   = "type 'a phantom_tagged" "and 'a phantom_even_t" \
                 "type 'a phantom_odd_t"
NOGREP_Phantom = "'ph"

# Each of these is extracted with --custard_backend Krml, run through karamel
# to produce C, compiled and run; the program must exit 0.  Skipped when
# karamel is not installed.
KRML_TESTS += KrmlBasic

# Each of these is extracted with --custard_backend C, then compiled by a C11
# compiler with the warnings on and run; the program must exit 0.  The direct
# backend has no polymorphism to fall back on, so it always runs with type
# monomorphization (section 5.0.1).
C_TESTS += KrmlBasic

# CGREP_<name>/CNOGREP_<name> assert on the generated .c.  These are the
# output-quality invariants of section 6: a unit parameter is a thunk, which C
# does not need; a pattern binding is an alias, not a copy; and the last arm
# of an exhaustive match is not guarded.
CGREP_KrmlBasic   = "int32_t KrmlBasic_main(void)" \
                    "if (s.tag == KRMLBASIC_SQUARE) return (s.val.KrmlBasic_Square._0" \
                    "if ((n == ((uint32_t)0))) return acc;"
CNOGREP_KrmlBasic = "custard_unit tmp" "(void)(((custard_unit)0))" "abort"

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
REJECT_TESTS += MonoEffect
CODE_MonoEffect = 363
REJECT_TESTS += MonoPartial
REJECT_TESTS += MonoFuel
REJECT_TESTS += NormBudget
# WarnAny is higher-kinded (#f:Type0 -> Type0), which has no counterpart in the
# target type language: it lands on TAny, which --custard_warn_any reports and
# WARN_ANY escalates.  This is the positive test for section 5.6.
REJECT_TESTS += WarnAny
# Section 6: the direct-to-C backend has no representation for an unbounded
# Prims.int, and none for a closure.  Both must be diagnosed, not mistranslated.
REJECT_TESTS += CNoInt
REJECT_TESTS += CNoClosure
FLAGS_CNoInt     = --custard_backend C --custard_monomorphize_types true
FLAGS_CNoClosure = --custard_backend C --custard_monomorphize_types true
CODE_CNoInt      = 367
CODE_CNoClosure  = 367
CODE_MonoPoly    = 363
CODE_MonoPartial = 363
CODE_MonoFuel    = 364
CODE_NormBudget  = 364
CODE_WarnAny     = 366

include $(FSTAR_ROOT)/mk/test.mk

# --custard_warn_any escalated to an error (section 5.6): no declaration in the
# corpus may lose the representation of a value.  This is what keeps the "no
# surviving ECast, no surviving TAny" measurement of section 5.4 true.
WARN_ANY = --custard_warn_any --warn_error @366

# Override the default OCaml extraction rule from test.mk: we drive the Custard
# pipeline instead, which is whole-program and hence keyed on an entry point.
$(OUTPUT_DIR)/%.ml:
	$(call msg, "CUSTARD", $(basename $(notdir $@)))
	$(FSTAR) --codegen Custard $(WARN_ANY) $(FLAGS_$*) --custard_main $*.main $< -o $@
	$(Q)for p in $(GREP_$*); do \
	  grep -q -- "$$p" $@ \
	    || { echo "ERROR: $* output is missing $$p"; exit 1; }; done
	$(Q)for p in $(NOGREP_$*); do \
	  grep -q -- "$$p" $@ \
	    && { echo "ERROR: $* output should not contain $$p"; exit 1; }; done; true

$(OUTPUT_DIR)/%.rejected: $(CACHE_DIR)/%.fst.checked
	$(call msg, "REJECT", $(basename $(notdir $@)))
	@mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --message_format human --codegen Custard $(WARN_ANY) $(FLAGS_$*) \
	  --custard_main $*.main $< >$(OUTPUT_DIR)/$*.err 2>&1 || true
	$(Q)grep -q "Error $(CODE_$*)" $(OUTPUT_DIR)/$*.err \
	  || { echo "ERROR: expected error $(CODE_$*) from $*"; cat $(OUTPUT_DIR)/$*.err; false; }
	$(Q)touch $@

$(OUTPUT_DIR)/%.roots: $(CACHE_DIR)/%.fst.checked
	$(call msg, "ROOTS", $(basename $(notdir $@)))
	@mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard $(WARN_ANY) $(FLAGS_$*) \
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
	$(FSTAR) --codegen Custard $(WARN_ANY) $(FLAGS_$*) --custard_backend Krml \
	  --custard_main $*.main $< -o $@

# karamel emits its own compile_flags.txt, which is the only portable way to
# learn where krmllib's headers live.
$(OUTPUT_DIR)/%.cexe: $(OUTPUT_DIR)/%.krml
	$(call msg, "KRML", $(basename $(notdir $@)))
	$(Q)krml -silent -skip-linking -no-prefix $* -tmpdir $(OUTPUT_DIR)/$*_c $<
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) $$(tr '\n' ' ' < $(OUTPUT_DIR)/$*_c/compile_flags.txt) \
	  $(OUTPUT_DIR)/$*_c/Custard.c -o $@

# The direct-to-C backend (section 6): no krmllib, no krml, just a C11
# compiler.  -Werror is part of the test -- an unused variable or a missing
# cast is a bug in the backend, not a style question.
$(OUTPUT_DIR)/%.dc: $(CACHE_DIR)/%.fst.checked
	$(call msg, "CUSTARD-C", $(basename $(notdir $@)))
	@mkdir -p $(OUTPUT_DIR)
	$(FSTAR) --codegen Custard $(WARN_ANY) --custard_backend C \
	  --custard_monomorphize_types true --custard_main $*.main $*.fst -o $@
	$(Q)for p in $(CGREP_$*); do \
	  grep -qF -- "$$p" $@ \
	    || { echo "ERROR: $* C output is missing $$p"; exit 1; }; done
	$(Q)for p in $(CNOGREP_$*); do \
	  grep -qF -- "$$p" $@ \
	    && { echo "ERROR: $* C output should not contain $$p"; exit 1; }; done; true

$(OUTPUT_DIR)/%.dcexe: $(OUTPUT_DIR)/%.dc
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) -std=c11 -Wall -Wextra -Werror -x c $< -o $@

$(OUTPUT_DIR)/%.dcran: $(OUTPUT_DIR)/%.dcexe
	$(call msg, "RUN-C", $(basename $(notdir $@)))
	$(Q)$<
	$(Q)touch $@

$(OUTPUT_DIR)/%.cran: $(OUTPUT_DIR)/%.cexe
	$(call msg, "RUN-C", $(basename $(notdir $@)))
	$(Q)$<
	$(Q)touch $@

all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .out.diff, $(CUSTARD_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .rejected, $(REJECT_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .roots, $(ROOT_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .dcran, $(C_TESTS)))

# Only when karamel is on the PATH: the OCaml backend is always testable, the
# C one needs a toolchain.
ifneq ($(shell command -v krml 2>/dev/null),)
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .cran, $(KRML_TESTS)))
endif
