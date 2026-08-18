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
CUSTARD_TESTS += PolyVal
CUSTARD_TESTS += TypeEntry
CUSTARD_TESTS += ShortCircuit
CUSTARD_TESTS += MonoTypes
CUSTARD_TESTS += MonoState
CUSTARD_TESTS += InlineFields
CUSTARD_TESTS += KeyNames
CUSTARD_TESTS += Refs
CUSTARD_TESTS += Thunk
CUSTARD_TESTS += Exceptions
CUSTARD_TESTS += LocalRec
CUSTARD_TESTS += RecEffect
CUSTARD_TESTS += NewtypeInline
CUSTARD_TESTS += SortBy
CUSTARD_TESTS += LocalPoly
CUSTARD_TESTS += MonoHoles
CUSTARD_TESTS += DepParams
CUSTARD_TESTS += MonoDyn
CUSTARD_TESTS += MatchGuard
CUSTARD_TESTS += Magic
CUSTARD_TESTS += HigherKind
CUSTARD_TESTS += Literals
CUSTARD_TESTS += RetArity
CUSTARD_TESTS += Realized
CUSTARD_TESTS += Patlift
CUSTARD_TESTS += EraseAbbrev
GREP_EraseAbbrev = "let eraseAbbrev_add4 (n : Prims.int) (x : Prims.int) (y : Prims.int) : Prims.int"
# The failure this guards against is [add4] keeping its abbreviated codomain
# as an arrow instead of taking its binders: [let add4 (n : Prims.int) : ...].
# Naming [add4] is what makes it specific -- a plain arrow is a perfectly
# good type for a parameter, and [twice] takes one.
NOGREP_EraseAbbrev = "let eraseAbbrev_add4 (n : Prims.int) :"
CUSTARD_TESTS += Mymon
CUSTARD_TESTS += Reify
CUSTARD_TESTS += AssumedProj
# Section 5.0: [let mymon = writer (list int)] is an abbreviation of kind
# [Type -> Type] that binds *no* binders.  The IR has no partial application
# of a type constructor, so the abbreviation is eta-expanded from the binders
# of its own type; left as is, its use as a monad loses an argument.
GREP_Mymon += "let rec mymon_iterM__writer_list_int (f : ('a -> ((Prims.int) list \* unit))) (l : ('a) list)"
# Section 5.6: a local [let rec] is lambda-lifted, and its binders and its body
# must come from *one* opening of the definiens -- [abs_formals] invents fresh
# names every time, so opening twice gives the body variables that no binder
# binds.  Here both binders are the same [uu___], so the two occurrences
# collapsed into one and the second argument was silently dropped.
GREP_Patlift += "match (tmp, tmp1) with"
# Section 5.1: a negative literal is a *reduced* application, and the
# normalizer hands the result back as an embedding rather than as a constant.
# Left lazy it looks like a term with no runtime meaning and is erased to
# [()], which typechecks nowhere and is silently wrong where it does.
GREP_Literals += "(Prims.parse_int \"-1\")"
# Section 5.0: [m : Type -> Type] is a type binder, so it is erased like any
# other -- and so is a type argument in a spine whose head is a [match], which
# is what a method call on a [dyn] dictionary compiles to.  Either one left
# behind is an unbound variable in the emitted OCaml, which is what compiling
# and running this test checks.  --warn_error -366 for the same reason as
# Magic: a class over a type constructor has Obj.t fields.
FLAGS_HigherKind    = --warn_error -366
NOGREP_HigherKind  += ") a "
# Section 5.4: a class over a type constructor used to be the one thing
# neither the IR nor OCaml could name.  It no longer is: [m : Type -> Type] is
# a type binder like any other, so a call whose instance is known specializes
# on it, and this module comes out entirely at [option] with no coercion at
# all.  That is what is pinned here -- see HigherKind for the case that does
# still need [Obj.t], where the dictionary is only known at run time.
GREP_Magic   += "(magic_twice__option (Some ((Prims.parse_int \"21\"))))"
GREP_Magic   += "let magic_ret__option (tmp : 'a) : ('a) option ="
# Section 8.5: a projector or discriminator that [@@no_auto_projectors] left
# as a bare [val] must be *derived* from the type declaration, not treated as
# an external.  Left external it prints as a qualified call to a realization
# that does not exist.
NOGREP_AssumedProj += "AssumedProj\.u___proj"
GREP_AssumedProj += "here = (Prims.parse_int \"7\")"

NOGREP_Magic += "Obj.magic"
NOGREP_Magic += "Obj.t"
# One shared specialization taking the dictionary at run time (the identity
# skeleton), one fully specialized version for the static call site, and no
# trace of the [dyn] marker itself.
GREP_MonoDyn += "monoDyn_render__int_dyn_printable (tmp : (Prims.int -> string)) : (Prims.int -> string)"
GREP_MonoDyn += "monoDyn_render__int (x : Prims.int) : string"
# The marker itself must be gone; it survives only inside the *name* of the
# specialization that asked for it, which is exactly what it means.
NOGREP_MonoDyn += "Custard_dyn"

# FLAGS_<name> are extra options for that test's extraction.
FLAGS_MonoTypes = --custard_monomorphize_types true
# Section 7.4: [Tac] is a reifiable effect, so it is compiled through its
# representation type -- [tac_repr a wp = ref_proofstate -> Dv a] -- and not by
# erasing the effect.  What is pinned is that the proofstate argument is there
# and that the definition returning it is *pure*: applying a metaprogram to its
# own arguments builds a closure and runs nothing.  [twice] is not reachable
# from [main], so it is named as an entry point of its own.
FLAGS_Reify = --custard_entry Reify.twice --custard_entry Reify.after_letrec
GREP_Reify += "let reify_add (x : Prims.int) : (fStarC_Tactics_Types_ref_proofstate -> Prims.int) ="
# The bind is fully reduced: what is left is the proofstate threaded through
# two calls in sequence, which is what the representation type means.
GREP_Reify += "(fun ps -> (let x1 = (reify_add x ps) in"
GREP_Reify += "(reify_add x1 ps)))"
# Section 8.3: ulib's [FStar.Stubs.Tactics.Types] is a stub for the compiler's
# own [FStarC.Tactics.Types], and the two have to be one name.
NOGREP_Reify += "FStar_Stubs"
# Section 7.5: the [let] after the local [let rec] has to be reified too; left
# unreified it compiles as if [add] returned an integer -- and, since a call
# that returns a value looks pure, is deleted outright.
GREP_Reify += "(fun ps -> (let x = (reify_add (reify_after_letrec__sum l) ps) in"
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
                   "type monoTypes_both__int = {" "fst : Prims.int;" "snd : Prims.int;" \
                   "{ fst = ((p : monoTypes_both__int)).snd;"
NOGREP_MonoTypes = "'" "Mkboth" "match p with"
# Section 5.0.1: a type of a realized module is frozen, so it is neither
# cloned nor emitted, and prints in OCaml's own syntax.  A clone of it would
# name a member the realization does not define -- which is what every one of
# these used to be.
NOGREP_MonoTypes += "fStar_Pervasives_Native"
GREP_MonoTypes   += "(o : (Prims.int) option)"
GREP_MonoTypes   += "(q : (prims_list__int \* Prims.int))"
# Frozen affects the name only: the list inside the tuple is still cloned, and
# the pattern under it still renamed against that clone.
GREP_MonoTypes   += "| Prims_Nil__int ->"

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

# Section 7.3 only deletes a *pure* discarded subterm, so the effect of a call
# into a recursion still being extracted has to be assumed impure: the callee
# is not in [st.emitted] yet, and read pure the first of two recursive calls
# in [walk l; walk r] is silently deleted.  Deleting it is not a compile error
# anywhere -- it is a traversal that stops visiting half of its argument.
GREP_RecEffect = "recEffect_walk l" "recEffect_walk_r l" "recEffect_walk_local__go l"

# The collapsed newtype is the pair itself, and no [inline] marker escapes.
GREP_NewtypeInline   = "(bool \* string)"
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
GREP_DepParams     = "type .a depParams_labelled = {" "tag : string;" "value : .a;"
NOGREP_DepParams   = "p_int"

# Section 5.0: a higher-kinded Mono argument arrives as a *lambda*, so
# substituting it leaves a beta-redex in type position -- [m a] becomes
# [(fun a -> ctxt -> ML (a & ctxt)) a].  Read as [any] that made the whole of
# a state monad's plumbing Obj.t; the compiler's own output had 528 Obj.magic
# and has 80.  So the assertion is that the state type is written down, and
# that nothing here is an Obj at all -- which --custard_warn_any, on by
# default for these tests, independently checks.
GREP_MonoState     = "(monoState_ctxt -> ('a \* monoState_ctxt))" \
                     "let rec monoState_walk (l : (Prims.int) list) : (monoState_ctxt -> (unit \* monoState_ctxt))"
NOGREP_MonoState   = "Obj"

# Section 3.2c: a Mono argument that mentions a runtime value is specialized
# on its *shape*, with the runtime parts passed as extra parameters.  The
# dictionary's code is static (p_int's printer is called directly, and the
# record never appears at runtime) and its data is not (the tag arrives as an
# argument).  The closure case is the same mechanism and leaves no closure at
# all.
GREP_MonoHoles     = "monoHoles_render__int" "monoHoles_twice__op_Addition"
NOGREP_MonoHoles   = "set_tag" "fun y"

# Issue #4382: a tuple field lives in the constructor, not behind a pointer to
# a pair; [@@@custard_inline_field] asks for the same on a named record.
GREP_InlineFields   = "InlineFields_Bar of bool \* string" \
                      "InlineFields_W of bool \* string" \
                      "InlineFields_W (pa, pb)) -> (if pa then pb else " \
                      "type inlineFields_keep = {" "p : inlineFields_pair;"
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

# A phantom type parameter is carried rather than eliminated: a type's layout
# is a function of the type, and dropping a parameter is a function of the
# whole program.  The parameter is free in OCaml and gone by the time the C
# backend sees anything, since monomorphization has run.  What this checks is
# that it survives *uniformly* -- every declaration keeps both parameters, so
# no use site disagrees with a declaration about the arity.
# The retained binder is a placeholder, so it is typed 'unit' and passed '()':
# typing it by its sort would make it 'any' and put an Obj.magic at every call.
# The abbreviation is emitted only because it is named as an entry point.
FLAGS_TypeEntry  = --custard_entry TypeEntry.t
GREP_TypeEntry   = "type typeEntry_t ="

GREP_PolyVal   = "let polyVal_box_empty (tmp : unit)" "(polyVal_box_empty ())"
NOGREP_PolyVal = "Obj.magic"

GREP_Phantom   = "type ('a, 'ph) phantom_tagged" "and ('a, 'ph) phantom_even_t" \
                 "type ('a, 'ph) phantom_odd_t"

# Each of these is extracted with --custard_backend Krml, run through karamel
# to produce C, compiled and run; the program must exit 0.  Skipped when
# karamel is not installed.
KRML_TESTS += KrmlBasic

# Each of these is extracted with --custard_backend C, then compiled by a C11
# compiler with the warnings on and run; the program must exit 0.  The direct
# backend has no polymorphism to fall back on, so it always runs with type
# monomorphization (section 5.0.1).
C_TESTS += KrmlBasic CExtern CRecType IndexedSquash CByValue CDeadLet CFunPtr
C_TESTS += RefStrip

# Section 14.5 and 14.6: a type the target declares, said both ways, and a
# global whose initializer is a computation -- against one that is a constant
# expression, which is declared with its value and stays out of
# custard_init_globals so that the linker can put it in .rodata.
FLAGS_CExtern   = --custard_extern_type 'CExtern.tag=cextern_tag_t@CExtern_stubs.h'
CGREP_CExtern   = "include \"CExtern_stubs.h" \
                  "cextern_handle_t b_h;" \
                  "void custard_init_globals(void)" \
                  "CExtern_gt = cextern_mk_tag();" \
                  "if (c.tag == CEXTERN_BUMP) cextern_bump(" \
                  "uint32_t CExtern_base = ((uint32_t)7U);" \
                  "uint8_t CExtern_low = (uint8_t)((uint32_t)300U);"
# No definition is emitted for either external type, and neither is declared
# as an abstract struct the way a Custard-owned opaque type would be.
CNOGREP_CExtern = "typedef cextern_handle_t" "CExtern_handle" "CExtern_tag" \
                  "  CExtern_base =" "  CExtern_low ="

# Section 18.2: an inductive indexed by a value that occurs only under [squash].
# The index is dropped from [payload], as it should be, but [dtuple2]'s second
# parameter is an arity over that index -- and dropping *that* left the second
# field typed by a name no parameter bound, so it was [any] and had no C
# representation at all.  This is EverParse's whole parse/serialize idiom.
CGREP_IndexedSquash   = "IndexedSquash_payload _2;"
CNOGREP_IndexedSquash = "void *"

# Section 17.3: recursion through a pointer.  Every struct is tagged and every
# tag is forward-declared, so a field may name a type that is defined later --
# which a self-referential type always does.
CGREP_CRecType   = "typedef struct CRecType_tree_s CRecType_tree;" \
                   "typedef struct CRecType_node_s CRecType_node;" \
                   "struct CRecType_node_s {" \
                   "CRecType_tree *left;"
# No struct typedef is anonymous any more, and the recursive types are not
# rejected as infinite: the recursion goes through a pointer.
CNOGREP_CRecType = "typedef struct {" "} CRecType_tree;" "} CRecType_node;"

# Section 18.4: a field held by value needs a complete type, so the struct
# definitions are topologically sorted over the by-value edges -- which are
# acyclic even when the group as a whole is cyclic through a pointer.  The
# real assertion is that this compiles: without the sort, [arr] holds a
# [slice__raw] that is still incomplete at that point, which is an error.
CGREP_CByValue   = "CByValue_slice__raw a_ptr;" "CByValue_raw *s_base;"
CNOGREP_CByValue = "typedef struct {"

# Section 19.5: a pattern that names fields the body never reads leaves a
# declaration with an initializer and no use, which -Werror=unused-variable
# refuses.  The real assertion is that this file compiles at all; the greps
# only pin down that the *live* binding is still there and the dead ones are
# not declared under any name.
CGREP_CDeadLet   = "return dflt;" "return s.val.CDeadLet_Rect._1;"
CNOGREP_CDeadLet = " = p;" "_letpattern"

# Section 19.14: the refinement on [table] costs 2^40 steps to normalize and
# has no bearing on any question Custard asks about the declaration.  The
# budget is what makes this a test: it is far below what normalizing the
# proposition would take, so extracting at all is the assertion.
FLAGS_RefStrip   = --custard_norm_budget 20000
CGREP_RefStrip   = "uint32_t RefStrip_table = ((uint32_t)7U);"
CNOGREP_RefStrip = "q40"

# Section 19.12: a closed lambda is lifted to a top-level function and the
# record stores its address, which is the same C the named version produces.
# The two greps are the two halves: a lifted function exists, and no lambda
# survived anywhere (a surviving one would not have compiled, so this pins
# down that the fix was lifting and not something else).
CGREP_CFunPtr   = "bool CFunPtr_mk_lambda__lam(uint64_t" \
                  ".impl_validate = CFunPtr_mk_lambda__lam" \
                  ".impl_validate = CFunPtr_is_even" \
                  "CFunPtr_quarter__lam"
CNOGREP_CFunPtr = "(*)("

# CGREP_<name>/CNOGREP_<name> assert on the generated .c.  These are the
# output-quality invariants of section 6: a unit parameter is a thunk, which C
# does not need; a pattern binding is an alias, not a copy; and the last arm
# of an exhaustive match is not guarded.
CGREP_KrmlBasic   = "int32_t KrmlBasic_main(void)" \
                    "if (s.tag == KRMLBASIC_SQUARE) return (s.val.KrmlBasic_Square._0" \
                    "if ((n == ((uint32_t)0U))) return acc;"
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
	$(FSTAR) --codegen Custard $(WARN_ANY) $(FLAGS_$*) --custard_backend C \
	  --custard_monomorphize_types true --custard_main $*.main $*.fst -o $@
	$(Q)for p in $(CGREP_$*); do \
	  grep -qF -- "$$p" $@ \
	    || { echo "ERROR: $* C output is missing $$p"; exit 1; }; done
	$(Q)for p in $(CNOGREP_$*); do \
	  grep -qF -- "$$p" $@ \
	    && { echo "ERROR: $* C output should not contain $$p"; exit 1; }; done; true
	$(Q)awk '/\{$$/ { open = NR; next } \
	         /^[ \t]*\}/ && open == NR - 1 { print NR; found = 1 } \
	         { open = 0 } END { exit found }' $@ \
	  || { echo "ERROR: $* C output has an empty block, at the lines above"; \
	       exit 1; }

$(OUTPUT_DIR)/%.dcexe: $(OUTPUT_DIR)/%.dc
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) -std=c11 -Wall -Wextra -Werror -I$(CURDIR) -x c $< -o $@

$(OUTPUT_DIR)/%.dcran: $(OUTPUT_DIR)/%.dcexe
	$(call msg, "RUN-C", $(basename $(notdir $@)))
	$(Q)$<
	$(Q)touch $@

$(OUTPUT_DIR)/%.cran: $(OUTPUT_DIR)/%.cexe
	$(call msg, "RUN-C", $(basename $(notdir $@)))
	$(Q)$<
	$(Q)touch $@

# Section 12: separate compilation.  SepLib is compiled once, on its own, as a
# named unit; SepApp links against the .cui it left behind.  What is being
# tested is not that the two agree at run time -- that is the easy half -- but
# that SepApp *did not compile any of SepLib again*: the NOGREPs below are the
# actual assertion, and the run only confirms that the references it emitted
# instead denote what they should.
$(OUTPUT_DIR)/SepLib.cui: $(CACHE_DIR)/SepLib.fst.checked
	$(call msg, "CUSTARD-UNIT", SepLib)
	@mkdir -p $(OUTPUT_DIR)
	$(FSTAR) --codegen Custard $(WARN_ANY) --custard_unit SepLib \
	  --custard_entry SepLib.sum_areas --custard_entry SepLib.area \
	  --custard_entry SepLib.bump --custard_entry SepLib.describe \
	  --odir $(OUTPUT_DIR) SepLib.fst

$(OUTPUT_DIR)/SepLib.ml: $(OUTPUT_DIR)/SepLib.cui
	$(Q)test -f $@

$(OUTPUT_DIR)/SepApp.ml: $(CACHE_DIR)/SepApp.fst.checked $(OUTPUT_DIR)/SepLib.cui
	$(call msg, "CUSTARD-LINK", SepApp)
	$(FSTAR) --codegen Custard $(WARN_ANY) \
	  --custard_link $(OUTPUT_DIR)/SepLib.cui \
	  --custard_main SepApp.main SepApp.fst -o $@
	$(Q)for p in $(GREP_SepApp); do \
	  grep -q -- "$$p" $@ \
	    || { echo "ERROR: SepApp output is missing $$p"; exit 1; }; done
	$(Q)for p in $(NOGREP_SepApp); do \
	  grep -q -- "$$p" $@ \
	    && { echo "ERROR: SepApp output should not contain $$p"; exit 1; }; done; true

# The imported function is called through its unit's module, and the imported
# type, constructor and record field are all spelled with that qualification.
GREP_SepApp  += "SepLib.sepLib_sum_areas"
GREP_SepApp  += "SepLib.SepLib_Circle"
# Not one line of SepLib was compiled again -- not its functions, not its types.
NOGREP_SepApp += "let sepLib_sum_areas"
NOGREP_SepApp += "let sepLib_area"
NOGREP_SepApp += "type sepLib_shape"
NOGREP_SepApp += "type sepLib_named"
GREP_SepApp  += "SepLib.sepLib_describe"
GREP_SepApp  += "SepLib.SepLib_Rect"

$(OUTPUT_DIR)/SepApp.exe: $(OUTPUT_DIR)/SepLib.ml $(OUTPUT_DIR)/SepApp.ml
	$(call msg, "OCAMLOPT", SepApp)
	$(FSTAR_EXE) --ocamlopt -I $(OUTPUT_DIR) $(OUTPUT_DIR)/SepLib.ml $(OUTPUT_DIR)/SepApp.ml -o $@

all: $(OUTPUT_DIR)/SepApp.out.diff

# Section 12.9: output splitting.  SplitLo is Custard-compiled, SplitMid.ml is
# hand written and calls SplitLo, SplitHi is Custard-compiled and calls
# SplitMid -- the alternation F*'s own realizations create, and the one a
# single output file cannot express because OCaml compilation units must form
# a DAG.  What is tested is that the split puts each declaration in the file
# its own module names, under the plain identifier the hand-written code
# spells, in an order ocamlopt accepts.
#
# SplitLo.add_one is a root, because only the hand-written OCaml calls it and
# dead-code elimination cannot see that.  That is the general rule for a
# realization's callees, and the same --custard_entry idiom section 4.4 asks
# of a library.
$(OUTPUT_DIR)/SplitHi.ml: $(CACHE_DIR)/SplitHi.fst.checked
	$(call msg, "CUSTARD-SPLIT", SplitHi)
	@mkdir -p $(OUTPUT_DIR)
	$(FSTAR) --codegen Custard $(WARN_ANY) --custard_split \
	  --custard_main SplitHi.main --custard_entry SplitLo.add_one \
	  --odir $(OUTPUT_DIR) SplitHi.fst
	$(Q)test -f $(OUTPUT_DIR)/SplitLo.ml
	$(Q)for p in $(GREP_SplitLo); do \
	  grep -q -- "$$p" $(OUTPUT_DIR)/SplitLo.ml \
	    || { echo "ERROR: SplitLo output is missing $$p"; exit 1; }; done
	$(Q)for p in $(GREP_SplitHi); do \
	  grep -q -- "$$p" $@ \
	    || { echo "ERROR: SplitHi output is missing $$p"; exit 1; }; done; true

# A declaration in the file its own module names is emitted under its plain
# identifier, constructors included; that is what SplitMid.ml refers to.
GREP_SplitLo += "^type color ="
GREP_SplitLo += "| Red"
GREP_SplitLo += "let flip (c : color) : color"
GREP_SplitLo += "let add_one"
# A cross-file reference is qualified by the module, and never by an [open].
GREP_SplitHi += "SplitMid.name"
GREP_SplitHi += "SplitLo.flip"
GREP_SplitHi += "SplitLo.Red"
GREP_SplitHi += "let _ = main ()"

$(OUTPUT_DIR)/SplitHi.exe: $(OUTPUT_DIR)/SplitHi.ml SplitMid.ml
	$(call msg, "OCAMLOPT", SplitHi)
	$(FSTAR_EXE) --ocamlopt -I $(OUTPUT_DIR) \
	  $(OUTPUT_DIR)/SplitLo.ml SplitMid.ml $(OUTPUT_DIR)/SplitHi.ml -o $@

all: $(OUTPUT_DIR)/SplitHi.out.diff

all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .out.diff, $(CUSTARD_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .rejected, $(REJECT_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .roots, $(ROOT_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .dcran, $(C_TESTS)))

# Only when karamel is on the PATH: the OCaml backend is always testable, the
# C one needs a toolchain.
ifneq ($(shell command -v krml 2>/dev/null),)
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .cran, $(KRML_TESTS)))
endif

# The result type is peeled down to the last arrow, through both abbreviations.
GREP_RetArity += ") : Prims.int ="

# Section 8.2: a realized type's OCaml shape is the hand-written one.
# [FStar.Pervasives.dtuple3] is a one-constructor *variant* there, so there is
# no record to recover and no field to project.  Its second and third
# parameters are arities -- [a -> Type] and [a -> b a -> Type] -- and section
# 18.2 is what lets them be written honestly: every argument they take is a
# value, so each denotes one target type and [bool] and [string] are it.  They
# used to be [Obj.t].
FLAGS_Realized    = --warn_error -366
GREP_Realized     = "FStar_Pervasives.Mkdtuple3" \
                    "(Prims.int, bool, string) FStar_Pervasives.dtuple3" \
                    "match d with"
# No record recovery, no projection, and the erased GTot call is gone.
# No record recovery, no projection, no erased GTot call -- and no [Obj.t].
NOGREP_Realized   = "u__1" "gmagic" "Obj.t"
