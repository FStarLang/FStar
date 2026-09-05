FSTAR_ROOT ?= ../../..
PULSE_ROOT ?= $(FSTAR_ROOT)/pulse

# Pulse programs can only be *parsed* by a compiler with the Pulse syntax
# extension linked in, which is stage3.  So, unlike ../Makefile, these tests
# run against the installed stage3 compiler, and are not part of the default
# `make test` of tests/custard: they are reached from the root Makefile's
# _test_pulse instead, which only test-3 runs.
STAGE3 ?= 1
FSTAR_EXE ?= $(FSTAR_ROOT)/stage3/out/bin/fstar.exe

include $(PULSE_ROOT)/mk/test.mk

# Section 62.1.  Same discovery as tests/custard and for the same reason:
# CI passes KRML_EXE= and never puts krml on the PATH, so a `command -v
# krml` guard silently skipped both karamel legs of this suite.
KRML_CANDIDATES := $(KRML_EXE) $(dir $(FSTAR_EXE))krml $(FSTAR_ROOT)/karamel/out/bin/krml
KRML_FOUND      := $(firstword $(wildcard $(KRML_CANDIDATES)) $(shell command -v krml 2>/dev/null))
ifneq ($(KRML_FOUND),)
  override KRML_EXE := $(KRML_FOUND)
endif

# Each of these is extracted with --codegen Custard from its 'main'; the
# generated OCaml must contain every GREP_<name> pattern and none of the
# NOGREP_<name> ones.  We check the shape of the output rather than running
# it: Pulse has no I/O library, so a Pulse program cannot print anything.
GREP_TESTS += PulseBasic
GREP_PulseBasic += "while"
GREP_PulseBasic += "FStar_SizeT.lt"
GREP_PulseBasic += "FStar_SizeT.add"
GREP_PulseBasic += "Array.make 4"
NOGREP_PulseBasic += "Pulse_Lib"
NOGREP_PulseBasic += "PulseCore"
NOGREP_PulseBasic += "Obj.magic"
# Section 8.4: 'let mut' is an OCaml ref, not a one-element array.
GREP_PulseBasic += "(ref (FStar_SizeT.uint_to_t"
GREP_PulseBasic += "(!(i))"
NOGREP_PulseBasic += "Array.make 1"

# The hash table is polymorphic, stores a closure in a runtime record, and is
# loaded from another module's implementation through its interface.  It stays
# polymorphic all the way into karamel, which monomorphizes it itself.
GREP_TESTS += PulseHashTable
GREP_PulseHashTable += "pulse_Lib_HashTable_alloc"
GREP_PulseHashTable += "pulse_Lib_HashTable_insert"
GREP_PulseHashTable += "pulse_Lib_HashTable_lookup"
GREP_PulseHashTable += "while"
GREP_PulseHashTable += "Array.make"
NOGREP_PulseHashTable += "Obj.magic"
NOGREP_PulseHashTable += "PulseCore"
NOGREP_PulseHashTable += "prims_unit"
# Section 5.5: 'ht_t' comes back as a record rather than a one-constructor
# variant, and the two 'unreachable' branches are gone.
GREP_PulseHashTable += "pulse_Lib_HashTable_Type_ht_t = {"
GREP_PulseHashTable += "  sz : FStar_SizeT.t;"
GREP_PulseHashTable += "(ht).sz"
NOGREP_PulseHashTable += "Mkht_t"
NOGREP_PulseHashTable += "failwith"
GREP_PulseHashTable += "(ref false)"
GREP_PulseHashTable += "(u__break) := true"
NOGREP_PulseHashTable += "Array.make 1"

# The generated OCaml must also type-check: these programs are large enough
# that a grep test alone would miss most of what can go wrong in a signature.
OCAML_TESTS += PulseBasic
OCAML_TESTS += PulseHashTable
OCAML_TESTS += PulseFnPtrRet

# Same modules, through the karamel backend: krml must accept the output and
# the C compiler must build it.
KRML_TESTS += PulseBasic
KRML_TESTS += PulseHashTable
KRML_TESTS += PulseSlice
# PulseSlice needs one extra flag on the C column.  Pulse.Lib.Slice.split is
# polymorphic and returns a tuple, so with types compiled uniformly (section
# 6) the .krml holds 'tuple2<slice<'t>, slice<'t>>' -- a type application whose
# arguments are not ground.  karamel's own monomorphizer only instantiates
# closed applications, so its checker then reports tuple2 as an undefined
# type.  Asking Custard to monomorphize the types too sidesteps it.  This is
# not specific to slices and not new in section 20; PulseSlice is simply the
# first test in this suite to return a tuple from a polymorphic function.
KRML_FLAGS_PulseSlice += --custard_monomorphize_types true

# Section 20.  The Rust column, which exists for one reason: karamel compiles
# Pulse.Lib.Slice to Rust's own borrowed slice, and only if Custard leaves the
# type alone for it to recognize.  Compiled *and run*, because the bug this
# closes was a miscompilation and not a build failure -- with the borrows
# silenced the generated code wrote through a temporary and read back zeroes
# (section 19.15), which a program that checks its own answers catches and a
# program that merely builds does not.
RUST_TESTS += PulseSlice
RUST_TESTS += PulseSliceRec
# A reduced CBOR well-formedness checker over a slice, run against a curated
# corpus of 48 boundary vectors.  Unlike the tests above it does not merely
# build: it writes each vector through the slice and checks its own answer,
# so a borrow compiled as an owning Box (section 19.15) fails it rather than
# passing silently.  The corpus is mutation-adequate against the extracted C
# -- see CborBoundarySlice.mutants.py, which reproduces the numbers.
RUST_TESTS += CborBoundarySlice

# Same modules again, through the direct-to-C backend: no krml, no krmllib,
# just a C11 compiler with the warnings turned on, and then run.  PulseHashTable is the
# demanding one -- arrays, a struct-valued cell, and a hash function stored in
# a record, which becomes a C function pointer.
C_TESTS += PulseBasic
# Section 58: the pure condition is spelled in the loop header.
CGREP_PulseBasic += "while (i < n)"
CNOGREP_PulseBasic += "while (true)"
C_TESTS += PulseHashTable
# Section 58, the other half of that pair, and the reason it is worth a grep:
# these two conditions genuinely need statements (a [_break] flag is tested
# to produce the condition value), so they must *keep* [while (true)] with
# the leading break.  Asserting only the rewritten form would leave a
# rewrite that fired too eagerly undetected.
CGREP_PulseHashTable += "while (true)"
C_TESTS += CborBoundarySlice
# Section 30: a maker that returns a one-field record collapses to a function
# returning a function pointer, and its callers must stay saturated.
C_TESTS += PulseFnPtrRet

# Sections 33.1-33.3.  [@@@monomorphize] on the binder of a Pulse [fn]: the
# annotation is on the lambda and not on the elaborated arrow type, and the
# [fn] itself arrives eta-contracted.  Both had to be fixed for the
# specialization to happen at all, so the assertion is that it did -- there is
# a specialized name, no function pointer, and the program checks its own
# answer when it runs.
C_TESTS += PulseMono
CGREP_PulseMono += "PulseMono_apply_twice__add_mod"
CGREP_PulseMono += "static void PulseMono_add_k(uint32_t k, uint32_t *eta)"
CNOGREP_PulseMono += "(*f)"

# Section 34.3.  A Pulse [fn] block argument that captures a [ref] and a value
# from the caller's frame, driven by a loop combinator.  The specialized loop
# must take both captures as parameters -- there is no closure in the output --
# and the [slprop] invariant must not survive at all.  The program checks its
# own answer, so a capture from the wrong frame is a nonzero exit.
C_TESTS += PulseForCapture
CGREP_PulseForCapture += "PulseForCapture_for_upto__0(uint32_t *"
CGREP_PulseForCapture += "PulseForCapture_for_upto__0(r, k,"
# Section 58: the loop is here, and its condition is pure, so it is spelled
# as a C programmer would spell it rather than as [while (true)] with a
# leading [break].  A stronger assertion than the old "while (true)": that
# one held whatever the condition did.
CGREP_PulseForCapture += "while (i < n)"
CNOGREP_PulseForCapture += "while (true)"
CNOGREP_PulseForCapture += "slprop"
CNOGREP_PulseForCapture += "(*body)"

# Section 41.1.  Pulse.Lib.ArrayPtr.memcpy is the only rule that produces a
# BufBlit, and until this file no test reached it, so the printer case had
# never printed anything.  The length position is where a redundant pair
# appears, and only when the length is already a group, which a literal is.
#
# Section 59: the length is now a bare [2] -- the [sizeof] it multiplies is
# a [size_t], so the other operand fixes the type -- and section 59.3's
# [is_atom] keeps [group] from putting the pair back.  The CNOGREP is kept
# in both spellings, since 41.1's hazard is the pair and not the cast.
C_TESTS += ExtBuf
# Section 60.2.  The cast is the assertion, and the C++ leg added above is
# what enforces it: extbuf_base is a macro yielding void *, which C converts
# implicitly and C++ refuses.  Removing the cast from PrintC leaves this
# file compiling clean under gcc and failing under g++.
CGREP_ExtBuf = "(uint8_t *)extbuf_base"
# The returned pointer must be *bound* to a typed variable.  Discarding it
# would emit a (void) cast, which C++ accepts with or without the fix.
CGREP_ExtBuf += "uint8_t *"

C_TESTS += PulseBlit
CGREP_PulseBlit += "memmove("
CGREP_PulseBlit += "2 * sizeof(uint8_t)"
CNOGREP_PulseBlit += "(((size_t)2ULL))"
CNOGREP_PulseBlit += "(2) * sizeof"

# Section 5.6, escalated: neither of these -- and PulseHashTable in particular,
# which is the repr-over-erased-index style section 5.4 is about -- may lose
# the representation of a value.
WARN_ANY = --custard_warn_any --warn_error @367

# Section 49.6.  As in ../Makefile: every rule that runs $(FSTAR) depends on
# the binary, so that a rebuilt compiler invalidates the generated output
# rather than leaving yesterday's beside a today's binary.

$(OUTPUT_DIR)/%.custard.ml: $(CACHE_DIR)/%.fst.checked $(FSTAR_EXE)
	$(call msg, "CUSTARD", $(basename $(notdir $@)))
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard $(WARN_ANY) --custard_main $*.main $*.fst -o $@

$(OUTPUT_DIR)/%.grepped: $(OUTPUT_DIR)/%.custard.ml
	$(call msg, "GREP", $(basename $(notdir $@)))
	$(Q)for p in $(GREP_$*); do \
	  grep -q -- "$$p" $< \
	    || { echo "ERROR: $* output is missing $$p"; exit 1; }; done
	$(Q)for p in $(NOGREP_$*); do \
	  grep -q -- "$$p" $< \
	    && { echo "ERROR: $* output should not contain $$p"; exit 1; }; done; true
	$(Q)touch $@

$(OUTPUT_DIR)/%.mlchecked: $(OUTPUT_DIR)/%.custard.ml
	$(call msg, "OCAMLOPT", $(basename $(notdir $@)))
	$(Q)mkdir -p $(OUTPUT_DIR)/$*_ml
	$(Q)cp $< $(OUTPUT_DIR)/$*_ml/$*.ml
	$(Q)cd $(OUTPUT_DIR)/$*_ml && $(abspath $(FSTAR_EXE)) --ocamlopt $*.ml -o $*.exe
	$(Q)touch $@

$(OUTPUT_DIR)/%.custard.krml: $(CACHE_DIR)/%.fst.checked $(FSTAR_EXE)
	$(call msg, "CUSTARD-KRML", $(basename $(notdir $@)))
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard $(WARN_ANY) --custard_backend KrmlC $(KRML_FLAGS_$*) \
	  --custard_main $*.main $*.fst -o $@

# Section 20.  KrmlRust is a different backend and not a flag on this one: it
# models Pulse.Lib.Slice away, so this .krml does not hold the program the C
# column needs and the C column's does not hold the one Rust needs.
$(OUTPUT_DIR)/%.custard.rust.krml: $(CACHE_DIR)/%.fst.checked $(FSTAR_EXE)
	$(call msg, "CUSTARD-KRML-RUST", $(basename $(notdir $@)))
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard $(WARN_ANY) --custard_backend KrmlRust --custard_main $*.main \
	  $*.fst -o $@

# -fkeep-tuples is not optional here and is part of what section 20 documents:
# karamel's split_at hook destructures a real tuple, and without the flag the
# tuple has already become a struct by the time the Rust backend sees it.
#
# -fno-box is section 20.6.  karamel sorts a struct holding pointers into one
# of two disjoint sets: returned by value, so it owns its pointees and they
# become Box; or not returned, so it borrows them and the struct gains a
# lifetime.  A slice fits neither -- it is a borrow by construction and cannot
# be owned -- so a *returned* struct with a slice field comes out as
# `struct view { bytes: &[u8] }`, a borrow in a type that binds no lifetime,
# which is E0106.  -fno-box empties the returned set and every such struct
# gets its lifetime.  A karamel-side bug, and this is the workaround.
$(OUTPUT_DIR)/%.rs: $(OUTPUT_DIR)/%.custard.rust.krml
	$(call msg, "KRML-RUST", $(basename $(notdir $@)))
	$(Q)rm -rf $(OUTPUT_DIR)/$*_rs
	$(Q)$(KRML_EXE) -silent -fkeep-tuples -fno-box -skip-linking -backend rust \
	  -tmpdir $(OUTPUT_DIR)/$*_rs $<
	$(Q)sed 's/^pub fn main()/pub fn krml_main()/' $(OUTPUT_DIR)/$*_rs/*.rs > $@
	$(Q)grep -q '^pub fn krml_main()' $@ || \
	  { echo "ERROR: $*: krml did not emit 'main' in the generated crate"; exit 1; }
	@# The whole point of the exercise: a slice must be a borrow, not an
	@# owning Box, or every write through it lands in a temporary.
	$(Q)grep -q 'Box<' $@ \
	  && { echo "ERROR: $*: a slice was compiled to an owning Box"; exit 1; }; true
	$(Q)echo 'fn main() { std::process::exit(krml_main() as i32) }' >> $@

$(OUTPUT_DIR)/%.rsran: $(OUTPUT_DIR)/%.rs
	$(call msg, "RUSTC", $(basename $(notdir $@)))
	$(Q)rustc --edition 2021 -A warnings -o $(OUTPUT_DIR)/$*.rsexe $<
	$(call msg, "RUN-RUST", $(basename $(notdir $@)))
	$(Q)$(OUTPUT_DIR)/$*.rsexe
	$(Q)touch $@

$(OUTPUT_DIR)/%.dc: $(CACHE_DIR)/%.fst.checked $(FSTAR_EXE)
	$(call msg, "CUSTARD-C", $(basename $(notdir $@)))
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard $(WARN_ANY) --custard_backend C \
	  --custard_monomorphize_types true --custard_main $*.main $*.fst -o $@
	@# Section 35.3.  These were set here for two rounds and consulted by
	@# nothing, which is M10-phi-phi's bug in a second directory: an
	@# assertion nobody runs is worse than no assertion, because it reads
	@# like one.  Over the header as well as the source, as in tests/custard.
	$(Q)for p in $(CGREP_$*); do \
	  grep -qF -- "$$p" $@ $(basename $@).h \
	    || { echo "ERROR: $* C output is missing $$p"; exit 1; }; done
	$(Q)for p in $(CNOGREP_$*); do \
	  grep -qF -- "$$p" $@ $(basename $@).h \
	    && { echo "ERROR: $* C output should not contain $$p"; exit 1; }; done; true
	$(Q)python3 $(CURDIR)/../checkgroup.py $@ $(basename $@).h

$(OUTPUT_DIR)/%.dcexe: $(OUTPUT_DIR)/%.dc $(OUTPUT_DIR)/%.dcxx
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) -std=c11 -Wall -Wextra -Werror -I$(CURDIR) -x c $< -o $@

# Section 60.1.  The C++ leg of section 47.1, which existed only in
# tests/custard and so had never been run over any of the output in this
# directory -- which is the output that matters more for it.  A C++
# disagreement is about declarations, scope and implicit conversions, and
# this is where the tagged unions, the nested structs, the function
# pointers and the pointer-returning externs are.  The every-push suite
# next door is mostly scalars.
#
# It found nothing: all seven units compiled clean as C++ the first time.
# That is the right outcome and not a reason to leave the leg out --- 47.1's
# bug (an enum nested in a struct scopes its enumerators differently in the
# two languages) was invisible to a C-only suite for the same reason it
# would be invisible here, and Kuiper consumes this backend through nvcc,
# which is C++.
$(OUTPUT_DIR)/%.dcxx: $(OUTPUT_DIR)/%.dc
	$(call msg, "CXX", $(basename $(notdir $@)))
	$(Q)$(CXX) -std=c++17 -Wall -Werror -I$(CURDIR) -fsyntax-only -x c++ $<
	$(Q)touch $@

# Each of these programs' [main] checks its own answers and exits 0 if they
# are right, so running it is a test of the generated code and not only of the
# C compiler's willingness to accept it.
$(OUTPUT_DIR)/%.dcran: $(OUTPUT_DIR)/%.dcexe
	$(call msg, "RUN-C", $(basename $(notdir $@)))
	$(Q)$<
	$(Q)touch $@

$(OUTPUT_DIR)/%.cexe: $(OUTPUT_DIR)/%.custard.krml
	$(call msg, "KRML", $(basename $(notdir $@)))
	$(Q)$(KRML_EXE) -silent -skip-linking -tmpdir $(OUTPUT_DIR)/$*_c $<
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) $$(tr '\n' ' ' < $(OUTPUT_DIR)/$*_c/compile_flags.txt) \
	  -c $(OUTPUT_DIR)/$*_c/Custard.c -o $@

# Section 19.11.  A specification named as an explicit entry point.  Two
# assertions, and the negative one is the point: '--custard_entry' on an
# slprop-valued 'val' must say that it is a specification, not reject the
# recursive datatype that only ever indexes it.  This is the suite's one
# negative test, so it is a rule of its own rather than a GREP_TESTS entry.
$(OUTPUT_DIR)/PulseSpecRoot.specroot: $(CACHE_DIR)/PulseSpecRoot.fst.checked $(FSTAR_EXE)
	$(call msg, "CUSTARD-C", PulseSpecRoot)
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard --custard_backend C \
	  --custard_entry_module PulseSpecRoot PulseSpecRoot.fst \
	  -o $(OUTPUT_DIR)/PulseSpecRoot.c
	$(Q)grep -q 'PulseSpecRoot_size' $(OUTPUT_DIR)/PulseSpecRoot.c \
	  || { echo "ERROR: PulseSpecRoot.c is missing PulseSpecRoot_size"; exit 1; }
	$(Q)grep -q 'tree' $(OUTPUT_DIR)/PulseSpecRoot.c \
	  && { echo "ERROR: PulseSpecRoot.c should not mention tree"; exit 1; }; true
	$(Q)$(CC) -std=c11 -Wall -Wextra -Werror -c -x c \
	  $(OUTPUT_DIR)/PulseSpecRoot.c -o $(OUTPUT_DIR)/PulseSpecRoot.o
	$(Q)for e in rep rep_abs; do \
	  $(FSTAR) --codegen Custard --custard_backend C \
	    --custard_entry PulseSpecRoot.$$e PulseSpecRoot.fst \
	    -o $(OUTPUT_DIR)/PulseSpecRoot_$$e.c > $(OUTPUT_DIR)/$$e.out 2>&1; \
	  grep -q 'is a specification, not code' $(OUTPUT_DIR)/$$e.out \
	    || { echo "ERROR: --custard_entry PulseSpecRoot.'$$e' did not report a \
specification:"; cat $(OUTPUT_DIR)/$$e.out; exit 1; }; done
	$(Q)touch $@

ALL_TEST_NAMES := $(GREP_TESTS) $(OCAML_TESTS) $(C_TESTS) \
                  $(KRML_TESTS) $(RUST_TESTS)

# Section 35.3.  A setting whose name matches no registered test.
#
# [CGREP_PulseForCapture] was set in pulse/Makefile for two rounds and read by
# no recipe, and M10-phi-phi was the same bug from the other side: a test with
# settings but no registration.  Both are silent, and both read like coverage
# that does not exist.  Any name here that is not in a test list is one or the
# other.  Recursively expanded, so that [.VARIABLES] is complete by the time a
# recipe asks.
SETTING_PREFIXES := FLAGS GREP NOGREP EGREP NOEGREP CGREP CNOGREP CODE
ORPHAN_SETTINGS = $(strip $(foreach p,$(SETTING_PREFIXES),\
  $(foreach v,$(filter $(p)_%,$(.VARIABLES)),\
    $(if $(filter $(patsubst $(p)_%,%,$(v)),$(ALL_TEST_NAMES) TESTS),,$(v)))))

.PHONY: check-settings
check-settings:
	$(Q)test -z "$(ORPHAN_SETTINGS)" || { \
	  echo "ERROR: setting(s) for no registered test: $(ORPHAN_SETTINGS)"; \
	  echo "Either register the test, or delete the setting."; exit 1; }

all: check-settings

all: $(OUTPUT_DIR)/PulseSpecRoot.specroot
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .grepped, $(GREP_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .mlchecked, $(OCAML_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .dcran, $(C_TESTS)))

ifneq ($(KRML_FOUND),)
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .cexe, $(KRML_TESTS)))
ifneq ($(shell command -v rustc 2>/dev/null),)
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .rsran, $(RUST_TESTS)))
endif
endif
