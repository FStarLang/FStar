FSTAR_ROOT ?= ../../..
PULSE_ROOT ?= $(FSTAR_ROOT)/pulse

# Pulse programs can only be *parsed* by a compiler with the Pulse syntax
# extension linked in, which is stage3.  So, unlike ../Makefile, these tests
# run against the installed stage3 compiler, and are not part of the default
# `make test` of tests/custard.
STAGE3 ?= 1
FSTAR_EXE ?= $(FSTAR_ROOT)/stage3/out/bin/fstar.exe

include $(PULSE_ROOT)/mk/test.mk

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
C_TESTS += PulseHashTable
C_TESTS += CborBoundarySlice

# Section 5.6, escalated: neither of these -- and PulseHashTable in particular,
# which is the repr-over-erased-index style section 5.4 is about -- may lose
# the representation of a value.
WARN_ANY = --custard_warn_any --warn_error @367

$(OUTPUT_DIR)/%.custard.ml: $(CACHE_DIR)/%.fst.checked
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

$(OUTPUT_DIR)/%.custard.krml: $(CACHE_DIR)/%.fst.checked
	$(call msg, "CUSTARD-KRML", $(basename $(notdir $@)))
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard $(WARN_ANY) --custard_backend KrmlC $(KRML_FLAGS_$*) \
	  --custard_main $*.main $*.fst -o $@

# Section 20.  KrmlRust is a different backend and not a flag on this one: it
# models Pulse.Lib.Slice away, so this .krml does not hold the program the C
# column needs and the C column's does not hold the one Rust needs.
$(OUTPUT_DIR)/%.custard.rust.krml: $(CACHE_DIR)/%.fst.checked
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
	$(Q)krml -silent -fkeep-tuples -fno-box -skip-linking -backend rust \
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

$(OUTPUT_DIR)/%.dc: $(CACHE_DIR)/%.fst.checked
	$(call msg, "CUSTARD-C", $(basename $(notdir $@)))
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard $(WARN_ANY) --custard_backend C \
	  --custard_monomorphize_types true --custard_main $*.main $*.fst -o $@

$(OUTPUT_DIR)/%.dcexe: $(OUTPUT_DIR)/%.dc
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) -std=c11 -Wall -Wextra -Werror -x c $< -o $@

# Each of these programs' [main] checks its own answers and exits 0 if they
# are right, so running it is a test of the generated code and not only of the
# C compiler's willingness to accept it.
$(OUTPUT_DIR)/%.dcran: $(OUTPUT_DIR)/%.dcexe
	$(call msg, "RUN-C", $(basename $(notdir $@)))
	$(Q)$<
	$(Q)touch $@

$(OUTPUT_DIR)/%.cexe: $(OUTPUT_DIR)/%.custard.krml
	$(call msg, "KRML", $(basename $(notdir $@)))
	$(Q)krml -silent -skip-linking -tmpdir $(OUTPUT_DIR)/$*_c $<
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) $$(tr '\n' ' ' < $(OUTPUT_DIR)/$*_c/compile_flags.txt) \
	  -c $(OUTPUT_DIR)/$*_c/Custard.c -o $@

# Section 19.11.  A specification named as an explicit entry point.  Two
# assertions, and the negative one is the point: '--custard_entry' on an
# slprop-valued 'val' must say that it is a specification, not reject the
# recursive datatype that only ever indexes it.  This is the suite's one
# negative test, so it is a rule of its own rather than a GREP_TESTS entry.
$(OUTPUT_DIR)/PulseSpecRoot.specroot: $(CACHE_DIR)/PulseSpecRoot.fst.checked
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

all: $(OUTPUT_DIR)/PulseSpecRoot.specroot
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .grepped, $(GREP_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .mlchecked, $(OCAML_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .dcran, $(C_TESTS)))

ifneq ($(shell command -v krml 2>/dev/null),)
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .cexe, $(KRML_TESTS)))
ifneq ($(shell command -v rustc 2>/dev/null),)
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .rsran, $(RUST_TESTS)))
endif
endif
