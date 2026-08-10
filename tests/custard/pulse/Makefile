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
GREP_PulseHashTable += "pulse_Lib_HashTable_Type_ht_t = { sz : FStar_SizeT.t;"
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

# Same modules again, through the direct-to-C backend: no krml, no krmllib,
# just a C11 compiler with the warnings turned on, and then run.  PulseHashTable is the
# demanding one -- arrays, a struct-valued cell, and a hash function stored in
# a record, which becomes a C function pointer.
C_TESTS += PulseBasic
C_TESTS += PulseHashTable

# Section 5.6, escalated: neither of these -- and PulseHashTable in particular,
# which is the repr-over-erased-index style section 5.4 is about -- may lose
# the representation of a value.
WARN_ANY = --custard_warn_any --warn_error @366

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
	$(Q)$(FSTAR) --codegen Custard $(WARN_ANY) --custard_backend Krml --custard_main $*.main \
	  $*.fst -o $@

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

all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .grepped, $(GREP_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .mlchecked, $(OCAML_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .dcran, $(C_TESTS)))

ifneq ($(shell command -v krml 2>/dev/null),)
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .cexe, $(KRML_TESTS)))
endif
