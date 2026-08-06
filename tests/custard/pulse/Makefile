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

# The hash table is polymorphic, stores a closure in a runtime record, and is
# loaded from another module's implementation through its interface.  It does
# not go through the karamel backend: a closure in a data structure is the
# section 3.2 [Poly] case deferred to v2, and karamel rejects it.
GREP_TESTS += PulseHashTable
GREP_PulseHashTable += "pulse_Lib_HashTable_alloc"
GREP_PulseHashTable += "pulse_Lib_HashTable_insert"
GREP_PulseHashTable += "pulse_Lib_HashTable_lookup"
GREP_PulseHashTable += "while"
GREP_PulseHashTable += "Array.make"
NOGREP_PulseHashTable += "Obj.magic"
NOGREP_PulseHashTable += "PulseCore"
NOGREP_PulseHashTable += "prims_unit"

# The generated OCaml must also type-check: these programs are large enough
# that a grep test alone would miss most of what can go wrong in a signature.
OCAML_TESTS += PulseBasic
OCAML_TESTS += PulseHashTable

# Same modules, through the karamel backend: krml must accept the output and
# the C compiler must build it.
KRML_TESTS += PulseBasic

$(OUTPUT_DIR)/%.custard.ml: $(CACHE_DIR)/%.fst.checked
	$(call msg, "CUSTARD", $(basename $(notdir $@)))
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen Custard --custard_main $*.main $*.fst -o $@

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
	$(Q)$(FSTAR) --codegen Custard --custard_backend Krml --custard_main $*.main \
	  $*.fst -o $@

$(OUTPUT_DIR)/%.cexe: $(OUTPUT_DIR)/%.custard.krml
	$(call msg, "KRML", $(basename $(notdir $@)))
	$(Q)krml -silent -skip-linking -tmpdir $(OUTPUT_DIR)/$*_c $<
	$(call msg, "CC", $(basename $(notdir $@)))
	$(Q)$(CC) $$(tr '\n' ' ' < $(OUTPUT_DIR)/$*_c/compile_flags.txt) \
	  -c $(OUTPUT_DIR)/$*_c/Custard.c -o $@

all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .grepped, $(GREP_TESTS)))
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .mlchecked, $(OCAML_TESTS)))

ifneq ($(shell command -v krml 2>/dev/null),)
all: $(addprefix $(OUTPUT_DIR)/, $(addsuffix .cexe, $(KRML_TESTS)))
endif
