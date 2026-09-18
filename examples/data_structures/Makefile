FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

HAS_OCAML ?= 1

ifneq (,$(HAS_OCAML))
all: $(OUTPUT_DIR)/RBTreeIntrinsic.exe
endif

# EXTRACT = RBTreeIntrinsic

# OCAML_DEFAULT_FLAGS += -I $(OUTPUT_DIR) -w -31

# $(OUTPUT_DIR)/test.exe: $(OUTPUT_DIR)/$(EXTRACT).ml
# 	@echo 'let _ = test()' >> $^
# 	$(FSTAR_EXE) --ocamlopt $^ -o $@

%.run: $(OUTPUT_DIR)/%.exe
	$(call msg, "RUN", $<)
	./$<
	touch $@

$(OUTPUT_DIR)/%.exe: $(OUTPUT_DIR)/%.ml
	$(call msg, "OCAMLOPT", $<)
	$(FSTAR_EXE) --ocamlopt $< -o $@

# Section 126.  Custard is whole-program and keyed on an entry point, so the
# program the old rule built by appending a call to the extracted module is
# built by *naming* that call: --custard_main is the definition the generated
# program invokes on startup.  Nothing else in the module reaches [test], and
# under --custard_entry_module it was dead code and dropped.

$(OUTPUT_DIR)/RBTreeIntrinsic.ml: $(CACHE_DIR)/RBTreeIntrinsic.fst.checked $(FSTAR_EXE)
	$(call msg, "EXTRACT", RBTreeIntrinsic.fst)
	$(FSTAR) --codegen Custard --custard_main RBTreeIntrinsic.test $< -o $@
