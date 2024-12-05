FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

HAS_OCAML ?= 1

ifneq (,$(HAS_OCAML))
all: $(OUTPUT_DIR)/RBTreeIntrinsic_patched.exe
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

$(OUTPUT_DIR)/%.ml: %.fst
	$(call msg, "EXTRACT", $<)
	$(FSTAR) --codegen OCaml --extract $(basename $@) $<

$(OUTPUT_DIR)/RBTreeIntrinsic_patched.ml: $(OUTPUT_DIR)/RBTreeIntrinsic.ml
	cp -f $< $@
	echo 'let _ = test()' >> $@
