FSTAR_HOME ?= ../..

OUT_DIR = .output
CACHE_DIR = .cache

ROOTS = RBTree.fst

include $(FSTAR_HOME)/ulib/ml/Makefile.include

INCLUDES = \
  $(FSTAR_HOME)/ulib/.cache

FSTAR_INCLUDES = $(addprefix --include ,$(INCLUDES))

FSTAR_FLAGS = \
  --cache_checked_modules \
  --already_cached 'Prims FStar' \
  --cmi \
  --odir $(OUT_DIR) \
  --cache_dir $(CACHE_DIR) \
  $(FSTAR_INCLUDES) 

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS) $(OTHERFLAGS)

all: verify-all

verify-all: $(CACHE_DIR) $(CACHE_DIR)/RBTree.fst.checked

depend: .depend

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > $@

include .depend

$(CACHE_DIR) $(OUT_DIR):
	mkdir -p $@

$(CACHE_DIR)/%.checked: | $(CACHE_DIR) .depend
	$(FSTAR) $< && \
	touch -c $@

$(OUT_DIR)/%.ml: | $(OUT_DIR) .depend
	$(FSTAR) --codegen OCaml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

%.cmx:
	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/RBTree.cmx:
	@echo 'let _ = test()' >> $(OUT_DIR)/RBTree.ml
	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/test.exe: $(subst .ml,.cmx,$(ALL_ML_FILES)) | $(OUT_DIR)
	$(OCAMLOPT) -I $(OUT_DIR) -o $(OUT_DIR)/test.exe $(subst .ml,.cmx,$(ALL_ML_FILES))

test: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR) .depend
