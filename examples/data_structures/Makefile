FSTAR_HOME = ../..

OUT_DIR = .output
CACHE_DIR = .cache

FSTAR_FILES = $(wildcard *.fst)

include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_INCLUDES = $(addprefix --include ,$(INCLUDES))

FSTAR_FLAGS = \
  --cache_checked_modules \
  --already_cached 'Prims FStar' \
  --cmi \
  --odir $(OUT_DIR) \
  --cache_dir $(CACHE_DIR) \
  $(FSTAR_INCLUDES) 

#TODO: use Makefile.include or Makefile.tmpl
FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS) $(OTHERFLAGS)

all: verify-all

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

depend: .depend

EXTRACT = RBTreeIntrinsic

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) --extract '$(EXTRACT)' > $@

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

$(OUT_DIR)/RBTreeIntrinsic.cmx:
	@echo 'let _ = test()' >> $(OUT_DIR)/$(EXTRACT).ml
	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/test.exe: $(subst .ml,.cmx,$(ALL_ML_FILES)) | $(OUT_DIR)
	$(OCAMLOPT) -I $(OUT_DIR) -o $(OUT_DIR)/test.exe $(subst .ml,.cmx,$(ALL_ML_FILES))

test: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR) .depend

.PHONY: depend verify-all test clean
