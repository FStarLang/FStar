FSTAR_HOME ?= ../..

include $(FSTAR_HOME)/ulib/ml/Makefile.include

OUT_DIR   = out
CACHE_DIR = cache
ROOTS     = Test.fst

FSTAR_FLAGS = $(OTHERFLAGS) --cmi --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) \
  --cache_checked_modules --already_cached 'Prims FStar'

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

.PHONY: all test clean

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) test

# 1. Extract .ml files
# - generate the F* dependency graph of $(ROOTS) with `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .ml file in parallel
.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > $@

include .depend

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

# 2. Compile all .ml files to .cmx and link them to get an executable
$(OUT_DIR):
	mkdir -p $@

$(OUT_DIR)/%.ml: | .depend
	$(FSTAR) --codegen OCaml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

%.cmx:
	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/test.exe: $(subst .ml,.cmx,$(ALL_ML_FILES)) | $(OUT_DIR)
	$(OCAMLOPT) -I $(OUT_DIR) -o $(OUT_DIR)/test.exe $(subst .ml,.cmx,$(ALL_ML_FILES))

test: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR)
