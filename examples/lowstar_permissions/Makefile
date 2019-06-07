OUTPUT_DIR    = .output
HINT_DIR      = .hints
GENERATED_DIR = pointers-c
OUT_DIR	      = pointers-c

.PHONY: all test stage1 stage2 clean distclean

all: compile-c

compile-c: $(GENERATED_DIR)/Makefile.include
	$(MAKE) -C $(GENERATED_DIR) -f Makefile.basic
compile-c: EXTRA+=-o libpointers.a

test-c: $(GENERATED_DIR)/Makefile.include | $(GENERATED_DIR)
	$(MAKE) -C $(GENERATED_DIR) -f Makefile.basic Test_Impl_Signal.exe
	$(GENERATED_DIR)/pointers.exe
test-c: EXTRA+=-o pointers.exe -add-include '"kremlib.h"'

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib


FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules  --odir $(OUTPUT_DIR) \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Pointer.fst

.PRECIOUS: %.krml

ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) --dep full $(ROOTS) --extract 'Pointer -FStar.Real' > $@
.PHONY: .FORCE
.FORCE:
endif
include .depend

$(HINT_DIR):
	mkdir -p $@

%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

$(GENERATED_DIR):
	mkdir -p $@

$(GENERATED_DIR_WASM):
	mkdir -p $@

KREMLIN=$(KREMLIN_HOME)/krml

# 2. Generation of .c files

$(GENERATED_DIR)/Makefile.include: EXTRA+=-fparentheses

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
%/Makefile.include: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) -skip-compilation \
	-no-prefix 'Pointer' \
	-bundle Prims -bundle LowStar.Endianness -bundle C.Endianness \
	-bundle FStar.* \
	-tmpdir $* \
	$(EXTRA) \
	$^

# 5. Targets for interactive mode

%.fst-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# 6. Clean targets

SHELL=/bin/bash

clean:
	rm -rf $(GENERATED_DIR) $(OUT_DIR)/*.exe $(OUT_DIR)/*.a
	rm -rf include/*.o include/*.d

clean-c:
	rm -rf $(GENERATED_DIR)/{*.{c,h},Makefile.include}

distclean: clean
	rm -rf $(OUT_DIR) $(OUTPUT_DIR) *.checked
