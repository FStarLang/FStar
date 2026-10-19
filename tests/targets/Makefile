# Compilation targets (doc/ref/targets.md).  Counter has one implementation
# per language (Counter-ocaml.fst, Counter-c.fst, Counter-model.fst) behind a
# common interface.  Uart has a common fallback, implementations for s2, for
# s2.qemu and for s3-c.  --dep full on all files verifies every file once, and
# extraction picks the most specific file implied by --target and --codegen.
SUBDIRS_ALL += neg plugin
SUBDIRS_CLEAN += neg plugin

RUN += Main.fst
# Main prints the name of the target it was extracted for, which is "c" (not
# "ocaml") under Cherry; Board.grep covers target selection for Cherry.
NO_CHERRY += Main.fst

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

# The C backend picks Counter-c.fst.
all: $(OUTPUT_DIR)/CName.c.grep
$(OUTPUT_DIR)/CName.c.grep: $(CACHE_DIR)/CName.fst.checked | $(ALL_CHECKED_FILES)
	$(call msg, "EXTRACT C", CName)
	$(FSTAR) --codegen C --custard_entry_module CName $< -o $(OUTPUT_DIR)/CName.c
	grep -q '"c"' $(OUTPUT_DIR)/CName.c
	! grep -q '"ocaml"' $(OUTPUT_DIR)/CName.c
	! grep -q '"model"' $(OUTPUT_DIR)/CName.c
	touch $@

# Uart under several configurations.
all: $(OUTPUT_DIR)/Board.grep
$(OUTPUT_DIR)/Board.grep: $(CACHE_DIR)/Board.fst.checked | $(ALL_CHECKED_FILES)
	$(call msg, "EXTRACT", Board)
	$(FSTAR) --codegen OCaml --custard_entry_module Board $< -o $(OUTPUT_DIR)/board_generic.ml
	grep -q '"generic"' $(OUTPUT_DIR)/board_generic.ml
	$(FSTAR) --codegen OCaml --target s2.qemu --custard_entry_module Board $< -o $(OUTPUT_DIR)/board_s2qemu.ml
	grep -q '"s2.qemu"' $(OUTPUT_DIR)/board_s2qemu.ml
	$(FSTAR) --codegen OCaml --target s2.silicon --custard_entry_module Board $< -o $(OUTPUT_DIR)/board_s2silicon.ml
	grep -q '"s2"' $(OUTPUT_DIR)/board_s2silicon.ml
	$(FSTAR) --codegen OCaml --target s3.silicon --custard_entry_module Board $< -o $(OUTPUT_DIR)/board_s3ocaml.ml
	grep -q '"generic"' $(OUTPUT_DIR)/board_s3ocaml.ml
	$(FSTAR) --codegen C --target s3.silicon --custard_entry_module Board $< -o $(OUTPUT_DIR)/board_s3c.c
	grep -q '"s3-c"' $(OUTPUT_DIR)/board_s3c.c
	$(FSTAR) --codegen Cherry --target s3.silicon --custard_entry_module Board $< -o $(OUTPUT_DIR)/board_s3cherry.c
	grep -q '"s3-c"' $(OUTPUT_DIR)/board_s3cherry.c
	touch $@

# --dep full finds the files of every target by itself: from Board and Main
# alone, which only reach the common interfaces of Uart and Counter.
all: $(OUTPUT_DIR)/DepFull.grep
$(OUTPUT_DIR)/DepFull.grep: Board.fst Main.fst
	$(call msg, "DEPEND", DepFull)
	mkdir -p $(OUTPUT_DIR)
	$(FSTAR) --dep full Board.fst Main.fst -o $(OUTPUT_DIR)/DepFull.depend
	for f in Uart.fst Uart-s2.fst Uart-s2.qemu.fst Uart-s3-c.fst \
	         Counter-ocaml.fst Counter-c.fst Counter-model.fst; do \
	  grep -q "$$f\.checked" $(OUTPUT_DIR)/DepFull.depend || { echo "missing $$f"; exit 1; }; \
	done
	touch $@
