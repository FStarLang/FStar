# Compilation targets: Counter has one implementation per target
# (Counter-ocaml.fst, Counter-c.fst, Counter-model.fst) behind a common
# interface.  --dep full on all files verifies every target, and extraction
# picks the implementation of the backend's target.
SUBDIRS_ALL += neg plugin
SUBDIRS_CLEAN += neg plugin

RUN += Main.fst

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
