include mk/common.mk

$(call need_exe, FSTAR_EXE, fstar.exe to be used)
$(call need_dir_mk, CACHE_DIR, directory for checked files)
$(call need_dir_mk, OUTPUT_DIR, directory for extracted OCaml files)
$(call need_dir, SRC, source directory)
$(call need, TAG, a tag for the .depend; to prevent clashes. Sorry.)
$(call need, ROOTS, a list of roots for the dependency analysis)
# Optional: DEPFLAGS
#
# TOUCH (optional): pass a file to touch everytime something is
# performed. We also create it if it does not exist (this simplifies
# external use)
ifneq ($(TOUCH),)
_ != $(shell [ -f "$(TOUCH)" ] || touch $(TOUCH))
endif

maybe_touch=$(if $(TOUCH), touch $(TOUCH))

EXTENSION := .checked
MSG := CHECK

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR)
	rm -rf $(OUTPUT_DIR)

.PHONY: verify
verify: all-checked

FSTAR_OPTIONS += --odir "$(OUTPUT_DIR)"
FSTAR_OPTIONS += --cache_dir "$(CACHE_DIR)"
FSTAR_OPTIONS += --include "$(SRC)"
FSTAR_OPTIONS += $(OTHERFLAGS)

ifeq ($(ADMIT),1)
FSTAR_OPTIONS += --admit_smt_queries true
endif

FSTAR := $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

%$(EXTENSION): FF=$(notdir $<)
%$(EXTENSION):
	$(call msg, $(MSG), $(FF))
	$(FSTAR) --already_cached ',*' -c $< -o $@
	touch -c $@ # update timestamp even if cache hit
	$(maybe_touch)

DEPSTEM := $(CACHE_DIR)/.depend$(TAG)

# This file's timestamp is updated whenever anything in $(SRC)
# changes, forcing rebuilds downstream. Note that deleting a file
# will bump the directories timestamp, we also catch that.
.PHONY: .force
$(DEPSTEM).touch: .force
	mkdir -p $(dir $@)
	[ -e $@ ] || touch $@
	# Ignore anything in CACHE_DIR and OUTPUT_DIR, to avoid rebuilding .depend in a loop
	find $(SRC) -path $(CACHE_DIR) -prune -o -path $(OUTPUT_DIR) -prune -o -newer $@ -exec touch $@ \; -quit

$(DEPSTEM): $(DEPSTEM).touch
	$(call msg, "DEPEND", $(SRC))
	$(FSTAR) --dep full $(ROOTS) $(DEPFLAGS) -o $@

depend: $(DEPSTEM)
include $(DEPSTEM)

depgraph: $(DEPSTEM).pdf
$(DEPSTEM).pdf: $(DEPSTEM) .force
	$(call msg, "DEPEND GRAPH", $(SRC))
	$(FSTAR) --dep graph $(ROOTS) $(DEPFLAGS) -o $(DEPSTEM).graph
	$(FSTAR_ROOT)/.scripts/simpl_graph.py $(DEPSTEM).graph > $(DEPSTEM).simpl
	dot -Tpdf -o $@ $(DEPSTEM).simpl
	echo "Wrote $@"

all-checked: $(ALL_CHECKED_FILES)

# stage0 predates --codegen OCaml for Custard.  A stage0 bump overwrites this
# file with generic-1.mk, which drops this line.
CUSTARD_CODEGEN := --codegen Custard --custard_backend OCaml

# Extraction: a single whole-program Custard pass.  Included last, because its rule's prerequisite is the list of
# checked files the .depend above defines.
include mk/custard-extract.mk
