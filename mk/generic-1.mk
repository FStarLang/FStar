include mk/common.mk

$(call need_exe, FSTAR_EXE, fstar.exe to be used)
$(call need_dir_mk, CACHE_DIR, directory for checked files)
$(call need_dir_mk, OUTPUT_DIR, directory for extracted OCaml files)
$(call need, CODEGEN, backend (OCaml / Plugin))
$(call need_dir, SRC, source directory)
$(call need, TAG, a tag for the .depend; to prevent clashes. Sorry.)
$(call need, ROOTS, a list of roots for the dependency analysis)
# Optional: EXTRACT, DEPFLAGS
#
# TOUCH (optional): pass a file to touch everytime something is
# performed. We also create it if it does not exist (this simplifies
# external use)
ifneq ($(TOUCH),)
_ != $(shell [ -f "$(TOUCH)" ] || touch $(TOUCH))
endif

maybe_touch=$(if $(TOUCH), touch $(TOUCH))

# This is to support both --lax and non --lax clients.
EXTENSION := $(if $(findstring --lax,$(FSTAR_OPTIONS)),.checked.lax,.checked)
MSG := $(if $(findstring --lax,$(FSTAR_OPTIONS)),LAXCHECK,CHECK)

ifeq ($(CODEGEN),FSharp)
EEXT=fs
else ifeq ($(CODEGEN),krml)
EEXT=krml
else
EEXT=ml
endif

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR)
	rm -rf $(OUTPUT_DIR)

.PHONY: ocaml
ocaml: all-ml

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
	$(FSTAR) $(if $(findstring FStarC.,$<),--MLish,) --already_cached ',*' -c $< -o $@
	@# HACK: finding FStarC modules and passing --MLish
	@# for them and only them.
	touch -c $@ # update timestamp even if cache hit
	$(maybe_touch)

%.$(EEXT): FF=$(notdir $<)
%.$(EEXT):
	$(call msg, "EXTRACT", $(FF))
	$(FSTAR) $(if $(findstring FStarC.,$<),--MLish,) --already_cached '*,' --codegen $(CODEGEN) $< -o $@
	@# HACK: finding FStarC modules and passing --MLish
	@# for them and only them.
	$(maybe_touch)

%.krml: FF=$(notdir $<)
%.krml:
	$(call msg, "EXTRACT", $(FF))
	$(FSTAR) --already_cached ',*' --codegen krml $< -o $@

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
	$(FSTAR) --dep full $(ROOTS) $(EXTRACT) $(DEPFLAGS) -o $@

depend: $(DEPSTEM)
include $(DEPSTEM)

depgraph: $(DEPSTEM).pdf
$(DEPSTEM).pdf: $(DEPSTEM) .force
	$(call msg, "DEPEND GRAPH", $(SRC))
	$(FSTAR) --dep graph $(ROOTS) $(EXTRACT) $(DEPFLAGS) -o $(DEPSTEM).graph
	$(FSTAR_ROOT)/.scripts/simpl_graph.py $(DEPSTEM).graph > $(DEPSTEM).simpl
	dot -Tpdf -o $@ $(DEPSTEM).simpl
	echo "Wrote $@"

all-checked: $(ALL_CHECKED_FILES)

all-ml: $(ALL_ML_FILES)
	@# Remove extraneous .ml files, which can linger after
	@# module renamings. The realpath is necessary to prevent
	@# discrepancies between absolute and relative paths, double
	@# slashes, etc.
	rm -vf $(filter-out $(realpath $(ALL_ML_FILES)), $(realpath $(wildcard $(OUTPUT_DIR)/*.ml)))

all-fs: $(ALL_FS_FILES)
	rm -vf $(filter-out $(realpath $(ALL_FS_FILES)), $(realpath $(wildcard $(OUTPUT_DIR)/*.fs)))
