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

FSTAR_OPTIONS += $(OTHERFLAGS)
FSTAR_OPTIONS += --odir "$(OUTPUT_DIR)"
FSTAR_OPTIONS += --cache_dir "$(CACHE_DIR)"
FSTAR_OPTIONS += --include "$(SRC)"
FSTAR_OPTIONS += --cache_checked_modules

ifeq ($(ADMIT),1)
FSTAR_OPTIONS += --admit_smt_queries true
endif

ifeq ($(OS),Windows_NT)
WINWRAP=$(FSTAR_ROOT)/mk/winwrap.sh
else
WINWRAP=
endif

FSTAR := $(WINWRAP) $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

%$(EXTENSION): FF=$(notdir $(subst $(EXTENSION),,$@))
%$(EXTENSION):
	$(call msg, $(MSG), $(FF))
	$(FSTAR) $(if $(findstring FStarC.,$<),--MLish,) --already_cached ',*' $<
	@# HACK: finding FStarC modules and passing --MLish
	@# for them and only them.
	touch -c $@ # update timestamp even if cache hit
	$(maybe_touch)

%.$(EEXT): FF=$(notdir $(subst $(EXTENSION),,$<))
%.$(EEXT): MM=$(basename $(FF))
%.$(EEXT): LBL=$(notdir $@)
# ^ HACK we use notdir to get the module name since we need to pass in
# the fst (not the checked file), but we don't know where it is, so this
# is relying on F* looking in its include path.
%.$(EEXT):
	$(call msg, "EXTRACT", $(LBL))
	$(FSTAR) $(if $(findstring FStarC.,$<),--MLish,) $(FF) --already_cached '*,' --codegen $(CODEGEN) --extract_module $(MM)
	@# HACK: finding FStarC modules and passing --MLish
	@# for them and only them.
	$(maybe_touch)

%.krml: FF=$(notdir $(subst $(EXTENSION),,$<))
%.krml: MM=$(basename $(FF))
%.krml: LBL=$(notdir $@)
%.krml:
	$(call msg, "EXTRACT", $(LBL))
	$(FSTAR) $(FF) --already_cached ',*' --codegen krml --extract_module $(MM)

DEPSTEM := $(CACHE_DIR)/.depend$(TAG)

# We always run this to compute a full list of fst/fsti files in the
# $(SRC) (ignoring the roots, it's a bit conservative). The list is
# saved in $(DEPSTEM).touch.chk, and compared to the one we generated
# before in $(DEPSTEM).touch. If there's a change (or the 'previous')
# does not exist, the timestamp of $(DEPSTEM0.touch will be updated
# triggering an actual dependency run.
.PHONY: .force
$(DEPSTEM).touch: .force
	mkdir -p $(dir $@)
	find $(SRC) -name '*.fst*' > $@.chk
	diff -q $@ $@.chk 2>/dev/null || cp $@.chk $@

$(DEPSTEM): $(DEPSTEM).touch
	$(call msg, "DEPEND", $(SRC))
	$(FSTAR) --dep full $(ROOTS) $(EXTRACT) $(DEPFLAGS) --output_deps_to $@

depend: $(DEPSTEM)
include $(DEPSTEM)

depgraph: $(DEPSTEM).pdf
$(DEPSTEM).pdf: $(DEPSTEM) .force
	$(call msg, "DEPEND GRAPH", $(SRC))
	$(FSTAR) --dep graph $(ROOTS) $(EXTRACT) $(DEPFLAGS) --output_deps_to $(DEPSTEM).graph
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
