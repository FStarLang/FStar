include mk/common.mk

$(call need_exe, FSTAR_EXE, fstar.exe to be used)
$(call need_dir_mk, CACHE_DIR, directory for checked files)
$(call need_dir_mk, OUTPUT_DIR, directory for extracted OCaml files)
$(call need, CODEGEN, backend (OCaml / Plugin))
$(call need_dir, SRC, source directory)
$(call need, TAG, a tag for the .depend; to prevent clashes. Sorry.)

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR)
	rm -rf $(OUTPUT_DIR)

.PHONY: all
all: verify ocaml

.PHONY: ocaml
ocaml: all-ml

.PHONY: verify
verify: all-checked

FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --MLish_effect 'FStarC.Compiler.Effect'
FSTAR_OPTIONS += --cache_checked_modules
FSTAR_OPTIONS += --cache_dir "$(CACHE_DIR)"
FSTAR_OPTIONS += --odir "$(OUTPUT_DIR)"

FSTAR_OPTIONS += --include "$(SRC)"

FSTAR_OPTIONS += $(OTHERFLAGS)

FSTAR = $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

# FIXME: Maintaining this list sucks. Could **the module** itself specify whether it is
# noextract? Actually, the F* compiler should already know which of its modules are
# in its library, and do this by default.
EXTRACT :=
EXTRACT += --extract ',*' # keep the comma (https://github.com/FStarLang/FStar/pull/3640)
EXTRACT += --extract -Prims
EXTRACT += --extract -FStar
EXTRACT += --extract -FStarC.Extraction.ML.PrintML # very much a special case

# Library wrangling
EXTRACT += --extract +FStar.Pervasives
EXTRACT += --extract -FStar.Pervasives.Native
EXTRACT += --extract +FStar.Class.Printable
EXTRACT += --extract +FStar.Seq.Base
EXTRACT += --extract +FStar.Seq.Properties

%.checked.lax: LBL=$(basename $(basename $(notdir $@)))
%.checked.lax:
	$(call msg, "LAXCHECK", $(LBL))
	$(FSTAR) $(if $(findstring FStarC,$<),--MLish,) $<
	@# HACK: finding FStarC modules
	@touch -c $@  ## SHOULD NOT BE NEEDED

%.ml: FF=$(notdir $(subst .checked.lax,,$<))
%.ml: MM=$(basename $(FF))
%.ml: LBL=$(notdir $@)
# ^ HACK we use notdir to get the module name since we need to pass in
# the fst (not the checked file), but we don't know where it is, so this
# is relying on F* looking in its include path.
%.ml:
	$(call msg, "EXTRACT", $(LBL))
	$(FSTAR) $(FF) $(if $(findstring FStarC,$<),--MLish,) --codegen $(CODEGEN) --extract_module $(MM)
	@touch -c $@  ## SHOULD NOT BE NEEDED

ROOTS :=
ROOTS += $(SRC)/fstar/FStarC.Main.fst

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

all-ml: $(ALL_ML_FILES)
	@# Remove extraneous .ml files, which can linger after
	@# module renamings. The realpath is necessary to prevent
	@# discrepancies between absolute and relative paths, double
	@# slashes, etc.
	rm -vf $(filter-out $(realpath $(ALL_ML_FILES)), $(realpath $(wildcard $(OUTPUT_DIR)/*.ml)))

all-checked: $(ALL_CHECKED_FILES)
