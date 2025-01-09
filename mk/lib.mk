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

.PHONY: verify
verify: all-checked

FSTAR_OPTIONS += --cache_checked_modules # should be the default
FSTAR_OPTIONS += --cache_dir "$(CACHE_DIR)"
FSTAR_OPTIONS += --odir "$(OUTPUT_DIR)"

FSTAR_OPTIONS += --use_hints
FSTAR_OPTIONS += --hint_dir $(SRC)/.hints
FSTAR_OPTIONS += --warn_error -333 # Do not warn about missing hints
FSTAR_OPTIONS += --ext context_pruning
FSTAR_OPTIONS += --z3version 4.13.3

FSTAR_OPTIONS += --no_default_includes
FSTAR_OPTIONS += --include $(SRC)
ifeq ($(ADMIT),1)
FSTAR_OPTIONS += --admit_smt_queries true
endif

# Extension for extracted files
ifeq ($(CODEGEN),FSharp)
EEXT:=fs
else
EEXT:=ml
endif

FSTAR_OPTIONS += $(OTHERFLAGS)

EXTRACT_NS :=
EXTRACT_NS += -FStar.Buffer
EXTRACT_NS += -FStar.Bytes
EXTRACT_NS += -FStar.Char
EXTRACT_NS += -FStar.CommonST
EXTRACT_NS += -FStar.Constructive
EXTRACT_NS += -FStar.Dyn
EXTRACT_NS += -FStar.Float
EXTRACT_NS += -FStar.Ghost
EXTRACT_NS += -FStar.Heap
EXTRACT_NS += -FStar.Monotonic.Heap
EXTRACT_NS += -FStar.HyperStack.All
EXTRACT_NS += -FStar.HyperStack.ST
EXTRACT_NS += -FStar.HyperStack.IO
EXTRACT_NS += -FStar.Int16
EXTRACT_NS += -FStar.Int32
EXTRACT_NS += -FStar.Int64
EXTRACT_NS += -FStar.Int8
EXTRACT_NS += -FStar.IO
EXTRACT_NS += -FStar.List
EXTRACT_NS += -FStar.List.Tot.Base
EXTRACT_NS += -FStar.Option
EXTRACT_NS += -FStar.Pervasives.Native
EXTRACT_NS += -FStar.ST
EXTRACT_NS += -FStar.Exn
EXTRACT_NS += -FStar.String
EXTRACT_NS += -FStar.UInt16
EXTRACT_NS += -FStar.UInt32
EXTRACT_NS += -FStar.UInt64
EXTRACT_NS += -FStar.UInt8
EXTRACT_NS += -FStar.Pointer.Derived1
EXTRACT_NS += -FStar.Pointer.Derived2
EXTRACT_NS += -FStar.Pointer.Derived3
EXTRACT_NS += -FStar.BufferNG
EXTRACT_NS += -FStar.TaggedUnion
EXTRACT_NS += -FStar.Bytes
EXTRACT_NS += -FStar.Util
EXTRACT_NS += -FStar.InteractiveHelpers
EXTRACT_NS += -FStar.Class
EXTRACT_NS += -FStar.Vector.Base
EXTRACT_NS += -FStar.Vector.Properties
EXTRACT_NS += -FStar.Vector
EXTRACT_NS += -FStar.TSet
EXTRACT_NS += -FStar.MSTTotal
EXTRACT_NS += -FStar.MST
EXTRACT_NS += -FStar.NMSTTotal
EXTRACT_NS += -FStar.NMST
EXTRACT_NS += -FStar.Printf
EXTRACT_NS += -FStar.ModifiesGen
EXTRACT_NS += -LowStar.Printf
EXTRACT_NS += -FStar.Sealed
EXTRACT_NS += +FStar.List.Pure.Base
EXTRACT_NS += +FStar.List.Tot.Properties
EXTRACT_NS += +FStar.Int.Cast.Full

# Note: the pluginlib rules will enable these.
EXTRACT_NS += -FStar.Tactics
EXTRACT_NS += -FStar.Reflection

FSTAR := $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

EXTRACT := --extract '* $(EXTRACT_NS)'

%.checked: LBL=$(basename $(notdir $@))
%.checked:
	$(call msg, "CHECK", $(LBL))
	$(FSTAR) $<
	@touch -c $@  ## SHOULD NOT BE NEEDED

%.$(EEXT): FF=$(notdir $(subst .checked,,$<))
%.$(EEXT): MM=$(basename $(FF))
%.$(EEXT): LBL=$(notdir $@)
# ^ HACK: we use notdir to get the module name since we need to pass in
# the fst (not the checked file), but we don't know where it is, so this
# is relying on F* looking in its include path. sigh.
%.$(EEXT):
	$(call msg, "EXTRACT", $(LBL))
	$(FSTAR) $(FF) --codegen $(CODEGEN) --extract_module $(MM)
	@touch -c $@  ## SHOULD NOT BE NEEDED

# Leaving this empty, F* will scan the include path for all fst/fsti
# files. This will read fstar.include and follow it too.
# ROOTS :=
# No! If we do that, we will pick up files from the current directory
# (the root of the repo) since that is implicitly included in F*'s
# search path. So instead, be explicit about scanning over all the files
# in $(SRC) (i.e. ulib). Note that there is a still a problem if there is a
# file in the cwd named like a file in ulib/, F* may prefer the former.
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')

$(CACHE_DIR)/.depend$(TAG):
	$(call msg, "DEPEND", $(SRC))
	$(FSTAR) --dep full $(ROOTS) $(EXTRACT) $(DEPFLAGS) --output_deps_to $@
	mkdir -p $(CACHE_DIR)

depend: $(CACHE_DIR)/.depend$(TAG)
include $(CACHE_DIR)/.depend$(TAG)

all-checked: $(ALL_CHECKED_FILES)
# These targets imply verification of every file too, regardless
# of extraction.
all-ml: all-checked $(ALL_ML_FILES)
	@# Remove extraneous .ml files, which can linger after
	@# module renamings. The realpath is necessary to prevent
	@# discrepancies between absolute and relative paths, double
	@# slashes, etc.
	rm -vf $(filter-out $(realpath $(ALL_ML_FILES)), $(realpath $(wildcard $(OUTPUT_DIR)/*.ml)))

all-fs: all-checked $(ALL_FS_FILES)
	rm -vf $(filter-out $(realpath $(ALL_FS_FILES)), $(realpath $(wildcard $(OUTPUT_DIR)/*.fs)))
