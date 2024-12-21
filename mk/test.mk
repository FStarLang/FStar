# This generic makefile is used by almost everything in examples/ and tests/.
#
# Most clients only need to set FSTAR_ROOT and include $(FSTAR_ROOT)/mk/test.mk (this makefile).
#
# This will take care of running dependency analysis and checking every file in the current directory.
# If there are .expected files, we will try to produce the relevant file and compare it with the .expected file.
# For instance, defining A.ml.expected in a directory with A.fst will trigger extraction of A
# into $(OUTPUT_DIR)/A.ml and comparison with A.ml.expected.
#
# If your directory has subdirectories, you can define SUBDIRS to list them (a line like 'SUBDIRS += dir'
# for each one is idiomatic). If the subdirectories use custom makefiles without all the rules here,
# you can just add them to SUBDIRS_ALL and SUBDIRS_CLEAN.
#
# The 'all' rule by default just depends on __verify and the recursive 'all' rules. This
# will check all files, check all # expected outputs, and extract/build/run the files defined
# in EXTRACT, BUILD, RUN. You can add more functionality in a given Makefile by adding more
# requirements to the 'all' rule.

ifeq ($(FSTAR_ROOT),)
  $(error FSTAR_ROOT is not set. Please set it to the root of your F* repository)
endif
include $(FSTAR_ROOT)/mk/common.mk
.DEFAULT_GOAL := all

# Set a default FSTAR_EXE for most clients.
FSTAR_EXE ?= $(FSTAR_ROOT)/out/bin/fstar.exe
FSTAR_EXE := $(abspath $(FSTAR_EXE))
export FSTAR_EXE

HINTS_ENABLED?=--use_hints

# This warning is really useless.
OTHERFLAGS += --warn_error -321
OTHERFLAGS += --ext context_pruning
OTHERFLAGS += --z3version 4.13.3

# Set ADMIT=1 to admit queries
ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

# Almost everything goes into the OUTPUT_DIR, except for .checked files
# which go in the CACHE_DIR. The .depend goes in the current directory.
# Extracted files, executables, touch files (.diff), outputs (.out), etc,
# all go in the OUTPUT_DIR. This makes cleaning up pretty easy.
OUTPUT_DIR ?= _output
CACHE_DIR ?= _cache

FSTAR = $(FSTAR_EXE) $(SIL) 				\
	$(if $(NO_WRITE_CHECKED),,--cache_checked_modules)		\
	--odir $(OUTPUT_DIR)				\
	--cache_dir $(CACHE_DIR)			\
	--already_cached Prims,FStar,LowStar		\
	 $(OTHERFLAGS) $(MAYBE_ADMIT) $(HINTS_ENABLED)

ifneq ($(MAKECMDGOALS),clean)
ifeq ($(NODEPEND),) # Set NODEPEND=1 to not dependency analysis
FSTAR_FILES ?= $(wildcard *.fst) $(wildcard *.fsti)
FSTAR_FILES := $(strip $(FSTAR_FILES))

ifneq ($(FSTAR_FILES),) # It anyway only runs if fst/fsti files are found in the cwd
.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND", $(CURDIR))
	$(FSTAR) --dep full $(FSTAR_FILES) --output_deps_to $@
depend: .depend
include .depend
endif

endif
endif

# These will be in the cache directory due to the .depend
%.fst.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(FSTAR) $<
	touch -c $@

%.fsti.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(FSTAR) $<
	touch -c $@

$(OUTPUT_DIR)/%.fst.output: NO_WRITE_CHECKED=1
$(OUTPUT_DIR)/%.fst.output: %.fst
	$(call msg, "OUTPUT", $(basename $(notdir $@)))
	$(FSTAR) --message_format human -f --print_expected_failures $< >$@ 2>&1

$(OUTPUT_DIR)/%.fsti.output: NO_WRITE_CHECKED=1
$(OUTPUT_DIR)/%.fsti.output: %.fsti
	$(call msg, "OUTPUT", $(basename $(notdir $@)))
	$(FSTAR) --message_format human -f --print_expected_failures $< >$@ 2>&1

$(OUTPUT_DIR)/%.fst.json_output: NO_WRITE_CHECKED=1
$(OUTPUT_DIR)/%.fst.json_output: %.fst
	$(call msg, "JSONOUT", $(basename $(notdir $@)))
	$(FSTAR) --message_format json -f --print_expected_failures $< >$@ 2>&1

$(OUTPUT_DIR)/%.fsti.json_output: NO_WRITE_CHECKED=1
$(OUTPUT_DIR)/%.fsti.json_output: %.fsti
	$(call msg, "JSONOUT", $(basename $(notdir $@)))
	$(FSTAR) --message_format json -f --print_expected_failures $< >$@ 2>&1

$(OUTPUT_DIR)/$(subst .,_,%).ml:
	$(call msg, "EXTRACT", $(basename $(notdir $@)))
	$(FSTAR) $(subst .checked,,$(notdir $<)) --codegen OCaml --extract_module $(subst .fst.checked,,$(notdir $<))

$(OUTPUT_DIR)/$(subst .,_,%).fs:
	$(call msg, "EXTRACT FS", $(basename $(notdir $@)))
	$(FSTAR) $(subst .checked,,$(notdir $<)) --codegen FSharp --extract_module $(subst .fst.checked,,$(notdir $<))

# No FSharp compilation in these makefiles, sorry.
$(OUTPUT_DIR)/%.exe: $(OUTPUT_DIR)/%.ml
	$(call msg, "OCAMLOPT", $(basename $(notdir $<)))
	$(FSTAR_EXE) --ocamlopt $< -o $@

$(OUTPUT_DIR)/%.out: $(OUTPUT_DIR)/%.exe
	$(call msg, "RUN", $(basename $(notdir $<)))
	./$< > $@

### Checking expected output for any kind of file (error output, ml, etc)
$(OUTPUT_DIR)/%.diff: $(OUTPUT_DIR)/% %.expected
	$(call msg, "DIFF", $<)
	diff -u --strip-trailing-cr $^
	touch $@

$(OUTPUT_DIR)/%.accept: $(OUTPUT_DIR)/%
	$(call msg, "ACCEPT", $<)
	cp $< ./$*.expected

# Subrules for descending into subdirectories (coallesce with a define?)

%.__depend: # Make sure to sequeantlize the .depend for each subdir, to avoid duplication and races
	$(MAKE) -C $* depend

%.__all:
	$(MAKE) -C $* all

%.__verify:
	$(MAKE) -C $* verify

%.__clean:
	$(MAKE) -C $* clean

%.__accept:
	$(MAKE) -C $* accept

SUBDIRS_ALL += $(SUBDIRS)
all: $(addsuffix .__all, $(SUBDIRS_ALL))
# __verify: check all files here and in subdirectories (SUBDIRS / SUBDIRS_VERIFY)
# Implied by 'all' for each directory, but we cannot write 'all: verify' or we
# will get duplicate invocations for all/verify on a same subdir, and they overlap.
SUBDIRS_VERIFY += $(SUBDIRS)
__verify: $(ALL_CHECKED_FILES)
verify: $(addsuffix .__verify, $(SUBDIRS_VERIFY))
verify: __verify
ifeq ($(NOVERIFY),)
all: __verify
endif

HAS_OCAML ?= 1
# We assume we have ocaml, unless HAS_OCAML= was given as an argument
# to make (this is done by binary package CI). If we don't have ocaml,
# we don't try to build or run programs.
ifeq (,$(HAS_OCAML))
NORUN := 1
NOBUILD := 1
endif

# clean
SUBDIRS_CLEAN += $(SUBDIRS)
clean: $(addsuffix .__clean, $(SUBDIRS_CLEAN))
__clean:
	rm -rf $(OUTPUT_DIR) $(CACHE_DIR) .depend
clean: __clean

__extract: $(patsubst %.fst,$(OUTPUT_DIR)/%.ml,$(EXTRACT))
extract: __extract
ifeq ($(NOEXTRACT),)
all: __extract
endif

__build: $(patsubst %.fst,$(OUTPUT_DIR)/%.exe,$(BUILD))
build: __build
ifeq ($(NOBUILD),)
all: __build
endif

__run: $(patsubst %.fst,$(OUTPUT_DIR)/%.out,$(RUN))
run: __run
ifeq ($(NORUN),)
all: __run
endif

__diff: $(patsubst %.expected,$(OUTPUT_DIR)/%.diff,$(wildcard *.expected))
diff: __diff
ifeq ($(NODIFF),)
all: __diff
endif

accept: $(addsuffix .__accept,$(SUBDIRS))
__accept: $(patsubst %.expected,$(OUTPUT_DIR)/%.accept,$(wildcard *.expected))
accept: __accept

# Client makefiles can extend all these rules (all,verify,clean, etc) by adding more
# requisites or attaching a recipe.

# Don't delete intermediates.
.SECONDARY:

# If a rule fails, delete target as it could be corrupted
.DELETE_ON_ERROR:
