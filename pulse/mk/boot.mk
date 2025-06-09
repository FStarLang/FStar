include $(PULSE_ROOT)/mk/common.mk
include $(PULSE_ROOT)/mk/locate.mk

.DEFAULT_GOAL := ocaml
$(call need_exe, FSTAR_EXE, fstar.exe to be used)
$(call need_dir_mk, CACHE_DIR, directory for checked files)
$(call need_dir_mk, OUTPUT_DIR, directory for extracted OCaml files)
$(call need, CODEGEN, backend (OCaml / Plugin))
$(call need_dir, SRC, source directory)
$(call need, TAG, a tag for the .depend; to prevent clashes. Sorry.)
$(call need, ROOTS, a list of roots for the dependency analysis)
# Optional: EXTRACT, DEPFLAGS

# This is to support both --lax and non --lax clients.
EXTENSION := $(if $(findstring --lax,$(FSTAR_OPTIONS)),.checked.lax,.checked)
MSG := $(if $(findstring --lax,$(FSTAR_OPTIONS)),LAXCHECK,CHECK)

.PHONY: clean
clean:
	rm -rf $(CACHE_DIR)
	rm -rf $(OUTPUT_DIR)

.PHONY: __all
__all: verify ocaml

.PHONY: ocaml
ifdef NO_OCAML
ocaml:
else
ocaml: all-ml
endif

.PHONY: verify
verify: all-checked

FSTAR_OPTIONS += $(OTHERFLAGS)
FSTAR_OPTIONS += --odir "$(OUTPUT_DIR)"
FSTAR_OPTIONS += --cache_dir "$(CACHE_DIR)"
FSTAR_OPTIONS += --include "$(SRC)"
FSTAR_OPTIONS += --cache_checked_modules
FSTAR_OPTIONS += --warn_error -321
FSTAR_OPTIONS += $(addprefix --include , $(INCLUDE_PATHS))
FSTAR_OPTIONS += --ext optimize_let_vc
FSTAR_OPTIONS += --z3version 4.13.3

ifeq ($(ADMIT),1)
FSTAR_OPTIONS += --admit_smt_queries true
endif

FSTAR = $(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

%$(EXTENSION): FF=$(notdir $(subst $(EXTENSION),,$@))
%$(EXTENSION):
	$(call msg, $(MSG), $(FF))
	$(FSTAR) --already_cached ',*' $<
	touch -c $@

%.ml: LBL=$(notdir $@)
%.ml:
	$(call msg, "EXTRACT", $(LBL))
	$(FSTAR) $< --already_cached '*,' --codegen $(CODEGEN)
	touch -c $@

%.krml: FF=$(notdir $(subst $(EXTENSION),,$<))
%.krml: MM=$(basename $(FF))
%.krml: LBL=$(notdir $@)
%.krml:
	$(call msg, "EXTRACT", $(LBL))
	$(FSTAR) $< --already_cached ',*' --codegen krml --extract_module $(MM)
	touch -c $@

$(CACHE_DIR)/.depend$(TAG):
	$(call msg, "DEPEND", $(SRC))
	$(FSTAR) --dep full $(ROOTS) $(EXTRACT) $(FSTAR_OPTIONS) $(DEPFLAGS) --output_deps_to $@
	mkdir -p $(CACHE_DIR)

depend: $(CACHE_DIR)/.depend$(TAG)
include $(CACHE_DIR)/.depend$(TAG)

all-ml: $(ALL_ML_FILES)
all-checked: $(ALL_CHECKED_FILES)
