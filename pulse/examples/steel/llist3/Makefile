INCLUDE_PATHS += .. ../_cache
OTHERFLAGS+=--already_cached '*,-SelectorsLList3Example' --compat_pre_typed_indexed_effects --cmi
FSTAR_FILES = SelectorsLList3Example.fst

all: llist3

include ../../Makefile.common

$(OUTPUT_DIRECTORY)/%.krml:
	$(MY_FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<)))
	touch -c $@

llist3: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml -skip-makefiles -skip-linking -bundle 'SelectorsLList3Example=FStar.*,Steel.*,Selectors.*' $(ALL_KRML_FILES)

.PHONY: all llist3
