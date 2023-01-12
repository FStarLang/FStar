INCLUDE_PATHS += .. ../_cache
OTHERFLAGS+=--already_cached '*,-SelectorsLList2Example' --compat_pre_typed_indexed_effects
FSTAR_FILES = SelectorsLList2Example.fst

all: llist2

include ../../Makefile.common

$(OUTPUT_DIRECTORY)/%.krml:
	$(MY_FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<)))
	touch -c $@

llist2: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml -skip-makefiles -skip-linking -bundle 'SelectorsLList2Example=FStar.*,Steel.*,Selectors.*' $(ALL_KRML_FILES)

.PHONY: all llist2
