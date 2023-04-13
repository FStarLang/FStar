all: llist2

# assuming share/steel/examples/steel/llist2
STEEL_HOME ?= ../../../../..

FSTAR_OPTIONS := --already_cached '*,-SelectorsLList2Example' --include ..

include $(STEEL_HOME)/share/steel/Makefile.include

llist2: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml -skip-makefiles -skip-linking -bundle 'SelectorsLList2Example=FStar.*,Steel.*,Selectors.*' $(ALL_KRML_FILES)

.PHONY: all llist2 clean

clean::
	rm -f compile_flags.txt *.c *.h *.o
