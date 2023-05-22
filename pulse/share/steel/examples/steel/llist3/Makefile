all: llist3

# assuming share/steel/examples/steel/llist3
STEEL_HOME ?= ../../../../..

FSTAR_OPTIONS := --already_cached '*,-SelectorsLList3Example' --include ..

include $(STEEL_HOME)/share/steel/Makefile.include

llist3: $(ALL_KRML_FILES)
	$(KRML_HOME)/krml -skip-makefiles -skip-linking -bundle 'SelectorsLList3Example=FStar.*,Steel.*,Selectors.*' $(ALL_KRML_FILES)

.PHONY: all llist3 clean

clean::
	rm -f compile_flags.txt *.c *.h *.o
