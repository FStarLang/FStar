# This is a very simple Makefile to test the language extensions.
# We define a `tiny` language extension and use it with the file extension `.tiny`.
# I avoid using the mk/test.mk here because it doesn't support other file extensions.

FSTAR_OPT = --load TinyPlugin --lang_extensions tiny --already_cached FStar,Prims --cache_checked_modules --cache_dir .cache
FSTAR_EXE ?= fstar.exe

SRCS = Test0DotFst.fst Test1DotTiny.tiny Test2DotTiny.tiny
CHECKED = $(patsubst %,%.checked,$(SRCS))

all: $(CHECKED)
.PHONY: all

clean:
	rm -rf .cache
	rm TinyPlugin.cmi TinyPlugin.cmx TinyPlugin.o TinyPlugin.cmxs
	rm -f .depend
.PHONY: clean

%.checked: % TinyPlugin.cmxs
	$(FSTAR_EXE) $(FSTAR_OPT) $<

.depend:
	$(FSTAR_EXE) $(FSTAR_OPT) --dep full $(SRCS) -o .depend

include .depend
