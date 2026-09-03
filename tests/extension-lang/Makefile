# This is a very simple Makefile to test the language extensions.
# We define a `tiny` language extension and use it with the file extension `.tiny`.
# I avoid using the mk/test.mk here because it doesn't support other file extensions.

FSTAR_OPT = --load TinyPlugin --lang_extensions tiny --already_cached FStar,Prims --cache_checked_modules --cache_dir .cache
FSTAR_EXE ?= fstar.exe

SRCS = Test0DotFst.fst Test1DotTiny.tiny Test2DotTiny.tiny
CHECKED = $(patsubst %,%.done,$(SRCS))

all: $(CHECKED)
.PHONY: all

clean:
	rm -rf .cache
	rm -f $(PLUGIN_OBJS)
	rm -f TinyPlugin.stamp
	rm -f .depend
.PHONY: clean

# The OCaml objects F* dynlinks for TinyPlugin.
PLUGIN_OBJS = TinyPlugin.cmxs TinyPlugin.cmi TinyPlugin.cmx TinyPlugin.o

# F* compiles TinyPlugin.ml into TinyPlugin.cmxs only when the .cmxs does not
# exist (FStarC.Main.load_native_tactics); it never notices that an existing one
# is stale, and dynlinking a .cmxs built by an older binary fails with Error 353,
# either as an "interface mismatch" or as an undefined symbol.  This stamp is
# remade precisely when the plugin source or the compiler moved, so drop the
# objects there and let the next --load rebuild them.  Every rule below that runs
# F* (they all pass --load) depends on it.
TinyPlugin.stamp: TinyPlugin.ml $(FSTAR_EXE)
	rm -f $(PLUGIN_OBJS)
	touch $@

%.done: % TinyPlugin.stamp
	$(FSTAR_EXE) $(FSTAR_OPT) $<
	touch $@

.depend: TinyPlugin.stamp
	$(FSTAR_EXE) $(FSTAR_OPT) --dep full $(SRCS) -o .depend

include .depend
