ifdef FSTAR_HOME
  FSTAR_ULIB=$(shell if test -d $(FSTAR_HOME)/ulib ; then echo $(FSTAR_HOME)/ulib ; else echo $(FSTAR_HOME)/lib/fstar ; fi)
else
  # FSTAR_HOME not defined, assume fstar.exe installed through opam
  # or binary package, and reachable from PATH
  FSTAR_ULIB=$(dir $(shell which fstar.exe))/../lib/fstar
endif
include $(FSTAR_ULIB)/gmake/z3.mk
include $(FSTAR_ULIB)/gmake/fstar.mk

#for getting macros for OCaml commands to compile extracted code
include $(FSTAR_ULIB)/ml/Makefile.include

ifdef FSTAR_HOME
  -include $(FSTAR_HOME)/.common.mk
  FSTAR=$(FSTAR_HOME)/bin/fstar.exe
else
  FSTAR=fstar.exe
endif

INCLUDE_PATHS=.. ../_output/ ../_build/_output

MY_FSTAR=$(FSTAR) \
  $(addprefix --include , $(INCLUDE_PATHS)) \
	--cache_checked_modules \
  --already_cached Prims,FStar,Steel,Pulse \
	--load_cmxs Pulse.Main \
	--warn_error -249 \
	$(OTHERFLAGS)

all: prep UnitTests.fst.checked OWG.fst.checked

%.checked: prep
	$(MY_FSTAR) $*

%.ml: UnitTests.fst.checked
	$(MY_FSTAR) --cmi --codegen OCaml --extract $*  $*.fst

prep:
	$(MAKE) -C .. plugin
	$(MY_FSTAR) Tests.Common.fst

.PHONY: all prep

%.fst-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS)) --load_cmxs Pulse.Main --warn_error -249
