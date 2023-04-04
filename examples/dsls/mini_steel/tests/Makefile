INCLUDE_PATHS=.. ../_output/ ../_build/_output

FSTAR_FLAGS=$(addprefix --include , $(INCLUDE_PATHS)) \
	    --cache_checked_modules \
            --already_cached Prims,FStar,Steel \
	    --load Pulse.Main \
	    $(OTHERFLAGS)

FSTAR=fstar.exe $(FSTAR_FLAGS)

all: prep UnitTests.fst.checked OWG.fst.checked

%.checked: prep
	fstar.exe --cache_checked_modules --load_cmxs Pulse.Main $(addprefix --include , $(INCLUDE_PATHS)) $* $(OTHERFLAGS) --warn_error -249

%.ml: UnitTests.fst.checked
	fstar.exe --cmi --codegen OCaml --extract $* $(addprefix --include , $(INCLUDE_PATHS)) $*.fst $(OTHERFLAGS)

prep:
	$(MAKE) -C .. plugin
	fstar.exe --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) Tests.Common.fst $(OTHERFLAGS) --warn_error -249

.PHONY: all prep

%.fst-in:
	@echo $(addprefix --include , $(INCLUDE_PATHS)) --load_cmxs Pulse.Main --warn_error -249
