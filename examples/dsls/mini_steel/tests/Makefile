INCLUDE_PATHS=../../core .. ../_output/ ../_build/_output

FSTAR_FLAGS=$(addprefix --include , $(INCLUDE_PATHS)) \
	    --cache_checked_modules \
            --already_cached Prims,FStar,Steel \
	    --load Pulse.Main \
	    $(OTHERFLAGS)

FSTAR=fstar.exe $(FSTAR_FLAGS)

all: Pulse.Tests.fst.checked

Pulse.Tests.fst.checked: prep wrapper
	fstar.exe --cache_checked_modules --load_cmxs Pulse.Main $(addprefix --include , $(INCLUDE_PATHS)) Pulse.Tests.fst --log_types --trace_error --debug Pulse.Tests --debug_level SMTQuery $(OTHERFLAGS)

Pulse_Tests.ml: Pulse.Tests.fst.checked
	fstar.exe --cmi --codegen OCaml --extract Pulse.Tests $(addprefix --include , $(INCLUDE_PATHS)) Pulse.Tests.fst $(OTHERFLAGS)

prep:
	$(MAKE) -C .. plugin

wrapper:
	fstar.exe --cache_checked_modules --load_cmxs Pulse.Main $(addprefix --include , $(INCLUDE_PATHS)) Pulse.Steel.Wrapper.fsti $(OTHERFLAGS)
	fstar.exe --cache_checked_modules --load_cmxs Pulse.Main $(addprefix --include , $(INCLUDE_PATHS)) Pulse.Steel.Wrapper.fst $(OTHERFLAGS)


.PHONY: all prep

%.fst-in:
	@echo --include .. --include ../../core --include ../_output
