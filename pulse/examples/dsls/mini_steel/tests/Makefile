INCLUDE_PATHS=../core ..

FSTAR_FLAGS=$(addprefix --include , $(INCLUDE_PATHS)) \
	    --cache_checked_modules \
            --already_cached Prims,FStar,Steel \
	    --load Pulse.Main \
	    $(OTHERFLAGS)

FSTAR=fstar.exe $(FSTAR_FLAGS)

all: Pulse.Tests.fst.checked

Pulse.Tests.fst.checked: prep
	$(FSTAR) Pulse.Tests.fst

prep:
	$(MAKE) -C .. extract_all


.PHONY: all prep

%.fst-in:
	@echo --include .. --include ../../core --include ../_output
