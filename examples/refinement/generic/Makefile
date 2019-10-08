<<<<<<< HEAD:examples/refinement/generic/Makefile
FSTAR_HOME=../../../
include ../../Makefile.include
ROOTS=Lens.fst FibState.fst
=======
FSTAR_HOME=../..
OTHERFLAGS+=--already_cached 'Prims FStar LowStar'
include ../Makefile.include
ROOTS=HighComp.fst LowComp.fst sum_and_swap.fst
>>>>>>> master:examples/refinement/Makefile

all: verify-all

.depend:
	$(FSTAR) --dep full $(ROOTS) > .depend

depend: .depend

include .depend

verify-all: $(ALL_CHECKED_FILES)

%.checked:
	$(FSTAR) --cache_checked_modules $<

clean:
	rm -f .depend *.checked
