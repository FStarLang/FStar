FSTAR_HOME=../..
include ../Makefile.include

all: uall sall

uall: propext

sall: russell berardi 
#value-restriction

russell:
	$(SFSTAR) russell.fst

berardi:
	$(SFSTAR) FStar.Constructive.fst berardi.fst

value-restriction: value-restriction.fst
	$(SFSTAR) FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst  $^

propext:
	$(FSTAR) PropositionalExtensionalityInconsistent.fst

%.fst-in: 
	@echo $(OPTIONS) \
	--__temp_no_proj InjectiveTypeFormers \
	--verify_module $(basename $(notdir $@))
