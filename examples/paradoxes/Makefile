FSTAR_HOME=../..
include ../Makefile.include

all: uall

uall: propext

propext:
	$(FSTAR) PropositionalExtensionalityInconsistent.fst

%.fst-in: 
	@echo $(OPTIONS) \
	--__temp_no_proj InjectiveTypeFormers \
	--verify_module $(basename $(notdir $@))
