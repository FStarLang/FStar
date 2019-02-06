FSTAR_HOME=../..
include ../Makefile.include

all: uall

uall: $(patsubst %.fst,%.uver,$(wildcard *.fst))

Protocol.uver: PROTECT_TOP_LEVEL_AXIOMS=--protect_top_level_axioms false
Protocol.uver: OTHERFLAGS+=--z3cliopt 'smt.random_seed=6'

# special casing this file since there is a weird interaction
# between --verify_module and --use_hints
MRefHeap.uver : MRefHeap.fst
	$(FSTAR) --use_extracted_interfaces true $(OTHERFLAGS) $^

# Targets to get F* arguments in interactive mode
%.fst-in: 
	@echo --use_hints
