FSTAR_HOME=../..
include ../Makefile.include

all: uall

uall: $(patsubst %.fst,%.uver,$(wildcard *.fst))

# special casing this file since there is a weird interaction
# between --verify_module and --use_hints
MRefHeap.uver : MRefHeap.fst
	$(FSTAR) --use_extracted_interfaces true $(OTHERFLAGS) $^

# Targets to get F* arguments in interactive mode
%.fst-in: 
	@echo $(OTHERFLAGS) $(HINTS_ENABLED)
