FSTAR_HOME=../..
include ../Makefile.include

all: uall

uall: $(patsubst %.fst,%.uver,$(wildcard *.fst))

# Targets to get F* arguments in interactive mode
%.fst-in: 
	@echo $(OTHERFLAGS) $(HINTS_ENABLED)
