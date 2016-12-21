FSTAR_HOME=../..
include ../Makefile.include

all: uall sall

uall: $(patsubst %.fst,%.uver,$(wildcard *.fst))

# special casing this file since there is a weird interaction
# between --verify_module and --use_hints
MRefHeap.uver : MRefHeap.fst
	$(FSTAR) --record_hints --verify_module MRefHeap $^

sall:

