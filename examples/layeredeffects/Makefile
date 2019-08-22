FSTAR_HOME=../..
include ../Makefile.include

%.uver: %.fst
	$(BENCHMARK_PRE) $(FSTAR) --use_extracted_interfaces false $^

all: uall

uall: HoareST.uver HoareST2.uver Test.uver RST.Effect.uver RST.Effect.Test.uver
