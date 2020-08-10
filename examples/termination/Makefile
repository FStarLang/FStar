ALLFILES=CPS.Simple CPS.Double CPS.DoubleLambdaLifting2 CPS.DoubleDefun CPS.Expr \
	 CPS.SimpleDefun CPS.SimpleLambdaLifting Eval.DB mcCarthy91 termination \
	 TotalMemCpy

FSTAR_HOME=../..
include ../Makefile.include

all: $(addsuffix .uver, $(ALLFILES))

KRML=$(KREMLIN_HOME)/krml

extract:
	$(KRML) -skip-compilation TotalMemCpy.fst -tmpdir out
