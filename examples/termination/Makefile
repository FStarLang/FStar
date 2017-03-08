ALLFILES=CPS.Simple CPS.Double CPS.DoubleLambdaLifting2 CPS.DoubleDefun CPS.Expr \
	 CPS.SimpleDefun CPS.SimpleLambdaLifting Eval.DB mcCarthy91 termination

FSTAR_HOME=../..
include ../Makefile.include

all: $(addsuffix .uver, $(ALLFILES))

CFSTAR=$(subst CURRENT_DIR,examples/termination,$(CVERFSTAR))
all-cver: $(addsuffix .ucver, $(ALLFILES))
