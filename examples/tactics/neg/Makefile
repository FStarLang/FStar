FSTAR_HOME=../../..
include ../../Makefile.include

all:	NonTot.fail	\
	Unresolved.fail	\
	Unbound.fail	\
	Ill1.fail	\
	Ill2.fail	\
	NatNeg.fail	\
	LemmaArgs.fail

%.fail: %.fail-uver
	touch $@
