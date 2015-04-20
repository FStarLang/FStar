FSTAR_HOME=../../../..
FSTAR_BIN=fstar.exe
FSTAR=$(FSTAR_HOME)/bin/$(FSTAR_BIN) --fstar_home $(FSTAR_HOME)
STATE=
main: 
	$(FSTAR) $(FSTAR_HOME)/lib/list.fst main.fst 
#
#all : swap factorial fibonacci wp
#
#wp : exp.fst wp.fst
#	$(FSTAR) exp.fst wp.fst
#
#swap : swap.fst
#	$(FSTAR) $(STATE) $^
#
#factorial : factorial.fst
#	$(FSTAR) $(STATE) $^
#
#fibonacci : fibonacci.fst
#	$(FSTAR) $(STATE) $^

