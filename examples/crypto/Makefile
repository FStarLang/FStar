VERFILES=millionaires.fst cca2.fst mac.fst format.fst rpc.fst sig.fst padding.fst mac3.fst encrypt3.fst
include ../Makefile.include
all: .all.ver 

millionaires: 
	$(FSTAR) $(FSTAR_HOME)/lib/partialmap.fst $(FSTAR_HOME)/lib/st.fst 

mac: 
	$(FSTAR) $(FSTAR_HOME)/lib/partialmap.fst $(FSTAR_HOME)/lib/st.fst mac.fst
