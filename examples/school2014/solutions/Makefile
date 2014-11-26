include ../Makefile.include

RPCLIB = $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst list.fst st.fst array-realized.fst )

verify-format: format.fst
	$(FSTAR) $(RPCLIB) $^

verify-mac: mac.fst
	$(FSTAR) $(RPCLIB) $^

verify-rpc: format.fst mac.fst rpc.fst 
	$(FSTAR) $(RPCLIB) $^

verify-%: __force__
	$(FSTAR) $*.fst
