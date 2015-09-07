include ../Makefile.include

verify-ex8a-acls:  ex8a-acls.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst st.fst list.fst ) $^

verify-ex9a-acls-cap: ../solutions/ex9a-mac.fst ../solutions/ex9a-acls2.fst ex9a-acls-cap.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst st.fst list.fst ) $^

verify-ex9bc-format: ex9bc-format.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9bc-mac: ex9bc-mac.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9bc-rpc: ex9bc-format.fst ex9bc-mac.fst ex9bc-rpc.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9defgh-padding: ex9defgh-padding.fst
	$(FSTAR) $(SECLIB) $^

verify-ex10-shift: ex10-shift.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, ext.fst set.fsi heap.fst st.fst) --admit_fsi FStar.Set $^

verify-robots:
	$(FSTAR) robot2.fst

verify-%: __force__
	$(FSTAR) $*.fst

verify-security: verify-ex9a-acls-cap verify-ex9bc-format verify-ex9bc-mac verify-ex9bc-rpc verify-ex9defgh-padding
