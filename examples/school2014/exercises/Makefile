include ../Makefile.include

verify-ex9a-acls-cap: ../solutions/ex9a-mac.fst ../solutions/ex9a-acls2.fst ex9a-acls-cap.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, string.fst partialmap.fst st.fst array-realized.fst ) ../../../examples/unit-tests/list.fst $^

verify-ex9b-format: ex9b-format.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9c-format: ex9c-format.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9d-padding: ex9d-padding.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9e-padding: ex9e-padding.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9f-padding: ex9f-padding.fst
	$(FSTAR) $(SECLIB) $^

verify-ex9g-padding: ex9g-padding.fst
	$(FSTAR) $(SECLIB) $^



verify-%: __force__
	$(FSTAR) $*.fst

verify-security: verify-ex9b-format verify-ex9c-format verify-ex9d-padding verify-ex9e-padding verify-ex9f-padding verify-ex9g-padding
