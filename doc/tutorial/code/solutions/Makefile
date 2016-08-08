FSTAR_HOME=../../../..
include ../Makefile.include

verify-ex8a-acls:  ex8a-acls.fst
	$(SFSTAR) $(addprefix $(FSTAR_HOME)/lib/, FStar.String.fsti partialmap.fst FStar.ST.fst FStar.List.fst ) $^

verify-ex9a-acls-cap: ../solutions/ex9a-mac.fst ../solutions/ex9a-acls2.fst ex9a-acls-cap.fst
	$(SFSTAR) $(addprefix $(FSTAR_HOME)/lib/, FStar.String.fsti partialmap.fst FStar.ST.fst FStar.List.fst ) $^

verify-ex9bc-format: ex9bc-format.fst
	$(SFSTAR) $(SECLIB) $^

verify-ex9bc-mac: ex9bc-mac.fst
	$(SFSTAR) $(SECLIB) $^

verify-ex9bc-rpc: ex9bc-format.fst ex9bc-mac.fst ex9bc-rpc.fst
	$(SFSTAR) $(SECLIB) $^

verify-ex9defgh-padding: ex9defgh-padding.fst
	$(SFSTAR) $(SECLIB) $^

verify-ex10-shift: ex10-shift.fst
	$(SFSTAR) $(addprefix $(FSTAR_HOME)/lib/, FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst)  $^

verify-robots:
	$(SFSTAR) robot.fst
	$(SFSTAR) robot2.fst

verify-%: __force__
	$(SFSTAR) $*.fst

verify-security: verify-ex9a-acls-cap verify-ex9bc-format verify-ex9bc-mac verify-ex9bc-rpc verify-ex9defgh-padding

