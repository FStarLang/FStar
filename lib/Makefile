
FSTAR = ../bin/fstar.exe $(OTHERFLAGS)

all:
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst
	$(FSTAR) --admit_fsi FStar.Set ext.fst set.fsi seq.fsi seq.fst
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.Seq set.fsi heap.fst st.fst seq.fsi classical.fst seqproperties.fst arr.fst
	$(FSTAR) array.fst
	$(FSTAR) char.fst
	$(FSTAR) classical.fst
	$(FSTAR) constr.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst bytes.fst crypto.fst
	$(FSTAR) ghost.fst elogic.fst
	$(FSTAR) ext.fst
	$(FSTAR) hyperHeap.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst int8.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst int16.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst int31.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst int32.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst int63.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst int64.fst
	$(FSTAR) js.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst list.fst listproperties.fst
	$(FSTAR) listTot.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi ext.fst map.fsi map.fst
	$(FSTAR) mref.fst
	$(FSTAR) option.fst
	$(FSTAR) ordmap.fst
#	$(FSTAR) ordmapproperties.fst -- problem filed as #359
	$(FSTAR) ordset.fst
	$(FSTAR) ordsetproperties.fst
	$(FSTAR) pext.fst
	$(FSTAR) ext.fst set.fsi set.fst
#	$(FSTAR) stboot.fsi stboot.fst   -- Name "FStar.All.ML" not found
	$(FSTAR) st2.fst
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.Map ext.fst set.fsi heap.fst map.fsi listTot.fst hyperHeap.fst stHyperHeap.fst
	$(FSTAR) --admit_fsi FStar.Set set.fsi heap.fst st.fst all.fst bytes.fst tcp.fst
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.Map set.fsi heap.fst map.fsi twoLevelHeap.fst
#	$(FSTAR) util.fst    -- problem filed as #359
	$(FSTAR) squash.fst
	$(FSTAR) squashproperties.fst

wc:
	sloccount .
