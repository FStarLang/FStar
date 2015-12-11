
FSTAR = ../bin/fstar.exe $(OTHERFLAGS)

all:
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
	$(FSTAR) --admit_fsi FStar.Set ext.fst FStar.Set.fsi seq.fsi seq.fst
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.Seq FStar.Set.fsi FStar.Heap.fst FStar.ST.fst seq.fsi classical.fst seqproperties.fst arr.fst
	$(FSTAR) array.fst
	$(FSTAR) char.fst
	$(FSTAR) classical.fst
	$(FSTAR) constr.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst bytes.fst crypto.fst
	$(FSTAR) ghost.fst elogic.fst
	$(FSTAR) ext.fst
	$(FSTAR) hyperHeap.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst int8.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst int16.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst int31.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst int32.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst int63.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst int64.fst
	$(FSTAR) js.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst list.fst listproperties.fst
	$(FSTAR) listTot.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi ext.fst map.fsi map.fst
	$(FSTAR) mref.fst
	$(FSTAR) option.fst
	$(FSTAR) ordmap.fst
#	$(FSTAR) ordmapproperties.fst -- problem filed as #359
	$(FSTAR) ordset.fst
	$(FSTAR) ordsetproperties.fst
	$(FSTAR) pext.fst
	$(FSTAR) ext.fst FStar.Set.fsi FStar.Set.fst
#	$(FSTAR) stboot.fsi stboot.fst   -- Name "FStar.All.ML" not found
	$(FSTAR) st2.fst
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.Map ext.fst FStar.Set.fsi FStar.Heap.fst map.fsi listTot.fst hyperHeap.fst stHyperHeap.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst bytes.fst tcp.fst
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.Map FStar.Set.fsi FStar.Heap.fst map.fsi twoLevelHeap.fst
#	$(FSTAR) util.fst    -- problem filed as #359
	$(FSTAR) squash.fst
	$(FSTAR) squashproperties.fst

wc:
	sloccount .
