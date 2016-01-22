
FSTAR = ../bin/fstar.exe $(OTHERFLAGS)

all:
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.fst
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.Seq FStar.Set.fsi FStar.Heap.fst FStar.ST.fst seq.fsi FStar.Classical.fst FStar.SeqProperties.fst FStar.Array.fst
	$(FSTAR) array.fst
	$(FSTAR) FStar.Char.fst
	$(FSTAR) FStar.Classical.fst
	$(FSTAR) FStar.Constructive.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Bytes.fst FStar.Crypto.fst
	$(FSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst
	$(FSTAR) FStar.FunctionalExtensionality.fst
	$(FSTAR) FStar.HyperHeap.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int8.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int16.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int31.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int32.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst int63.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int64.fst
	$(FSTAR) js.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst FStar.ListProperties.fst
	$(FSTAR) FStar.List.Tot.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.FunctionalExtensionality.fst map.fsi FStar.Map.fst
	$(FSTAR) FStar.MRef.fst
	$(FSTAR) FStar.Option.fst
	$(FSTAR) FStar.OrdMap.fst
#	$(FSTAR) FStar.OrdMapProps.fst -- problem filed as #359
	$(FSTAR) FStar.OrdSet.fst
	$(FSTAR) FStar.OrdSetProps.fst
	$(FSTAR) FStar.PredicateExtensionality.fst
	$(FSTAR) FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Set.fst
#	$(FSTAR) stboot.fsi stboot.fst   -- Name "FStar.All.ML" not found
	$(FSTAR) FStar.Relational.fst
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.Map FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst FStar.HyperHeap.fst stHyperHeap.fst
	$(FSTAR) --admit_fsi FStar.Set FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Bytes.fst FStar.Tcp.fst
	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.Map FStar.Set.fsi FStar.Heap.fst map.fsi FStar.TwoLevelHeap.fst
#	$(FSTAR) FStar.Util.fst    -- problem filed as #359
	$(FSTAR) FStar.Squash.fst
	$(FSTAR) FStar.SquashProperties.fst

wc:
	sloccount .
