
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

STDLIB=FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst
UFSTAR=$(FSTAR) --universes

all_univs:
	# $(UFSTAR) FStar.List.Tot.fst $(STDLIB) FStar.List.fst FStar.ListProperties.fst
	# $(UFSTAR) $(STDLIB) FStar.Seq.fst FStar.Classical.fst FStar.SeqProperties.fst FStar.Array.fst
	# $(UFSTAR) $(STDLIB) array.fst FStar.Char.fst
	# $(UFSTAR) $(STDLIB) FStar.Bytes.fst FStar.Crypto.fst
	# $(UFSTAR) FStar.Constructive.fst 
	# $(UFSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst
	# $(UFSTAR) FStar.Squash.fst
	# $(UFSTAR) FStar.SquashProperties.fst --__temp_no_proj FStar.SquashProperties
	# $(UFSTAR) FStar.Int8.fst FStar.Int16.fst FStar.Int31.fst FStar.Int32.fst FStar.Int63.fst FStar.Int64.fst
	$(UFSTAR) FStar.HyperHeap.fst
# 	$(UFSTAR) js.fst
# 	$(UFSTAR) $(STDLIB) FStar.Map.fst
# 	$(UFSTAR) FStar.MRef.fst
# 	$(UFSTAR) FStar.Option.fst 
# 	$(UFSTAR) FStar.OrdMap.fst
# #	$(UFSTAR) FStar.OrdMapProps.fst -- problem filed as #359
# 	$(UFSTAR) FStar.OrdSet.fst
# 	$(UFSTAR) FStar.OrdSetProps.fst
# 	$(UFSTAR) FStar.PredicateExtensionality.fst
# #	$(UFSTAR) stboot.fsi stboot.fst   -- Name "FStar.All.ML" not found
# 	$(UFSTAR) FStar.Relational.fst
# 	$(UFSTAR) FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.List.Tot.fst FStar.HyperHeap.fst stHyperHeap.fst
# 	$(UFSTAR) $(STDLIB) FStar.Bytes.fst FStar.Tcp.fst
# 	$(UFSTAR) FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.TwoLevelHeap.fst
# #	$(UFSTAR) FStar.Util.fst    -- problem filed as #359

wc:
	sloccount .
