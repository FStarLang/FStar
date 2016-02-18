
FSTAR = ../bin/fstar.exe $(OTHERFLAGS)

all:
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
	$(FSTAR)  FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.fst
	$(FSTAR)   FStar.Set.fsi FStar.Heap.fst FStar.ST.fst seq.fsi FStar.Classical.fst FStar.SeqProperties.fst FStar.Array.fst
	$(FSTAR) array.fst
	$(FSTAR) FStar.Char.fst
	$(FSTAR) FStar.Classical.fst
	$(FSTAR) FStar.Constructive.fst
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Bytes.fst FStar.Crypto.fst
	$(FSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst
	$(FSTAR) FStar.FunctionalExtensionality.fst
	$(FSTAR) FStar.HyperHeap.fst
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int8.fst
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int16.fst
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int31.fst
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int32.fst
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst int63.fst
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Int64.fst
	$(FSTAR) js.fst
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst FStar.ListProperties.fst
	$(FSTAR) FStar.List.Tot.fst
	$(FSTAR)  FStar.Set.fsi FStar.FunctionalExtensionality.fst map.fsi FStar.Map.fst
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
	$(FSTAR)   FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst FStar.HyperHeap.fst stHyperHeap.fst
	$(FSTAR)  FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Bytes.fst FStar.Tcp.fst
	$(FSTAR)   FStar.Set.fsi FStar.Heap.fst map.fsi FStar.TwoLevelHeap.fst
#	$(FSTAR) FStar.Util.fst    -- problem filed as #359
	$(FSTAR) FStar.Squash.fst
	$(FSTAR) FStar.SquashProperties.fst

STDLIB=FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst
UFSTAR=$(FSTAR) --universes

working:
	$(UFSTAR) FStar.List.Tot.fst FStar.ListProperties.fst $(STDLIB) FStar.List.fst
	$(UFSTAR) $(STDLIB) FStar.Seq.fst FStar.Classical.fst FStar.SeqProperties.fst FStar.Array.fst

all_univs:
	$(UFSTAR) $(STDLIB) array.fst FStar.Char.fst FStar.Option.fst FStar.Bytes.fst FStar.Crypto.fst FStar.Tcp.fst
	$(UFSTAR) FStar.Constructive.fst 
	$(UFSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst
	$(UFSTAR) FStar.Squash.fst
	$(UFSTAR) $(STDLIB) FStar.Constructive.fst FStar.Squash.fst FStar.SquashProperties.fst --__temp_no_proj FStar.SquashProperties
	$(UFSTAR) FStar.Int8.fst FStar.Int16.fst FStar.Int31.fst FStar.Int32.fst FStar.Int63.fst FStar.Int64.fst
	$(UFSTAR) FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.List.Tot.fst FStar.HyperHeap.fst hyperheap/FStar.ST.fst
	$(UFSTAR) $(STDLIB) FStar.MRef.fst
	$(UFSTAR) FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.List.Tot.fst FStar.OrdSet.fst FStar.OrdSetProps.fst FStar.OrdMap.fst
	$(UFSTAR) FStar.PredicateExtensionality.fst
	$(UFSTAR) FStar.List.Tot.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst FStar.Relational.fst
	$(UFSTAR) FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.TwoLevelHeap.fst
# #	$(UFSTAR) FStar.OrdMapProps.fst -- problem filed as #359
# #	$(UFSTAR) stboot.fsi stboot.fst   -- Name "FStar.All.ML" not found
# #	$(UFSTAR) FStar.Util.fst    -- problem filed as #359
# #	# $(UFSTAR) js.fst



ALL_FILES=prims.fst $(STDLIB)\
FStar.List.Tot.fst FStar.ListProperties.fst FStar.List.fst FStar.Seq.fst FStar.Classical.fst FStar.SeqProperties.fst FStar.Array.fst array.fst FStar.Char.fst FStar.Option.fst FStar.Bytes.fst FStar.Crypto.fst FStar.Tcp.fst FStar.Constructive.fst FStar.Ghost.fst FStar.ErasedLogic.fst \
FStar.Squash.fst \
FStar.SquashProperties.fst \
FStar.Int8.fst FStar.Int16.fst FStar.Int31.fst FStar.Int32.fst FStar.Int63.fst FStar.Int64.fst \
FStar.HyperHeap.fst stHyperHeap.fst \
FStar.MRef.fst \
FStar.OrdSet.fst FStar.OrdSetProps.fst FStar.OrdMap.fst \
FStar.PredicateExtensionality.fst \
FStar.Map.fst \
FStar.TwoLevelHeap.fst

wc:
	wc -l $(ALL_FILES)
