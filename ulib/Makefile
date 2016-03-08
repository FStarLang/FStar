FSTAR = ../bin/fstar.exe $(OTHERFLAGS)
UFSTAR=$(FSTAR) --universes --explicit_deps
STDLIB=FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst

all:
	$(UFSTAR) FStar.List.Tot.fst FStar.ListProperties.fst $(STDLIB) FStar.List.fst
	$(UFSTAR) $(STDLIB) FStar.Seq.fst FStar.Classical.fst FStar.SeqProperties.fst FStar.Array.fst
	$(UFSTAR) $(STDLIB) FStar.Axiomatic.Array.fst FStar.Char.fsti FStar.Option.fst FStar.Bytes.fst FStar.Crypto.fst FStar.Tcp.fst
	$(UFSTAR) FStar.Constructive.fst 
	$(UFSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst
	$(UFSTAR) FStar.Squash.fst
	$(UFSTAR) FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.List.Tot.fst FStar.OrdSet.fst FStar.OrdSetProps.fst FStar.OrdMap.fst
	$(UFSTAR) FStar.PredicateExtensionality.fst
	$(UFSTAR) FStar.Mul.fst FStar.Int8.fst FStar.Int16.fst FStar.Int31.fst FStar.Int32.fst FStar.Int63.fst FStar.Int64.fst
	$(UFSTAR) FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.List.Tot.fst FStar.HyperHeap.fst hyperheap/FStar.ST.fst
	$(UFSTAR) $(STDLIB) FStar.MRef.fst
	$(UFSTAR) FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.TwoLevelHeap.fst
	$(UFSTAR) $(STDLIB) FStar.Constructive.fst FStar.Squash.fst FStar.SquashProperties.fst 
	$(UFSTAR) FStar.List.Tot.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst FStar.Relational.Relational.fst FStar.Relational.Comp.fst FStar.Relational.State.fst

test:


# #	$(UFSTAR) FStar.OrdMapProps.fst -- problem filed as #359
# #	$(UFSTAR) stboot.fsi stboot.fst   -- Name "FStar.All.ML" not found
# #	$(UFSTAR) FStar.Util.fst    -- problem filed as #359
# #	# $(UFSTAR) js.fst



ALL_FILES=prims.fst $(STDLIB)\
FStar.List.Tot.fst FStar.ListProperties.fst FStar.List.fst FStar.Seq.fst FStar.Classical.fst FStar.SeqProperties.fst FStar.Array.fst FStar.Axiomatic.Array.fst FStar.Char.fsti FStar.Option.fst FStar.Bytes.fst FStar.Crypto.fst FStar.Tcp.fst FStar.Constructive.fst FStar.Ghost.fst FStar.ErasedLogic.fst \
FStar.Squash.fst \
FStar.SquashProperties.fst \
FStar.Int8.fst FStar.Int16.fst FStar.Int31.fst FStar.Int32.fst FStar.Int63.fst FStar.Int64.fst \
FStar.HyperHeap.fst hyperheap/FStar.ST.fst \
FStar.MRef.fst \
FStar.OrdSet.fst FStar.OrdSetProps.fst FStar.OrdMap.fst \
FStar.PredicateExtensionality.fst \
FStar.Map.fst \
FStar.TwoLevelHeap.fst

wc:	
	wc -l $(ALL_FILES)
