
FSTAR = ../bin/fstar.exe $(OTHERFLAGS)

all:
	$(FSTAR) FStar.SeqProperties.fst FStar.Array.fst
	$(FSTAR) FStar.Axiomatic.Array.fst
	$(FSTAR) FStar.Char.fst
	$(FSTAR) FStar.Classical.fst
	$(FSTAR) FStar.Constructive.fst
	$(FSTAR) FStar.Crypto.fst
	$(FSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst
	$(FSTAR) FStar.FunctionalExtensionality.fst
	$(FSTAR) FStar.HyperHeap.fst
	$(FSTAR) FStar.Int8.fst
	$(FSTAR) FStar.Int16.fst
	$(FSTAR) FStar.Int31.fst
	$(FSTAR) FStar.Int32.fst
	$(FSTAR) FStar.Int63.fst
	$(FSTAR) FStar.Int64.fst
	$(FSTAR) FStar.ListProperties.fst
	$(FSTAR) FStar.List.Tot.fst
	$(FSTAR) FStar.Map.fst
	$(FSTAR) FStar.MRef.fst
	$(FSTAR) FStar.Option.fst
	# $(FSTAR) FStar.OrdSet.fst
	# $(FSTAR) FStar.OrdMap.fst
#	$(FSTAR) FStar.OrdMapProps.fst -- problem filed as #359
#	$(FSTAR) FStar.OrdSetProps.fst
	$(FSTAR) FStar.PredicateExtensionality.fst
	$(FSTAR) FStar.Set.fst
#	$(FSTAR) stboot.fsi stboot.fst   -- Name "FStar.All.ML" not found
#	$(FSTAR) FStar.Relational.fst
#	$(FSTAR) --explicit_deps   FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst map.fsi FStar.List.Tot.fst FStar.HyperHeap.fst stHyperHeap.fst
	$(FSTAR) FStar.Tcp.fst
#	$(FSTAR)   FStar.Set.fsi FStar.Heap.fst map.fsi FStar.TwoLevelHeap.fst
#	$(FSTAR) FStar.Util.fst    -- problem filed as #359
	$(FSTAR) FStar.Squash.fst
#	$(FSTAR) FStar.SquashProperties.fst

wc:
	sloccount .
