FLAGS=--admit_fsi FStar.Set \
    FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Relational.fst FStar.Bytes.fst FStar.List.fst

FSTAR = ../../bin/fstar.exe --explicit_deps $(FLAGS) $(OTHERFLAGS)

all: noninterference\
		 sample_examples\
		 ro_single\
		 simple_st2_examples\
		 smart_meter\
		 spdz\
		 cache\
		 projection_test\
		 monotone\
		 ifc\
		 ifc_compiler\
#		 ro 					Fails because of #405 (only works with z3.4.4.0)

noninterference:
	$(FSTAR) --z3timeout 15 --eager_inference distinct.fst noninterference.fst

sample_examples:
	$(FSTAR) sample.fst xor.fst sample_examples.fst

ro_single:
	$(FSTAR) xor.fst ro_single.fst

ro:
	$(FSTAR) xor.fst sample.fst ro.fst

smart_meter:
	$(FSTAR) smart_meter.fst

spdz:
	$(FSTAR) sample.fst spdz.fst

simple_st2_examples:
	$(FSTAR) simple_st2_examples.fst

cache:
	$(FSTAR) cache.fst

ifc_compiler:
	$(FSTAR) distinct.fst ifc_ts.fst ifc_compiler.fst

ifc:
	$(FSTAR) while.fst ifc.fst

monotone::
	$(FSTAR) monotone.fst

projection_test:
	$(FSTAR) projection_test.fst
