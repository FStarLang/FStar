
FLAGS=--explicit_deps
LIB=FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst\
    FStar.Relational.fst FStar.Comp.fst FStar.RelationalState.fst FStar.UInt8.fst FStar.Bytes.fst FStar.List.fst
OTHERFLAGS+=$(FLAGS) $(LIB)
FSTAR_HOME=../..
include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/src/gmake/nubuild.mk

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

NI_FILES=NonInterference.NI.fst        NonInterference.Example1.fst\
	 NonInterference.Example2.fst  NonInterference.Example2.fst\
	 NonInterference.Example4.fst  NonInterference.Example5.fst\
	 NonInterference.Example7.fst  NonInterference.Example7.fst 

noninterference: $(NI_FILES)
	$(FSTAR) --z3timeout 15 --eager_inference distinct.fst $^

sample_examples:
	$(FSTAR) bijection.fst sample.fst xor.fst Sample.Example1.fst Sample.Example2.fst

ro_single:
	$(FSTAR) xor.fst ro_single.fst

ro:
	$(FSTAR) xor.fst bijection.fst sample.fst RandomOracle.RO.fst RandomOracle.Encryption.fst

smart_meter:
	$(FSTAR) smart_meter.fst

spdz:SPDZ.Fp.fst  SPDZ.Sharing.fst  SPDZ.Triples.fst SPDZ.MPC.fst  
	$(FSTAR) bijection.fst sample.fst $^

simple_st2_examples:
	$(FSTAR) simple_st2_examples.fst

cache:
	$(FSTAR) cache.fst

ifc_compiler:
	$(FSTAR) distinct.fst IFC.IFC.fst IFC.Example1.fst IFC.Example3.fst IFC.Example5.fst IFC.Compiler.fst

ifc:
	$(FSTAR) while.fst ifc.fst

monotone::
	$(FSTAR) monotone.fst

projection_test:
	$(FSTAR) projection_test.fst
