FSTAR = ../../bin/fstar.exe

all: noninterference\
		 sample_examples\
		 ro_single\
		 simple_st2_examples\
		 smart_meter\
		 spdz\
		 cache\
		 ro\
		 projection_test\
		 monotone\
		 ifc_compiler

noninterference:
	$(FSTAR) noninterference.fst

sample_examples:
	$(FSTAR) sample_examples.fst

ro_single:
	$(FSTAR) ro_single.fst

ro:
	$(FSTAR) ro.fst

smart_meter:
	$(FSTAR) smart_meter.fst

spdz:
	$(FSTAR) spdz.fst

simple_st2_examples:
	$(FSTAR) simple_st2_examples.fst

cache:
	$(FSTAR) cache.fst

ifc_compiler:
	$(FSTAR) ifc_compiler.fst

monotone::
	$(FSTAR) monotone.fst

projection_test:
	$(FSTAR) projection_test.fst
