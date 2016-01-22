include ../Makefile.include

all:
	make api
	make theory
	(cd examples/fstar_main; ../../$(FSTAR) traces.fst)
	make codegen SMCIF=examples/fstar_main/psipaperiface.fsi SMCMAIN=examples/fstar_main/psipapermain.fst
	make distclean

EXAMPLES_DIR=./examples

api:
	make -C examples api FSTAR='../$(FSTAR)'

theory:
	$(FSTAR) theory.fst

OUTPUT_DIR=./ocaml-output

CONTRIB=$(FSTAR_HOME)/contrib

CODEGEN_FLAGS=--admit_fsi FStar.Set --admit_fsi FStar.String --admit_fsi FStar.Seq --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --admit_fsi FStar.IO\
              --admit_fsi FStar.Squash --admit_fsi Smciface --admit_fsi Hashtable --codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml --odir $(OUTPUT_DIR)\
              --use_native_int --__temp_no_proj PSemantics --__temp_no_proj SecServer

FSTAR_LIB_FILES=FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti\
                FStar.List.Tot.fst FStar.List.fst FStar.ListProperties.fst ordset.fsi FStar.OrdSet.fst ordmap.fsi FStar.OrdMap.fst FStar.IO.fsti string.fsi hashtable.fsi\

INTERPRETER_FILES=prins.fst ast.fst ffibridge.fsi sem.fst psem.fst rtheory.fst $(CONTRIB)/Platform/fst/Bytes.fst\
                  runtime.fsi print.fst ckt.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst crypto.fst\
                  interpreter.fst sec_server.fst examples/ffi.fst prog.fsi

#SMCIF and SMCMain are set from command line invocation of make
codegen:
	cp $(SMCIF) smciface.fsi
	cp $(SMCMAIN) smc_main.fst
	$(FSTAR) $(CODEGEN_FLAGS) $(EXTERNAL_FLAGS) $(FSTAR_LIB_FILES) $(INTERPRETER_FILES) smciface.fsi smc_main.fst

# codegen:
# 	$(FSTAR) --admit_fsi FStar.Set --admit_fsi FStar.String --admit_fsi FStar.Seq --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --admit_fsi FStar.IO --admit_fsi FStar.Squash\
#                  --codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml --odir $(OUTPUT_DIR) --use_native_int --__temp_no_proj PSemantics --__temp_no_proj SecServer\
#                  FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti\
#                  FStar.List.Tot.fst FStar.List.fst FStar.ListProperties.fst ordset.fsi FStar.OrdSet.fst ordmap.fsi FStar.OrdMap.fst FStar.IO.fsti string.fsi\
#                  prins.fst ast.fst ffibridge.fsi sem.fst psem.fst rtheory.fst $(CONTRIB)/Platform/fst/Bytes.fst runtime.fsi print.fst ckt.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst crypto.fst interpreter.fst sec_server.fst examples/ffi.fst prog.fsi main.fst 

a.out:
	make -C $(OUTPUT_DIR) a.out

clean:
	make -C $(OUTPUT_DIR) clean

distclean:
	rm -f smciface.fsi smc_main.fst
	make -C $(OUTPUT_DIR) distclean
