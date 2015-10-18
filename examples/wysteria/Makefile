include ../Makefile.include

all: api interpreter theory codegen distclean

EXAMPLES_DIR=./examples

api:
	make -C examples api FSTAR=../$(FSTAR)

interpreter:
	$(FSTAR) interpreter.fst

theory:
	$(FSTAR) theory.fst

OUTPUT_DIR=./ocaml-output

codegen:
	$(FSTAR) --admit_fsi FStar.Set\
	         --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --codegen OCaml --admit_fsi FStar.IO --odir $(OUTPUT_DIR) --use_native_int\
                 ghost.fst ext.fst listTot.fst set.fsi heap.fst st.fst all.fst list.fst listproperties.fst ordset.fsi ordset.fst ordmap.fsi ordmap.fst classical.fst \
                 io.fsti string.fsi prins.fst ast.fst ffibridge.fsi sem.fst runtime.fsi print.fst interpreter.fst sec_server.fst examples/ffi.fst prog.fsi main.fst 

a.out:
	make -C $(OUTPUT_DIR) a.out

clean:
	make -C $(OUTPUT_DIR) clean

distclean:
	make -C $(OUTPUT_DIR) distclean
