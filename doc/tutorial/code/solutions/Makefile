VERFILES= \
Ex01a.fst \
Ex02a.fst \
Ex03a.fst \
Ex03b.fst \
Ex03c.fst \
Ex04a.fst \
Ex04b.fst \
Ex04c.fst \
Ex04e.fst \
Ex04f.fst \
Ex04g.fst \
Ex04h.fst \
Ex05a.fst \
Ex05b.fst \
Ex06a.fst \
Ex06b.fst \
Ex06c.fst \
Ex06d.fst \
Ex06e.fst \
Ex07a.fst \
Ex07b.fst \
Ex07c.fst \
Ex07d.fst \
Ex10a.fst \
Ex10b.fst \
Ex11a.fst \
Ex12.MAC.fst \
Ex12a1.Cap.fst \
Ex12a2.Cap.fst \
Ex12b1.Format.fst \
Ex12b2.Format.fst \
Ex12b.RPC.fst \
Ex12d.Pad.fst \
Ex12e.Pad.fst \
Ex12f.TMAC.fst \
Ex12g.TMAC2.fst \
EtM.Plain.fst \
EtM.CPA.fst \
EtM.MAC.fst \
EtM.AE.fst \
LowStar.Ex1.fst \
LowStar.Ex2.fst \
LowStar.Ex3.fst

include ../Makefile.include

verify-%: __force__
	$(FSTAR) --include $(FSTAR_CONTRIB)/Platform/fst --include $(FSTAR_CONTRIB)/CoreCrypto/fst $*

all: uall sall Ex01a-ocaml

sall:

uall: $(VERFILES:%=verify-%)


# Importing targets for simplified extraction to Ocaml

include $(FSTAR_ULIB)/ml/Makefile.include

out:
	mkdir -p out

HAS_OCAMLFIND := $(shell which ocamlfind 2>/dev/null)

Ex01a-ocaml: out Ex01a.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Ex01a.fst
ifdef HAS_OCAMLFIND
	$(OCAMLOPT) out/Ex01a.ml -o Ex01a.exe 2>&1
	-./Ex01a.exe 2>&1
endif

# # Parameter for interactive mode
# %.fst-in:
# 	@echo $(OPTIONS) \
#  	--include $(FSTAR_HOME)/ulib/hyperstack \
