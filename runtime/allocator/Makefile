# Options:
# make DEBUG=y ===> compile with -g, enable debugging printfs
# make NOOPT=y ===> compile with -g, no prints
# make (no options) ===> compile with -O3
# make NOGC=y ===> compile with -O3, disable GC scanning support
# make OPT=y ===> same as NOGC

OCAMLC := ocamlfind ocamlopt
OCAMLLINK := ocamlfind ocamlopt
CMO := cmx

ifdef DEBUG
CFLAGS := -ccopt -DDEBUG
NOOPT := y
endif

ifndef NOOPT
CFLAGS := -ccopt -O3
else
FLAGS := -g 
CFLAGS := $(CFLAGS) -ccopt -g
endif

ifdef OPT
NOGC := y
endif

ifdef NOGC
CFLAGS := $(CFLAGS) -ccopt -DNOGC
endif

ifdef WINDIR
EXE=.exe
else
EXE=
endif

# If for some weird reason, you don't have ocamlfind installed, override it in
# your local config file.
-include Makefile.local

all: stacktest$(EXE) ffitest$(EXE)

stacktest$(EXE): stack.o bitmask.o stacktest.o
	$(OCAMLC) $(FLAGS) -o $@ $^ 

ffitest.$(CMO): camlstack.cmi

ffitest$(EXE): camlstack.o stack.o bitmask.o ffitest.$(CMO)
	$(OCAMLLINK) -o $@ $^

%.cmi: %.mli
	$(OCAMLC) $(FLAGS) -c  $^ -o $@

%.$(CMO): %.ml
	$(OCAMLC) $(FLAGS) -c  $< -o $@

%.o: %.c
	$(OCAMLC) $(FLAGS) $(CFLAGS) -c  $^ -o $@

clean:
	$(RM) *.o *.cm* stacktest$(EXE) ffitest$(EXE)
