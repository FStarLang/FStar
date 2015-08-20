ifdef WINDIR
EXE=.exe
else
EXE=
endif

OCAMLC := ocamlfind ocamlopt
OCAMLLINK := ocamlfind ocamlopt

ifndef OPT
FLAGS := -g 
CFLAGS := -ccopt -g
ifdef DEBUG
CFLAGS := $(CFLAGS) -ccopt -DDEBUG
endif
else
NOGC := y
CFLAGS := -ccopt -O3
endif
CMO := cmx

ifdef NOGC
CFLAGS := $(CFLAGS) -ccopt -DNOGC
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
