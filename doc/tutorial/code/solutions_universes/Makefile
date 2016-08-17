VERFILES=Ex1a.fst \
Ex2a.fst \
Ex3a.fst \
Ex3b.fst \
Ex3c.fst \
Ex4a.fst \
Ex4b.fst \
Ex4c.fst \
<<<<<<< HEAD
Ex4e.fst \
Ex4f.fst \
Ex4g.fst \
Ex4h.fst \
Ex5a.fst \
Ex6a.fst \
Ex6b.fst \
Ex6c.fst \
Ex6d.fst \
=======
Ex4g.fst \
Ex4h.fst \
Ex6a.fst \
>>>>>>> b4b7ae5b8c523c6feb1fd870b17500fde8aa5884
Ex6e.fst \
Ex7a.fst \
Ex7b.fst \
Ex7c.fst \
<<<<<<< HEAD
Ex7d.fst \
#currently failing \
Ex5b.fst \

=======
Ex7d.fst
#files currently not type checking \
Ex4e.fst \
Ex4f.fst \
Ex5a.fst \
Ex5b.fst \
Ex6b.fst \
Ex6c.fst \
Ex6d.fst \
>>>>>>> b4b7ae5b8c523c6feb1fd870b17500fde8aa5884

FSTAR_HOME=../../../../
include ../Makefile.include

verify-%: __force__
	$(FSTAR) --record_hints $*

all: uall

sall:

uall: $(VERFILES:%=verify-%)
