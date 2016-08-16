VERFILES=Ex1a.fst \
Ex2a.fst \
Ex3a.fst \
Ex3b.fst \
Ex3c.fst \
Ex4a.fst \
Ex4b.fst \
Ex4c.fst \
Ex4g.fst \
Ex4h.fst \
Ex6a.fst \
Ex6e.fst \
Ex7a.fst \
Ex7b.fst \
Ex7c.fst \
Ex7d.fst
#files currently not type checking \
Ex4e.fst \
Ex4f.fst \
Ex5a.fst \
Ex5b.fst \
Ex6b.fst \
Ex6c.fst \
Ex6d.fst \

FSTAR_HOME=../../../../
include ../Makefile.include

verify-%: __force__
	$(FSTAR) --record_hints $*

all: uall

uall: $(VERFILES:%=verify-%)
