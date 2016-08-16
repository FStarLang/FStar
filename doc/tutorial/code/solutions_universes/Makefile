VERFILES=Ex1a.fst Ex3c.fst Ex4d.fst Ex4h.fst Ex6b.fst Ex7a.fst Ex2a.fst Ex4a.fst Ex4e.fst Ex5a.fst Ex6c.fst Ex7b.fst Ex3a.fst Ex4b.fst Ex4f.fst Ex5b.fst Ex6d.fst Ex7c.fst Ex3b.fst Ex4c.fst Ex4g.fst Ex6a.fst Ex6e.fst Ex7d.fst

FSTAR_HOME=../../../../
include ../Makefile.include

verify-%: __force__
	$(FSTAR) $*

all: $(VERFILES:%=verify-%)
