VERFILES=Ex01a.fst \
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
Ex10b.fst

VERFILES_HH=Ex11a.fst

FSTAR_HOME=../../../../
HINTS_ENABLED=--use_hints --record_hints
include ../Makefile.include

HYPERHEAP=$(FSTAR_HOME)/ulib/hyperheap

verify-%: __force__
	$(FSTAR) $*

verify_hh-%: __force__
	$(FSTAR) --include $(HYPERHEAP) $*


all: uall sall

sall:

uall: $(VERFILES:%=verify-%) $(VERFILES_HH:%=verify_hh-%)
