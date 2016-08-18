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
#currently failing \
Ex05b.fst \


FSTAR_HOME=../../../../
include ../Makefile.include

verify-%: __force__
	$(FSTAR) --record_hints $*

all: uall

sall:

uall: $(VERFILES:%=verify-%)
