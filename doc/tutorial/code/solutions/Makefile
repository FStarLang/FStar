FSTAR_HOME=../../../..
include ../Makefile.include

EXERCISES =\
  ex1a-safe-read-write\
  ex2a-can-read-write-types\
  ex3a-factorial-types\
  ex3b-fibonacci\
  ex3c-fibonacci\
  ex4a-append-intrinsic\
  ex4b-append-extrinsic\
  ex4c-mem\
  ex4d-reverse\
  ex4e-find\
  ex4f-fold-left\
  ex4g-hd-tl\
  ex4h-nth\
  ex5a-rev\
  ex5b-fib\
  ex6a-partition\
  ex6e-insertion-sort\
  ex7a-stlc-typed-step\
  ex7b-stlc-pairs\
  ex7c-stlc-let\
  ex7d-stlc-eval\
  ex10a-acls\
  ex10-shift\
# Files currently not compiling
#  ex6b-sort-poly\
   ex6d-no-discard\

verify-%: __force__
	$(SFSTAR) $*.fst

all: uall sall

uall:

sall: $(EXERCISES:%=verify-%)
