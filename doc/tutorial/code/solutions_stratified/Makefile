FSTAR_HOME=../../../..
include ../Makefile.include

EXERCISES =\
  ex01a-safe-read-write\
  ex02a-can-read-write-types\
  ex03a-factorial-types\
  ex03b-fibonacci\
  ex03c-fibonacci\
  ex04a-append-intrinsic\
  ex04b-append-extrinsic\
  ex04c-mem\
  ex04d-reverse\
  ex04e-find\
  ex04f-fold-left\
  ex04g-hd-tl\
  ex04h-nth\
  ex05a-rev\
  ex05b-fib\
  ex06a-partition\
  ex06e-insertion-sort\
  ex07a-stlc-typed-step\
  ex07b-stlc-pairs\
  ex07c-stlc-let\
  ex07d-stlc-eval\
  ex10a-acls\
  ex10-shift\
# Files currently not compiling
#  ex06b-sort-poly\
   ex06d-no-discard\

verify-%: __force__
	$(FSTAR) --stratified $*.fst

all: uall sall

uall:

sall: $(EXERCISES:%=verify-%)
