VERFILES=stlc.fst 
include ../Makefile.include
all: .all.ver tinyfstar.vv stlcdb
stlcdb: 
	make stlcdb.fulllib.ver OTHERFLAGS='--z3timeout 10'
