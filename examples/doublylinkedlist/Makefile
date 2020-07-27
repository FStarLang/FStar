FSTAR_HOME=../..
include ../Makefile.include

all: uall

%.uveri: %.fsti
	$(FSTAR) $^

uall: DoublyLinkedList.uver DoublyLinkedListIface.uver DoublyLinkedListIface.uveri Example.uver 
