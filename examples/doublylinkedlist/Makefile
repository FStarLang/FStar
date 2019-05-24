FSTAR_HOME=../..
include ../Makefile.include

all: uall

%.uveri: %.fsti
	$(FSTAR) --use_extracted_interfaces true $^

uall: DoublyLinkedList.uver DoublyLinkedListIface.uver DoublyLinkedListIface.uveri Example.uver 
