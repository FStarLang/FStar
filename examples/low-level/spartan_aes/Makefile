# Override to get cross-compilation
MARCH?=$(shell uname -m)
UNAME?=$(shell uname | cut -c 1-6)

ifeq ($(UNAME),CYGWIN)
  CC=$(MARCH)-w64-mingw32-gcc
else ifeq ($(MARCH),i686)
  CC=gcc -m32
else
  CC=gcc
endif

ifeq ($(UNAME),Darwin)
  VARIANT=-Darwin
else ifeq ($(UNAME),Linux)
  VARIANT=-Linux
endif


all: aes.o sha256.o

%.o: %-$(MARCH)$(VARIANT).S
	$(CC) -c $< -o $@

.PHONY: import
import:
	@if [ x"$(SPARTAN_HOME)" = x ]; then echo "SPARTAN_HOME not defined"; exit 1; fi
	cp $(SPARTAN_HOME)/obj/aes-gcc.S aes-x86_64.S
	cp $(SPARTAN_HOME)/obj/sha256-gcc.S sha256-x86_64.S
	sed -i 's/.section .text/.text/' *.S

clean:
	rm -f *.o *~
