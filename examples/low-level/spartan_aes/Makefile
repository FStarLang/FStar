
MARCH = $(shell uname -m)

ifeq ($(MARCH),x86_64)
  AES = aes_x64.asm
  ML = ml64
  MLSUF = /amd64
else ifeq ($(MARCH),i686)
  AES = aes_i686.asm
  ML = ml
  MLSUF = 
else
  $(error Platform $(MARCH) is not supported)
endif

ifeq (, $(shell which $(ML) 2> /dev/null))
  ifeq ($(OS),Windows_NT)
	ML := "/cygdrive/c/Program Files (x86)/Microsoft Visual Studio 12.0/VC/bin$(MLSUF)/$(ML).exe"
  endif
endif

ifeq (, $(shell which $(ML) 2> /dev/null))
  $(error Command $(ML) not found in $(PATH))
endif

all: aes.o

clean:
	rm -f *.o *~

aes.o: $(AES)
	$(ML) -c -Fo aes.o -coff $^

