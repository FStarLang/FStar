all: aes.o

clean:
	rm aes.o *~

aes.o: aes.asm
	ml -c -Fo aes.o -coff aes.asm
