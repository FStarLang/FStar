all: world

LIB_STEEL=../../lib/steel
INCLUDE_STEEL=../../include/steel

world: $(LIB_STEEL)/libsteel.a

steel_spinlock.o: steel_spinlock.c $(INCLUDE_STEEL)/Steel_SpinLock.h
	$(CC) -c -I $(INCLUDE_STEEL) -o $@ $<

$(LIB_STEEL)/libsteel.a: steel_spinlock.o
	ar cr $@ $^

.PHONY: clean
clean:
	rm -f *.o *.a *.krml .depend*

.PHONY: extract
extract:
	+$(MAKE) -f extract.Makefile
