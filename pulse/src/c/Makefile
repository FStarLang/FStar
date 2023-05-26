all: world

LIB_STEEL=../../lib/steel
INCLUDE_STEEL=../../include/steel

world: $(LIB_STEEL)/libsteel.a

steel_spinlock.o: steel_spinlock.c $(INCLUDE_STEEL)/Steel_SpinLock.h
	$(CC) -Werror -c -I $(INCLUDE_STEEL) -o $@ $<

$(LIB_STEEL)/libsteel.a: steel_spinlock.o
	ar cr $@ $^

.PHONY: clean
clean:
	rm -f *.o *.a *.krml .depend*

.PHONY: extract
extract:
	+$(MAKE) -f extract.Makefile

install: $(addsuffix .install,$(wildcard *.c))

.PHONY: %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(STEEL_INSTALL_PREFIX)/src/c/$<

.PHONY: install
