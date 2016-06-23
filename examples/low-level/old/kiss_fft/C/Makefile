ifeq "$(NFFT)" ""
 NFFT=1800
endif
ifeq "$(NUMFFTS)" ""
 NUMFFTS=10000
endif

ifeq "$(DATATYPE)" ""
 DATATYPE=float
endif

BENCHKISS=bm_kiss_$(DATATYPE)

ifeq  "$(DATATYPE)" "short"
 TYPEFLAGS=-DFIXED_POINT -Dkiss_fft_scalar=short
 SELFTESTSRC=selftest_short.c
else
 TYPEFLAGS=-Dkiss_fft_scalar=$(DATATYPE)
 SELFTESTSRC=selftest.c
endif

ifeq  "$(DATATYPE)" "float"
# fftw needs to be built with --enable-float to build this lib
 FFTWLIB=fftw3f
else
 FFTWLIB=fftw3
endif

SRCFILES=kiss_fft.c pstats.c

all: $(BENCHKISS)

build: all

CFLAGS=-g -Wall -O3

CC=gcc
# If the above flags do not work, try the following
#CFLAGS=-Wall -O3 -I.. -I../tools

$(BENCHKISS): benchkiss.c $(SRCFILES) 
	$(CC) -o $@ $(CFLAGS) $(TYPEFLAGS) -lm  $+

malloc.o: malloc.c
	$(CC) -O3 -c malloc.c

test: $(BENCHKISS)
	./$(BENCHKISS) -x 10000 -n 1800

clean:
	rm -f *~ bm_* st_* tr_* kf_* tkfc_* ff_* ffr_* *.pyc *.pyo *.dat 
