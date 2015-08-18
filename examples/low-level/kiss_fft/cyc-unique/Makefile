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

SRCFILES=kiss_fft.cyc pstats.cyc

all: $(BENCHKISS)
build: all
build-nocheck: $(BENCHKISS)-nochk
build-aprof: $(BENCHKISS)-aprof

CFLAGS=-g -Wall -O3 -warnaliascoercion -nogc -noreaps

CC=cyclone
# If the above flags do not work, try the following
#CFLAGS=-Wall -O3 -I.. -I../tools

$(BENCHKISS): benchkiss.cyc $(SRCFILES)
	$(CC) -o $@ $(CFLAGS) $(TYPEFLAGS) -lm  $+

$(BENCHKISS)-nochk: benchkiss.cyc $(SRCFILES)
	$(CC) -o $@ $(CFLAGS) --nochecks $(TYPEFLAGS) -lm  $+

$(BENCHKISS)-aprof: benchkiss.cyc $(SRCFILES)
	$(CC) -o $@ $(CFLAGS) -pa $(TYPEFLAGS) -lm  $+

test: $(BENCHKISS) $(BENCHKISS)-nochk
	./$(BENCHKISS) -x 10000 -n 1800
	./$(BENCHKISS)-nochk -x 10000 -n 1800


clean:
	rm -f *~ bm_* st_* tr_* kf_* tkfc_* ff_* ffr_* *.pyc *.pyo *.dat
