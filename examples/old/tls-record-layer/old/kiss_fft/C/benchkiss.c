#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/times.h>
#include <unistd.h>
#include "kiss_fft.h"

#include "pstats.h"
int main(int argc,char ** argv)
{
    int nfft=1024;
    int isinverse=0;
    int numffts=1000,i;
    kiss_fft_cpx * buf;
    kiss_fft_cpx * bufout;
    void *st;

    while (1) {
      int c = getopt (argc, argv, "n:ix:");
      if (c == -1)
        break;
      switch (c) {
      case 'n':
        nfft = atoi (optarg);
        break;
      case 'x':
        numffts = atoi (optarg);
        break;
      case 'i':
        isinverse = 1;
        break;
      }
    }
    buf=(kiss_fft_cpx*)malloc(sizeof(kiss_fft_cpx) * nfft);
    bufout=(kiss_fft_cpx*)malloc(sizeof(kiss_fft_cpx) * nfft);

    for (i=0;i<nfft;++i ) {
        buf[i].r = rand() - RAND_MAX/2;
        buf[i].i = rand() - RAND_MAX/2;
    }

    pstats_init();

    st = kiss_fft_alloc( nfft ,isinverse ,0,0);

    for (i=0;i<numffts;++i)
        kiss_fft( st ,buf,bufout );

    kiss_fft_free(st);

    free(buf); free(bufout);

    fprintf(stderr,"KISS\tnfft=%d\tnumffts=%d\n" ,nfft,numffts);
    pstats_report();
    return 0;
}

