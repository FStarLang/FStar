#ifndef KISS_FFT_H
#define KISS_FFT_H

#include <stdlib.h>
#include <stdio.h>
#include <math.h>

/*
 ATTENTION!
 If you would like a :
 -- a utility that will handle the caching of fft objects
 -- real-only FFT
 -- a multi-dimensional FFT
 -- a command-line utility to perform ffts
 -- a command-line utility to perform fast-convolution filtering

 then see tools/
 */

#ifdef FIXED_POINT
# define kiss_fft_scalar short
#else
# ifndef kiss_fft_scalar
/*  default is float */
#   define kiss_fft_scalar float
# endif
#endif

typedef struct KISS_FFT_CPX {
  kiss_fft_scalar r;
  kiss_fft_scalar i;
}kiss_fft_cpx;

typedef struct KISS_FFT_STATE {
    int nfft;
    int inverse;
    int ?factors;
    kiss_fft_cpx ? twiddles;
    kiss_fft_cpx ? tmpbuf;
    kiss_fft_cpx ? scratch;
}kiss_fft_state;


/* 
 *  kiss_fft_alloc
 *  
 *  Initialize a FFT (or IFFT) algorithm's cfg/state buffer.
 *
 *  typical usage:      void * mycfg=kiss_fft_alloc(1024,0,NULL,NULL);
 *
 *  The return value from fft_alloc is a cfg buffer used internally
 *  by the fft routine or NULL.
 *
 *  If lenmem is NULL, then kiss_fft_alloc will allocate a cfg buffer using malloc.
 *  The returned value should be free()d when done to avoid memory leaks.
 *  
 *  The state can be placed in a user supplied buffer 'mem':
 *  If lenmem is not NULL and mem is not NULL and *lenmem is large enough,
 *      then the function places the cfg in mem and the size used in *lenmem
 *      and returns mem.
 *  
 *  If lenmem is not NULL and ( mem is NULL or *lenmem is not large enough),
 *      then the function returns NULL and places the minimum cfg 
 *      buffer size in *lenmem.
 * */
kiss_fft_state @`r+`H  kiss_fft_alloc(int nfft, int inverse_fft, kiss_fft_state *`r+`H mem); 

/*
 * kiss_fft(cfg,in_out_buf)
 *
 * Perform an FFT on a complex input buffer.
 * for a forward FFT,
 * fin should be  f[0] , f[1] , ... ,f[nfft-1]
 * fout will be   F[0] , F[1] , ... ,F[nfft-1]
 * Note that each element is complex and can be accessed like
    f[k].r and f[k].i
 * */
void kiss_fft(const kiss_fft_state *  cfg, const kiss_fft_cpx ?fin, kiss_fft_cpx ?fout);

void kiss_fft_stride(const kiss_fft_state * cfg, const kiss_fft_cpx ?fin, kiss_fft_cpx ?fout, int fin_stride);

/* If kiss_fft_alloc allocated a buffer, it is one contiguous 
   buffer and can be simply free()d when no longer needed*/
#define kiss_fft_free free

#endif
