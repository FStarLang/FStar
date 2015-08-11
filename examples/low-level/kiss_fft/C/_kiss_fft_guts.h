/*
Copyright (c) 2003, Mark Borgerding

All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the author nor the names of any contributors may be used to endorse or promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

/* kiss_fft.h
   defines kiss_fft_scalar as either short or a float type
   and defines
   typedef struct { kiss_fft_scalar r; kiss_fft_scalar i; }kiss_fft_cpx; */
#include "kiss_fft.h"

typedef struct {
    int nfft;
    int inverse;
    int *factors;
    kiss_fft_cpx * twiddles;
    kiss_fft_cpx * tmpbuf;
    kiss_fft_cpx * scratch;
}kiss_fft_state;

/*
  Explanation of macros dealing with complex math:

   C_MUL(m,a,b)         : m = a*b
   C_FIXDIV( c , div )  : if a fixed point impl., c /= div. noop otherwise
   C_SUB( res, a,b)     : res = a - b
   C_SUBFROM( res , a)  : res -= a
   C_ADDTO( res , a)    : res += a
 * */
#ifdef FIXED_POINT
#   define S_MUL(a,b) ( ( (a)*(b) + (1<<14) )>>15 )
#   define C_MUL(m,a,b) \
      do{ (m).r = ( ( (a).r*(b).r - (a).i*(b).i)  + (1<<14) ) >> 15;\
          (m).i = ( ( (a).r*(b).i + (a).i*(b).r)  + (1<<14) ) >> 15;\
      }while(0)
#   define C_FIXDIV(c,div) \
    do{ (c).r /= div; (c).i /=div; }while(0)

#   define C_MULBYSCALAR( c, s ) \
    do{ (c).r = ( ( (c).r*(s) ) + (1<<14) ) >> 15;\
        (c).i = ( ( (c).i*(s) ) + (1<<14) ) >> 15; }while(0)

#else  /* not FIXED_POINT*/

#   define S_MUL(a,b) ( (a)*(b) )
#define C_MUL(m,a,b) \
    do{ (m).r = (a).r*(b).r - (a).i*(b).i;\
        (m).i = (a).r*(b).i + (a).i*(b).r; }while(0)
#   define C_FIXDIV(c,div) /* NOOP */
#   define C_MULBYSCALAR( c, s ) \
    do{ (c).r *= (s);\
        (c).i *= (s); }while(0)
#endif

#define  C_ADD( res, a,b)\
    do {    (res).r=(a).r+(b).r;  (res).i=(a).i+(b).i;  }while(0)
#define  C_SUB( res, a,b)\
    do {    (res).r=(a).r-(b).r;  (res).i=(a).i-(b).i;  }while(0)
#define C_ADDTO( res , a)\
    do {    (res).r += (a).r;  (res).i += (a).i;  }while(0)
#define C_SUBFROM( res , a)\
    do {    (res).r -= (a).r;  (res).i -= (a).i;  }while(0)

static inline
kiss_fft_cpx kf_cexp(double phase) /* returns e ** (j*phase)   */
{
    kiss_fft_cpx x;
#ifdef FIXED_POINT
    x.r = (kiss_fft_scalar) (32767 * cos (phase));
    x.i = (kiss_fft_scalar) (32767 * sin (phase));
#else
    x.r = cos (phase);
    x.i = sin (phase);
#endif
    return x;
}

void kf_work(
        kiss_fft_cpx * Fout,
        const kiss_fft_cpx * f,
        int fstride,
        int in_skip,
        int * factors,
        const kiss_fft_state * st
        );

/* a debugging function */
#define pcpx(c)\
    fprintf(stderr,"%g + %gi\n",(double)((c)->r),(double)((c)->i) )
