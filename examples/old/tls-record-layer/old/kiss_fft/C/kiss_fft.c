/*
Copyright (c) 2003, Mark Borgerding

All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
    * Neither the author nor the names of any contributors may be used to endorse or promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/


#include "_kiss_fft_guts.h"
/* The guts header contains all the multiplication and addition macros that are defined for
 fixed or floating point complex numbers.  It also delares the kf_ internal functions.
 */

/* the max length of the sequence of factors of nfft , 
 MAXFACTORS==32 this should be good up to more 1e15 samples
 ( 2 * 3**31 )
 */
#define MAXFACTORS 32

static void kf_bfly2(
        kiss_fft_cpx * Fout,
        int fstride,
        const kiss_fft_state * st,
        int m
        )
{
    kiss_fft_cpx * Fout2;
    kiss_fft_cpx * tw1 = st->twiddles;
    kiss_fft_cpx t;
    Fout2 = Fout + m;
    do{
        C_FIXDIV(*Fout,2); C_FIXDIV(*Fout2,2);

        C_MUL (t,  *Fout2 , *tw1);
        tw1 += fstride;
        C_SUB( *Fout2 ,  *Fout , t );
        C_ADDTO( *Fout ,  t );
        ++Fout2;
        ++Fout;
    }while (--m);
}

static void kf_bfly4(
        kiss_fft_cpx * Fout,
        int fstride,
        const kiss_fft_state * st,
        int m
        )
{
    kiss_fft_cpx *Fout1,*Fout2,*Fout3;
    kiss_fft_cpx *tw1,*tw2,*tw3;
    kiss_fft_cpx scratch[6];

    Fout1 = Fout + m;
    Fout2 = Fout + 2*m;
    Fout3 = Fout + 3*m;
    tw3 = tw2 = tw1 = st->twiddles;

    do {
        C_FIXDIV(*Fout,4); C_FIXDIV(*Fout1,4); C_FIXDIV(*Fout2,4); C_FIXDIV(*Fout3,4);

        C_MUL(scratch[0],*Fout1 , *tw1 );
        C_MUL(scratch[1],*Fout2 , *tw2 );
        C_MUL(scratch[2],*Fout3 , *tw3 );

        C_SUB( scratch[5] , *Fout, scratch[1] );
        C_ADDTO(*Fout, scratch[1]);
        C_ADD( scratch[3] , scratch[0] , scratch[2] );
        C_SUB( scratch[4] , scratch[0] , scratch[2] );
        C_SUB( *Fout2, *Fout, scratch[3] );
        tw1 += fstride;
        tw2 += fstride*2;
        tw3 += fstride*3;
        C_ADDTO( *Fout , scratch[3] );

        if(st->inverse) {
            Fout1->r = scratch[5].r - scratch[4].i;
            Fout1->i = scratch[5].i + scratch[4].r;
            Fout3->r = scratch[5].r + scratch[4].i;
            Fout3->i = scratch[5].i - scratch[4].r;
        }else{
            Fout1->r = scratch[5].r + scratch[4].i;
            Fout1->i = scratch[5].i - scratch[4].r;
            Fout3->r = scratch[5].r - scratch[4].i;
            Fout3->i = scratch[5].i + scratch[4].r;
        }
        ++Fout; ++Fout1; ++Fout2; ++Fout3;
    }while(--m);
}

static void kf_bfly3(
         kiss_fft_cpx * Fout,
         int fstride,
         const kiss_fft_state * st,
         int m
         )
{
     kiss_fft_cpx *Fout0,*Fout1,*Fout2;
     kiss_fft_cpx *tw1,*tw2;
     kiss_fft_cpx scratch[5];
     kiss_fft_cpx epi3;
     epi3 = st->twiddles[fstride*m];

     Fout0=Fout;
     Fout1=Fout0+m;
     Fout2=Fout0+2*m;
     tw1=tw2=st->twiddles;

     do{
         C_FIXDIV(*Fout0,3); C_FIXDIV(*Fout1,3); C_FIXDIV(*Fout2,3);

         C_MUL(scratch[1],*Fout1 , *tw1);
         C_MUL(scratch[2],*Fout2 , *tw2);

         C_ADD(scratch[3],scratch[1],scratch[2]);
         C_SUB(scratch[0],scratch[1],scratch[2]);

         Fout1->r = Fout0->r - scratch[3].r/2;
         Fout1->i = Fout0->i - scratch[3].i/2;

         C_MULBYSCALAR( scratch[0] , epi3.i );

         C_ADDTO(*Fout0,scratch[3]);

         Fout2->r = Fout1->r + scratch[0].i;
         Fout2->i = Fout1->i - scratch[0].r;

         Fout1->r -= scratch[0].i;
         Fout1->i += scratch[0].r;

         ++Fout0;++Fout1;++Fout2;
         tw1 += fstride;
         tw2 += fstride*2;
     }while(--m);
}

static void kf_bfly5(
        kiss_fft_cpx * Fout,
        int fstride,
        const kiss_fft_state * st,
        int m
        )
{
    kiss_fft_cpx *Fout0,*Fout1,*Fout2,*Fout3,*Fout4;
    int u;
    kiss_fft_cpx scratch[13];
    kiss_fft_cpx * twiddles = st->twiddles;
    kiss_fft_cpx *tw;
    kiss_fft_cpx y1,y2;
    y1 = twiddles[fstride*m];
    y2 = twiddles[fstride*2*m];

    Fout0=Fout;
    Fout1=Fout0+m;
    Fout2=Fout0+2*m;
    Fout3=Fout0+3*m;
    Fout4=Fout0+4*m;

    tw=st->twiddles;
    for ( u=0; u<m; ++u ) {
        C_FIXDIV( *Fout0,5); C_FIXDIV( *Fout1,5); C_FIXDIV( *Fout2,5); C_FIXDIV( *Fout3,5); C_FIXDIV( *Fout4,5);
        scratch[0] = *Fout0;

        C_MUL(scratch[1] ,*Fout1, tw[u*fstride]);
        C_MUL(scratch[2] ,*Fout2, tw[2*u*fstride]);
        C_MUL(scratch[3] ,*Fout3, tw[3*u*fstride]);
        C_MUL(scratch[4] ,*Fout4, tw[4*u*fstride]);

        C_ADD( scratch[7],scratch[1],scratch[4]);
        C_SUB( scratch[10],scratch[1],scratch[4]);
        C_ADD( scratch[8],scratch[2],scratch[3]);
        C_SUB( scratch[9],scratch[2],scratch[3]);

        Fout0->r += scratch[7].r + scratch[8].r;
        Fout0->i += scratch[7].i + scratch[8].i;

        scratch[5].r = scratch[0].r + S_MUL(scratch[7].r,y1.r) + S_MUL(scratch[8].r,y2.r);
        scratch[5].i = scratch[0].i + S_MUL(scratch[7].i,y1.r) + S_MUL(scratch[8].i,y2.r);

        scratch[6].r =  S_MUL(scratch[10].i,y1.i) + S_MUL(scratch[9].i,y2.i);
        scratch[6].i = -S_MUL(scratch[10].r,y1.i) - S_MUL(scratch[9].r,y2.i);

        C_SUB(*Fout1,scratch[5],scratch[6]);
        C_ADD(*Fout4,scratch[5],scratch[6]);

        scratch[11].r = scratch[0].r + S_MUL(scratch[7].r,y2.r) + S_MUL(scratch[8].r,y1.r);
        scratch[11].i = scratch[0].i + S_MUL(scratch[7].i,y2.r) + S_MUL(scratch[8].i,y1.r);
        scratch[12].r = - S_MUL(scratch[10].i,y2.i) + S_MUL(scratch[9].i,y1.i);
        scratch[12].i = S_MUL(scratch[10].r,y2.i) - S_MUL(scratch[9].r,y1.i);

        C_ADD(*Fout2,scratch[11],scratch[12]);
        C_SUB(*Fout3,scratch[11],scratch[12]);

        ++Fout0;++Fout1;++Fout2;++Fout3;++Fout4;
    }
}

/* perform the butterfly for one stage of a mixed radix FFT */
static void kf_bfly_generic(
        kiss_fft_cpx * Fout,
        int fstride,
        const kiss_fft_state * st,
        int m,
        int p
        )
{
    int u,k,q1,q;
    kiss_fft_cpx * scratch = st->scratch;
    kiss_fft_cpx * twiddles = st->twiddles;
    kiss_fft_cpx t;
    int Norig = st->nfft;

    for ( u=0; u<m; ++u ) {
        k=u;
        for ( q1=0 ; q1<p ; ++q1 ) {
            scratch[q1] = Fout[ k  ];
            C_FIXDIV(scratch[q1],p);
            k += m;
        }

        k=u;
        for ( q1=0 ; q1<p ; ++q1 ) {
            int twidx=0;
            Fout[ k ] = scratch[0];
            for (q=1;q<p;++q ) {
                twidx += fstride * k;
                if (twidx>=Norig) twidx-=Norig;
                C_MUL(t,scratch[q] , twiddles[twidx] );
                C_ADDTO( Fout[ k ] ,t);
            }
            k += m;
        }
    }
}

void kf_work(
        kiss_fft_cpx * Fout,
        const kiss_fft_cpx * f,
        int fstride,
        int in_stride,
        int * factors,
        const kiss_fft_state * st
        )
{
    int m,p,q;
    p=*factors++;
    m=*factors++;

    for (q=0;q<p;++q) {
        if (m==1)
            Fout[q] = *f;
        else
            kf_work( Fout + m*q, f, fstride*p, in_stride, factors,st);
        f += fstride*in_stride;
    }

    switch (p) {
        case 2: kf_bfly2(Fout,fstride,st,m); break;
        case 3: kf_bfly3(Fout,fstride,st,m); break; 
        case 4: kf_bfly4(Fout,fstride,st,m); break;
        case 5: kf_bfly5(Fout,fstride,st,m); break; 
        default: kf_bfly_generic(Fout,fstride,st,m,p); break;
    }
}

/*  facbuf is populated by p1,m1,p2,m2, ...
    where 
    p[i] * m[i] = m[i-1]
    m0 = n                  */
void kf_factor(int n,int * facbuf)
{
    int p=4;
    int floor_sqrt = floor (sqrt (n));

    /*factor out powers of 4, powers of 2, then any remaining primes */
    do {
        while (n % p) {
            switch (p) {
                case 4: p = 2; break;
                case 2: p = 3; break;
                default: p += 2; break;
            }
            if (p > floor_sqrt)
                p = n;          /* no more factors, skip to end */
        }
        n /= p;
        *facbuf++ = p;
        *facbuf++ = n;
    } while (n > 1);
}

/*
 *
 * User-callable function to allocate all necessary scratch space for the fft.
 *
 * The return value is a contiguous block of memory, allocated with malloc.  As such,
 * It can be freed with free(), rather than a kiss_fft-specific function.
 * */
void * kiss_fft_alloc(int nfft,int inverse_fft,void * mem,size_t * lenmem )
{
    kiss_fft_state * st=NULL;
    size_t memneeded = sizeof(kiss_fft_state)
        + sizeof(kiss_fft_cpx)*nfft /* twiddle factors*/
        + sizeof(kiss_fft_cpx)*nfft /* tmpbuf*/
        + sizeof(int)*2*MAXFACTORS /* factors*/
        + sizeof(kiss_fft_cpx)*nfft; /* scratch*/

    if ( lenmem==NULL ) {
        st = ( kiss_fft_state *)malloc( memneeded );
    }else{
        if (*lenmem >= memneeded)
            st = ( kiss_fft_state *)mem;
        *lenmem = memneeded;
    }
    if (st){
        int i;
        st->nfft=nfft;
        st->inverse = inverse_fft;
        st->twiddles = (kiss_fft_cpx*)(st+1); /* just beyond struct*/
        st->tmpbuf = (kiss_fft_cpx*)(st->twiddles + nfft);/*  just after twiddles*/
        st->scratch = (kiss_fft_cpx*)(st->tmpbuf + nfft);
        st->factors = (int*)(st->scratch + nfft);

        for (i=0;i<nfft;++i) {
            const double pi=3.14159265358979323846264338327;
            double phase = ( -2*pi /nfft ) * i;
            if (st->inverse)
                phase *= -1;
            st->twiddles[i] = kf_cexp( phase );
        }

        kf_factor(nfft,st->factors);
    }
    return st;
}

void kiss_fft_stride(const void * cfg,const kiss_fft_cpx *fin,kiss_fft_cpx *fout,int in_stride)
{
    const kiss_fft_state * st = cfg;
    if (st->nfft < 0) {
        fprintf(stderr,"usage error: invalid kiss_fft_state. make sure the correct kiss_fft_alloc routine was used.\n");
        exit(1);
    }

    if (fin == fout) {
        kf_work(st->tmpbuf,fin,1,in_stride, st->factors,st);
        memcpy(fout,st->tmpbuf,sizeof(kiss_fft_cpx)*st->nfft);
    }else{
        kf_work( fout, fin, 1,in_stride, st->factors,st );
    }
}

void kiss_fft(const void * cfg,const kiss_fft_cpx *fin,kiss_fft_cpx *fout)
{
    kiss_fft_stride(cfg,fin,fout,1);
}

