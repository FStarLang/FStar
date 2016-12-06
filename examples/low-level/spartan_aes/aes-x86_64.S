.text
.global KeyExpansionStdcall
KeyExpansionStdcall:
  movdqu 0 (%rcx), %xmm1
  movdqu %xmm1, 0 (%rdx)
  aeskeygenassist $1, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 16 (%rdx)
  aeskeygenassist $2, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 32 (%rdx)
  aeskeygenassist $4, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 48 (%rdx)
  aeskeygenassist $8, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 64 (%rdx)
  aeskeygenassist $16, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 80 (%rdx)
  aeskeygenassist $32, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 96 (%rdx)
  aeskeygenassist $64, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 112 (%rdx)
  aeskeygenassist $128, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 128 (%rdx)
  aeskeygenassist $27, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 144 (%rdx)
  aeskeygenassist $54, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 160 (%rdx)
  pxor %xmm1, %xmm1
  pxor %xmm2, %xmm2
  pxor %xmm3, %xmm3
  sub 12, %rsp
  ret 

.global KeyExpansionAndInversionStdcall
KeyExpansionAndInversionStdcall:
  movdqu 0 (%rcx), %xmm1
  movdqu %xmm1, 0 (%rdx)
  aeskeygenassist $1, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 16 (%rdx)
  aeskeygenassist $2, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 32 (%rdx)
  aeskeygenassist $4, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 48 (%rdx)
  aeskeygenassist $8, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 64 (%rdx)
  aeskeygenassist $16, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 80 (%rdx)
  aeskeygenassist $32, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 96 (%rdx)
  aeskeygenassist $64, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 112 (%rdx)
  aeskeygenassist $128, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 128 (%rdx)
  aeskeygenassist $27, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 144 (%rdx)
  aeskeygenassist $54, %xmm1, %xmm2
  pshufd $255, %xmm2, %xmm2
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  vpslldq $4, %xmm1, %xmm3
  pxor %xmm3, %xmm1
  pxor %xmm2, %xmm1
  movdqu %xmm1, 160 (%rdx)
  movdqu 16 (%rdx), %xmm1
  aesimc %xmm1, %xmm1
  movdqu %xmm1, 16 (%rdx)
  movdqu 32 (%rdx), %xmm1
  aesimc %xmm1, %xmm1
  movdqu %xmm1, 32 (%rdx)
  movdqu 48 (%rdx), %xmm1
  aesimc %xmm1, %xmm1
  movdqu %xmm1, 48 (%rdx)
  movdqu 64 (%rdx), %xmm1
  aesimc %xmm1, %xmm1
  movdqu %xmm1, 64 (%rdx)
  movdqu 80 (%rdx), %xmm1
  aesimc %xmm1, %xmm1
  movdqu %xmm1, 80 (%rdx)
  movdqu 96 (%rdx), %xmm1
  aesimc %xmm1, %xmm1
  movdqu %xmm1, 96 (%rdx)
  movdqu 112 (%rdx), %xmm1
  aesimc %xmm1, %xmm1
  movdqu %xmm1, 112 (%rdx)
  movdqu 128 (%rdx), %xmm1
  aesimc %xmm1, %xmm1
  movdqu %xmm1, 128 (%rdx)
  movdqu 144 (%rdx), %xmm1
  aesimc %xmm1, %xmm1
  movdqu %xmm1, 144 (%rdx)
  pxor %xmm1, %xmm1
  pxor %xmm2, %xmm2
  pxor %xmm3, %xmm3
  sub 12, %rsp
  ret 

.global AES128EncryptOneBlockStdcall
AES128EncryptOneBlockStdcall:
  movdqu 0 (%rdx), %xmm0
  movdqu 0 (%r8), %xmm2
  pxor %xmm2, %xmm0
  movdqu 16 (%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 32 (%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 48 (%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 64 (%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 80 (%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 96 (%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 112 (%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 128 (%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 144 (%r8), %xmm2
  aesenc %xmm2, %xmm0
  movdqu 160 (%r8), %xmm2
  aesenclast %xmm2, %xmm0
  pxor %xmm2, %xmm2
  movdqu %xmm0, 0 (%rcx)
  sub 16, %rsp
  ret 


