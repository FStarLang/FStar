.686p
.model flat
.code
.XMM
ALIGN 16
KeyExpansionStdcall@12 proc
  mov eax, dword ptr [esp + 4]
  movdqu xmm1, xmmword ptr [eax + 0]
  mov eax, dword ptr [esp + 8]
  movdqu xmmword ptr [eax + 0], xmm1
  aeskeygenassist xmm2, xmm1, 1
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 16], xmm1
  aeskeygenassist xmm2, xmm1, 2
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 32], xmm1
  aeskeygenassist xmm2, xmm1, 4
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 48], xmm1
  aeskeygenassist xmm2, xmm1, 8
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 64], xmm1
  aeskeygenassist xmm2, xmm1, 16
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 80], xmm1
  aeskeygenassist xmm2, xmm1, 32
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 96], xmm1
  aeskeygenassist xmm2, xmm1, 64
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 112], xmm1
  aeskeygenassist xmm2, xmm1, 128
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 128], xmm1
  aeskeygenassist xmm2, xmm1, 27
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 144], xmm1
  aeskeygenassist xmm2, xmm1, 54
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 160], xmm1
  xor eax, eax
  pxor xmm1, xmm1
  pxor xmm2, xmm2
  pxor xmm3, xmm3
  ret 12
KeyExpansionStdcall@12 endp
ALIGN 16
KeyExpansionAndInversionStdcall@12 proc
  mov eax, dword ptr [esp + 4]
  movdqu xmm1, xmmword ptr [eax + 0]
  mov eax, dword ptr [esp + 8]
  movdqu xmmword ptr [eax + 0], xmm1
  aeskeygenassist xmm2, xmm1, 1
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 16], xmm1
  aeskeygenassist xmm2, xmm1, 2
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 32], xmm1
  aeskeygenassist xmm2, xmm1, 4
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 48], xmm1
  aeskeygenassist xmm2, xmm1, 8
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 64], xmm1
  aeskeygenassist xmm2, xmm1, 16
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 80], xmm1
  aeskeygenassist xmm2, xmm1, 32
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 96], xmm1
  aeskeygenassist xmm2, xmm1, 64
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 112], xmm1
  aeskeygenassist xmm2, xmm1, 128
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 128], xmm1
  aeskeygenassist xmm2, xmm1, 27
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 144], xmm1
  aeskeygenassist xmm2, xmm1, 54
  pshufd xmm2, xmm2, 255
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  vpslldq xmm3, xmm1, 4
  pxor xmm1, xmm3
  pxor xmm1, xmm2
  movdqu xmmword ptr [eax + 160], xmm1
  movdqu xmm1, xmmword ptr [eax + 16]
  aesimc xmm1, xmm1
  movdqu xmmword ptr [eax + 16], xmm1
  movdqu xmm1, xmmword ptr [eax + 32]
  aesimc xmm1, xmm1
  movdqu xmmword ptr [eax + 32], xmm1
  movdqu xmm1, xmmword ptr [eax + 48]
  aesimc xmm1, xmm1
  movdqu xmmword ptr [eax + 48], xmm1
  movdqu xmm1, xmmword ptr [eax + 64]
  aesimc xmm1, xmm1
  movdqu xmmword ptr [eax + 64], xmm1
  movdqu xmm1, xmmword ptr [eax + 80]
  aesimc xmm1, xmm1
  movdqu xmmword ptr [eax + 80], xmm1
  movdqu xmm1, xmmword ptr [eax + 96]
  aesimc xmm1, xmm1
  movdqu xmmword ptr [eax + 96], xmm1
  movdqu xmm1, xmmword ptr [eax + 112]
  aesimc xmm1, xmm1
  movdqu xmmword ptr [eax + 112], xmm1
  movdqu xmm1, xmmword ptr [eax + 128]
  aesimc xmm1, xmm1
  movdqu xmmword ptr [eax + 128], xmm1
  movdqu xmm1, xmmword ptr [eax + 144]
  aesimc xmm1, xmm1
  movdqu xmmword ptr [eax + 144], xmm1
  xor eax, eax
  pxor xmm1, xmm1
  pxor xmm2, xmm2
  pxor xmm3, xmm3
  ret 12
KeyExpansionAndInversionStdcall@12 endp
ALIGN 16
AES128EncryptOneBlockStdcall@16 proc
  mov eax, dword ptr [esp + 8]
  movdqu xmm0, xmmword ptr [eax + 0]
  mov eax, dword ptr [esp + 12]
  movdqu xmm2, xmmword ptr [eax + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  mov eax, dword ptr [esp + 4]
  movdqu xmmword ptr [eax + 0], xmm0
  ret 16
AES128EncryptOneBlockStdcall@16 endp
ALIGN 16
AES128EncryptOneBlock proc
  movdqu xmm2, xmmword ptr [eax + 0]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 16]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 32]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 48]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 64]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 80]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 96]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 112]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 128]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 144]
  aesenc xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 160]
  aesenclast xmm0, xmm2
  pxor xmm2, xmm2
  ret 8
AES128EncryptOneBlock endp
ALIGN 16
AES128DecryptOneBlock proc
  movdqu xmm2, xmmword ptr [eax + 160]
  pxor xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 144]
  aesdec xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 128]
  aesdec xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 112]
  aesdec xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 96]
  aesdec xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 80]
  aesdec xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 64]
  aesdec xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 48]
  aesdec xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 32]
  aesdec xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 16]
  aesdec xmm0, xmm2
  movdqu xmm2, xmmword ptr [eax + 0]
  aesdeclast xmm0, xmm2
  pxor xmm2, xmm2
  ret 8
AES128DecryptOneBlock endp
end
