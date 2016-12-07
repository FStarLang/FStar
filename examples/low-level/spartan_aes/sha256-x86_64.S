.text
.global sha256_main_i_SHA256_Compute64Steps
sha256_main_i_SHA256_Compute64Steps:
  mov %rdx, %r9
  movq %rcx, 96(%rsp)
  mov $0, %r8d
  mov $0, %r11d
  movl 0 (%rcx), %r11d
  movl 4 (%rcx), %r8d
  movl %r8d, 40(%rsp)
  movl 8 (%rcx), %r8d
  movl %r8d, 44(%rsp)
  movl 12 (%rcx), %r8d
  movl %r8d, 48(%rsp)
  movl 16 (%rcx), %r8d
  movl %r8d, 52(%rsp)
  movl 20 (%rcx), %r8d
  movl %r8d, 56(%rsp)
  movl 24 (%rcx), %r8d
  movl %r8d, 60(%rsp)
  movl 28 (%rcx), %r8d
  movl %r8d, 64(%rsp)
  mov $0, %eax
  mov $0, %ecx
  mov $0, %edx
  mov $0, %r10d
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1116352408, %r8d
  movl 0 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1899447441, %r8d
  movl 4 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3049323471, %r8d
  movl 8 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3921009573, %r8d
  movl 12 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $961987163, %r8d
  movl 16 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1508970993, %r8d
  movl 20 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2453635748, %r8d
  movl 24 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2870763221, %r8d
  movl 28 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3624381080, %r8d
  movl 32 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $310598401, %r8d
  movl 36 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $607225278, %r8d
  movl 40 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1426881987, %r8d
  movl 44 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1925078388, %r8d
  movl 48 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2162078206, %r8d
  movl 52 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2614888103, %r8d
  movl 56 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3248222580, %r8d
  movl 60 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3835390401, %r8d
  movl 64 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $4022224774, %r8d
  movl 68 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $264347078, %r8d
  movl 72 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $604807628, %r8d
  movl 76 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $770255983, %r8d
  movl 80 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1249150122, %r8d
  movl 84 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1555081692, %r8d
  movl 88 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1996064986, %r8d
  movl 92 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2554220882, %r8d
  movl 96 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2821834349, %r8d
  movl 100 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2952996808, %r8d
  movl 104 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3210313671, %r8d
  movl 108 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3336571891, %r8d
  movl 112 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3584528711, %r8d
  movl 116 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $113926993, %r8d
  movl 120 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $338241895, %r8d
  movl 124 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $666307205, %r8d
  movl 128 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $773529912, %r8d
  movl 132 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1294757372, %r8d
  movl 136 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1396182291, %r8d
  movl 140 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1695183700, %r8d
  movl 144 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1986661051, %r8d
  movl 148 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2177026350, %r8d
  movl 152 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2456956037, %r8d
  movl 156 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2730485921, %r8d
  movl 160 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2820302411, %r8d
  movl 164 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3259730800, %r8d
  movl 168 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3345764771, %r8d
  movl 172 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3516065817, %r8d
  movl 176 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3600352804, %r8d
  movl 180 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $4094571909, %r8d
  movl 184 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $275423344, %r8d
  movl 188 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $430227734, %r8d
  movl 192 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $506948616, %r8d
  movl 196 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $659060556, %r8d
  movl 200 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $883997877, %r8d
  movl 204 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $958139571, %r8d
  movl 208 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1322822218, %r8d
  movl 212 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1537002063, %r8d
  movl 216 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1747873779, %r8d
  movl 220 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $1955562222, %r8d
  movl 224 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2024104815, %r8d
  movl 228 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2227730452, %r8d
  movl 232 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2361852424, %r8d
  movl 236 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2428436474, %r8d
  movl 240 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $2756734187, %r8d
  movl 244 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  mov %r11d, %eax
  movl %eax, 68(%rsp)
  movl 40(%rsp), %r8d
  movl %r8d, 72(%rsp)
  movl 44(%rsp), %ecx
  movl %ecx, 76(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 52(%rsp), %r8d
  movl %r8d, 84(%rsp)
  mov %r8d, %edx
  not %edx
  movl 60(%rsp), %ecx
  movl %ecx, 92(%rsp)
  and %ecx, %edx
  movl 56(%rsp), %ecx
  movl %ecx, 88(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 64(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3204031479, %r8d
  movl 248 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 48(%rsp), %eax
  add %r8d, %eax
  movl %eax, 80(%rsp)
  mov %r11d, %eax
  movl %eax, 40(%rsp)
  movl 68(%rsp), %r8d
  movl %r8d, 44(%rsp)
  movl 72(%rsp), %ecx
  movl %ecx, 48(%rsp)
  mov %r8d, %edx
  and %eax, %r8d
  and %ecx, %edx
  and %eax, %ecx
  xor %ecx, %r8d
  xor %edx, %r8d
  mov %eax, %ecx
  mov %eax, %edx
  ror $2, %eax
  ror $13, %ecx
  xor %ecx, %eax
  ror $22, %edx
  xor %edx, %eax
  add %r8d, %eax
  movl 80(%rsp), %r8d
  movl %r8d, 56(%rsp)
  mov %r8d, %edx
  not %edx
  movl 88(%rsp), %ecx
  movl %ecx, 64(%rsp)
  and %ecx, %edx
  movl 84(%rsp), %ecx
  movl %ecx, 60(%rsp)
  and %r8d, %ecx
  xor %edx, %ecx
  mov %r8d, %edx
  mov %r8d, %r10d
  ror $6, %edx
  ror $11, %r10d
  xor %r10d, %edx
  ror $25, %r8d
  xor %r8d, %edx
  movl 92(%rsp), %r8d
  add %edx, %r8d
  add %ecx, %r8d
  add $3329325298, %r8d
  movl 252 (%r9), %ecx
  add %ecx, %r8d
  add %r8d, %eax
  mov %eax, %r11d
  movl 76(%rsp), %eax
  add %r8d, %eax
  movl %eax, 52(%rsp)
  movq 96(%rsp), %rcx
  movl 0 (%rcx), %r8d
  add %r11d, %r8d
  movl %r8d, 0 (%rcx)
  movl 4 (%rcx), %r8d
  movl 40(%rsp), %r11d
  add %r11d, %r8d
  movl %r8d, 4 (%rcx)
  movl 8 (%rcx), %r8d
  movl 44(%rsp), %r11d
  add %r11d, %r8d
  movl %r8d, 8 (%rcx)
  movl 12 (%rcx), %r8d
  movl 48(%rsp), %r11d
  add %r11d, %r8d
  movl %r8d, 12 (%rcx)
  movl 16 (%rcx), %r8d
  movl 52(%rsp), %r11d
  add %r11d, %r8d
  movl %r8d, 16 (%rcx)
  movl 20 (%rcx), %r8d
  movl 56(%rsp), %r11d
  add %r11d, %r8d
  movl %r8d, 20 (%rcx)
  movl 24 (%rcx), %r8d
  movl 60(%rsp), %r11d
  add %r11d, %r8d
  movl %r8d, 24 (%rcx)
  movl 28 (%rcx), %r8d
  movl 64(%rsp), %r11d
  add %r11d, %r8d
  movl %r8d, 28 (%rcx)
  movl $0, 40(%rsp)
  movl $0, 44(%rsp)
  movl $0, 48(%rsp)
  movl $0, 52(%rsp)
  movl $0, 56(%rsp)
  movl $0, 60(%rsp)
  movl $0, 64(%rsp)
  movl $0, 68(%rsp)
  movl $0, 72(%rsp)
  movl $0, 76(%rsp)
  movl $0, 80(%rsp)
  movl $0, 84(%rsp)
  movl $0, 88(%rsp)
  movl $0, 92(%rsp)
  movl $0, 96(%rsp)
  movl $0, 100(%rsp)
  movl $0, 104(%rsp)
  movl $0, 108(%rsp)
  movl $0, 112(%rsp)
  sub $112, %rsp
  ret 

.global sha256_main_i_SHA256_ComputeInitialWs
sha256_main_i_SHA256_ComputeInitialWs:
  mov %rcx, %r10
  add %rdx, %r10
  mov %r8, %r9
  mov $0, %eax
  mov $0, %ecx
  mov $0, %edx
  mov $0, %r8d
  mov $0, %r11d
  movl 0 (%r10), %eax
  bswap %eax
  movl 4 (%r10), %r8d
  bswap %r8d
  movl 8 (%r10), %ecx
  bswap %ecx
  movl 12 (%r10), %edx
  bswap %edx
  movl 16 (%r10), %r11d
  bswap %r11d
  movl %eax, 0 (%r9)
  movl %r8d, 4 (%r9)
  movl %ecx, 8 (%r9)
  movl %edx, 12 (%r9)
  movl %r11d, 16 (%r9)
  movl 20 (%r10), %eax
  bswap %eax
  movl 24 (%r10), %r8d
  bswap %r8d
  movl 28 (%r10), %ecx
  bswap %ecx
  movl 32 (%r10), %edx
  bswap %edx
  movl 36 (%r10), %r11d
  bswap %r11d
  movl %eax, 20 (%r9)
  movl %r8d, 24 (%r9)
  movl %ecx, 28 (%r9)
  movl %edx, 32 (%r9)
  movl %r11d, 36 (%r9)
  movl 40 (%r10), %eax
  bswap %eax
  movl 44 (%r10), %r8d
  bswap %r8d
  movl 48 (%r10), %ecx
  bswap %ecx
  movl 52 (%r10), %edx
  bswap %edx
  movl 56 (%r10), %r11d
  bswap %r11d
  movl %eax, 40 (%r9)
  movl %r8d, 44 (%r9)
  movl %ecx, 48 (%r9)
  movl %edx, 52 (%r9)
  movl %r11d, 56 (%r9)
  movl 60 (%r10), %eax
  bswap %eax
  movl %eax, 60 (%r9)
  movl 56 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 36 (%r9), %edx
  add %r8d, %edx
  movl 4 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 0 (%r9), %eax
  add %eax, %edx
  movl %edx, 64 (%r9)
  movl 60 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 40 (%r9), %edx
  add %r8d, %edx
  movl 8 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 4 (%r9), %eax
  add %eax, %edx
  movl %edx, 68 (%r9)
  movl 64 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 44 (%r9), %edx
  add %r8d, %edx
  movl 12 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 8 (%r9), %eax
  add %eax, %edx
  movl %edx, 72 (%r9)
  movl 68 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 48 (%r9), %edx
  add %r8d, %edx
  movl 16 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 12 (%r9), %eax
  add %eax, %edx
  movl %edx, 76 (%r9)
  movl 72 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 52 (%r9), %edx
  add %r8d, %edx
  movl 20 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 16 (%r9), %eax
  add %eax, %edx
  movl %edx, 80 (%r9)
  movl 76 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 56 (%r9), %edx
  add %r8d, %edx
  movl 24 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 20 (%r9), %eax
  add %eax, %edx
  movl %edx, 84 (%r9)
  movl 80 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 60 (%r9), %edx
  add %r8d, %edx
  movl 28 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 24 (%r9), %eax
  add %eax, %edx
  movl %edx, 88 (%r9)
  movl 84 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 64 (%r9), %edx
  add %r8d, %edx
  movl 32 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 28 (%r9), %eax
  add %eax, %edx
  movl %edx, 92 (%r9)
  movl 88 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 68 (%r9), %edx
  add %r8d, %edx
  movl 36 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 32 (%r9), %eax
  add %eax, %edx
  movl %edx, 96 (%r9)
  movl 92 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 72 (%r9), %edx
  add %r8d, %edx
  movl 40 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 36 (%r9), %eax
  add %eax, %edx
  movl %edx, 100 (%r9)
  movl 96 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 76 (%r9), %edx
  add %r8d, %edx
  movl 44 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 40 (%r9), %eax
  add %eax, %edx
  movl %edx, 104 (%r9)
  movl 100 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 80 (%r9), %edx
  add %r8d, %edx
  movl 48 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 44 (%r9), %eax
  add %eax, %edx
  movl %edx, 108 (%r9)
  movl 104 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 84 (%r9), %edx
  add %r8d, %edx
  movl 52 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 48 (%r9), %eax
  add %eax, %edx
  movl %edx, 112 (%r9)
  movl 108 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 88 (%r9), %edx
  add %r8d, %edx
  movl 56 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 52 (%r9), %eax
  add %eax, %edx
  movl %edx, 116 (%r9)
  movl 112 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 92 (%r9), %edx
  add %r8d, %edx
  movl 60 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 56 (%r9), %eax
  add %eax, %edx
  movl %edx, 120 (%r9)
  movl 116 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 96 (%r9), %edx
  add %r8d, %edx
  movl 64 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 60 (%r9), %eax
  add %eax, %edx
  movl %edx, 124 (%r9)
  movl 120 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 100 (%r9), %edx
  add %r8d, %edx
  movl 68 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 64 (%r9), %eax
  add %eax, %edx
  movl %edx, 128 (%r9)
  movl 124 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 104 (%r9), %edx
  add %r8d, %edx
  movl 72 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 68 (%r9), %eax
  add %eax, %edx
  movl %edx, 132 (%r9)
  movl 128 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 108 (%r9), %edx
  add %r8d, %edx
  movl 76 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 72 (%r9), %eax
  add %eax, %edx
  movl %edx, 136 (%r9)
  movl 132 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 112 (%r9), %edx
  add %r8d, %edx
  movl 80 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 76 (%r9), %eax
  add %eax, %edx
  movl %edx, 140 (%r9)
  movl 136 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 116 (%r9), %edx
  add %r8d, %edx
  movl 84 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 80 (%r9), %eax
  add %eax, %edx
  movl %edx, 144 (%r9)
  movl 140 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 120 (%r9), %edx
  add %r8d, %edx
  movl 88 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 84 (%r9), %eax
  add %eax, %edx
  movl %edx, 148 (%r9)
  movl 144 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 124 (%r9), %edx
  add %r8d, %edx
  movl 92 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 88 (%r9), %eax
  add %eax, %edx
  movl %edx, 152 (%r9)
  movl 148 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 128 (%r9), %edx
  add %r8d, %edx
  movl 96 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 92 (%r9), %eax
  add %eax, %edx
  movl %edx, 156 (%r9)
  movl 152 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 132 (%r9), %edx
  add %r8d, %edx
  movl 100 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 96 (%r9), %eax
  add %eax, %edx
  movl %edx, 160 (%r9)
  movl 156 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 136 (%r9), %edx
  add %r8d, %edx
  movl 104 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 100 (%r9), %eax
  add %eax, %edx
  movl %edx, 164 (%r9)
  movl 160 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 140 (%r9), %edx
  add %r8d, %edx
  movl 108 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 104 (%r9), %eax
  add %eax, %edx
  movl %edx, 168 (%r9)
  movl 164 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 144 (%r9), %edx
  add %r8d, %edx
  movl 112 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 108 (%r9), %eax
  add %eax, %edx
  movl %edx, 172 (%r9)
  movl 168 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 148 (%r9), %edx
  add %r8d, %edx
  movl 116 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 112 (%r9), %eax
  add %eax, %edx
  movl %edx, 176 (%r9)
  movl 172 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 152 (%r9), %edx
  add %r8d, %edx
  movl 120 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 116 (%r9), %eax
  add %eax, %edx
  movl %edx, 180 (%r9)
  movl 176 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 156 (%r9), %edx
  add %r8d, %edx
  movl 124 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 120 (%r9), %eax
  add %eax, %edx
  movl %edx, 184 (%r9)
  movl 180 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 160 (%r9), %edx
  add %r8d, %edx
  movl 128 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 124 (%r9), %eax
  add %eax, %edx
  movl %edx, 188 (%r9)
  movl 184 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 164 (%r9), %edx
  add %r8d, %edx
  movl 132 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 128 (%r9), %eax
  add %eax, %edx
  movl %edx, 192 (%r9)
  movl 188 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 168 (%r9), %edx
  add %r8d, %edx
  movl 136 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 132 (%r9), %eax
  add %eax, %edx
  movl %edx, 196 (%r9)
  movl 192 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 172 (%r9), %edx
  add %r8d, %edx
  movl 140 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 136 (%r9), %eax
  add %eax, %edx
  movl %edx, 200 (%r9)
  movl 196 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 176 (%r9), %edx
  add %r8d, %edx
  movl 144 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 140 (%r9), %eax
  add %eax, %edx
  movl %edx, 204 (%r9)
  movl 200 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 180 (%r9), %edx
  add %r8d, %edx
  movl 148 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 144 (%r9), %eax
  add %eax, %edx
  movl %edx, 208 (%r9)
  movl 204 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 184 (%r9), %edx
  add %r8d, %edx
  movl 152 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 148 (%r9), %eax
  add %eax, %edx
  movl %edx, 212 (%r9)
  movl 208 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 188 (%r9), %edx
  add %r8d, %edx
  movl 156 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 152 (%r9), %eax
  add %eax, %edx
  movl %edx, 216 (%r9)
  movl 212 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 192 (%r9), %edx
  add %r8d, %edx
  movl 160 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 156 (%r9), %eax
  add %eax, %edx
  movl %edx, 220 (%r9)
  movl 216 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 196 (%r9), %edx
  add %r8d, %edx
  movl 164 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 160 (%r9), %eax
  add %eax, %edx
  movl %edx, 224 (%r9)
  movl 220 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 200 (%r9), %edx
  add %r8d, %edx
  movl 168 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 164 (%r9), %eax
  add %eax, %edx
  movl %edx, 228 (%r9)
  movl 224 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 204 (%r9), %edx
  add %r8d, %edx
  movl 172 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 168 (%r9), %eax
  add %eax, %edx
  movl %edx, 232 (%r9)
  movl 228 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 208 (%r9), %edx
  add %r8d, %edx
  movl 176 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 172 (%r9), %eax
  add %eax, %edx
  movl %edx, 236 (%r9)
  movl 232 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 212 (%r9), %edx
  add %r8d, %edx
  movl 180 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 176 (%r9), %eax
  add %eax, %edx
  movl %edx, 240 (%r9)
  movl 236 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 216 (%r9), %edx
  add %r8d, %edx
  movl 184 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 180 (%r9), %eax
  add %eax, %edx
  movl %edx, 244 (%r9)
  movl 240 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 220 (%r9), %edx
  add %r8d, %edx
  movl 188 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 184 (%r9), %eax
  add %eax, %edx
  movl %edx, 248 (%r9)
  movl 244 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $17, %r8d
  ror $19, %ecx
  xor %ecx, %r8d
  shr $10, %eax
  xor %eax, %r8d
  movl 224 (%r9), %edx
  add %r8d, %edx
  movl 192 (%r9), %eax
  mov %eax, %r8d
  mov %eax, %ecx
  ror $7, %r8d
  ror $18, %ecx
  xor %ecx, %r8d
  shr $3, %eax
  xor %eax, %r8d
  add %r8d, %edx
  movl 188 (%r9), %eax
  add %eax, %edx
  movl %edx, 252 (%r9)
  sub $0, %rsp
  ret 


