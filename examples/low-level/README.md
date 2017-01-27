To compile a 32-bit version of OpenSSL and run the tests in 32-bit mode:

jonathan@chartreuse:~/Code/fstar/ucontrib/CoreCrypto/ml/openssl ((174ec01...)) $ KERNEL_BITS=32 ./config no-asm -m32
jonathan@chartreuse:~/Code/fstar/examples/low-level (c_record_aead) $ make test-perf.exe CFLAGS=-m32 KOPTS="-ccopt -m32" -B
