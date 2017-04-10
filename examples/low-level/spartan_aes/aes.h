#include <stdint>

// val keyExpansion: key:skey -> w:xkey -> sb:sbox -> STL unit
extern void Spartan_keyExpansion(char* key, char* expanded_key, char* ignored_sbox);

// val cipher: out:block -> input:block -> w:xkey -> sb:sbox -> STL unit
extern void Spartan_cipher(char* output, char* input, char* expanded_key, char* ignored_sbox);
