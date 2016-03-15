#include <stdint.h>
#include <stdio.h>
#include "fstarlib.h"

void init_key(char key[]){
  unsigned char i;
  for(i=0; i<32; i++){
    key[i] = i;
  }
}

void print_array(uint32* array, int len){
  unsigned char i;
  for (i=0; i < len; i++){
    printf("%x ", array[i] & 0xffffffff);
  }
  printf("\n");
}

void print_bytes(char* bytes, int len){
  unsigned char i;
  for (i=0; i < len; i++){
    printf("%x ", bytes[i] & 0xff);
    if ((i+1) % 16 == 0) {printf("\n");}
  }
  printf("\n");
}

int main(int argc, char** argv){
  uint8 key[32];
  uint8 test[64], test2[64];
  uint32 state[16]= {0};
  uint8 nonce[12] = {0,0,0,0,0,0,0,0x4a,0,0,0,0};
  uint8* plaintext = "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
  uint8 ciphertext[128] = {0};
  uint8* expected = "000  6e 2e 35 9a 25 68 f9 80 41 ba 07 28 dd 0d 69 81  n.5.%h..A..(..i.\n016  e9 7e 7a ec 1d 43 60 c2 0a 27 af cc fd 9f ae 0b  .~z..C`..'......\n032  f9 1b 65 c5 52 47 33 ab 8f 59 3d ab cd 62 b3 57  ..e.RG3..Y=..b.W\n048  16 39 d6 24 e6 51 52 ab 8f 53 0c 35 9f 08 61 d8  .9.$.QR..S.5..a.\n064  07 ca 0d bf 50 0d 6a 61 56 a3 8e 08 8a 22 b6 5e  ....P.jaV....\".^\n080  52 bc 51 4d 16 cc f8 06 81 8c e9 1a b7 79 37 36  R.QM.........y76\n096  5a f9 0b bf 74 a3 5b e6 b4 0b 8e ed f2 78 5e 42  Z...t.[......x^B\n112  87 4d\n";

  uint64 counter = 1;
  init_key(key);
  
  //FStar_SBytes_sbytes_of_uint32s(test, state, 16); 
  //Chacha_chacha20_block (ciphertext, state, key, 0, nonce);
  //Chacha_chacha20_encrypt_loop(ciphertext, key, counter, nonce, plaintext, 0, 0);
  /*
  print_array((uint32*)nonce, 3);
  Chacha_initialize_state(state, key, counter, nonce);
  print_array(state, 16);

  Chacha_chacha20_block (ciphertext, state, key, 1, nonce);
  print_array(state, 16);
  */
  printf("Running 1.000.000 iterations of chacha's test vector from RFC\n");
  unsigned int i;
  for(i=0;i<1000000;i++){
    Chacha_chacha20_encrypt(ciphertext, key, counter, nonce, plaintext, 114);
  }
  printf("Expected:\n%s\nGot:\n", expected);
  print_bytes(ciphertext, 114);
  return 0;
}
