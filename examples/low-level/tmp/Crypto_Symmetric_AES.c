#include "Crypto_Symmetric_AES.h"

Prims_nat Crypto_Symmetric_AES_v(uint32_t x)
{
  return FStar_UInt32_v(x);
}

uint32_t Crypto_Symmetric_AES_nb = (uint32_t )4;

uint32_t Crypto_Symmetric_AES_nk = (uint32_t )8;

uint32_t Crypto_Symmetric_AES_nr = (uint32_t )14;

uint32_t Crypto_Symmetric_AES_blocklen = (uint32_t )16;

uint32_t Crypto_Symmetric_AES_keylen = (uint32_t )32;

uint32_t Crypto_Symmetric_AES_xkeylen = (uint32_t )240;

uint8_t Crypto_Symmetric_AES_xtime(uint8_t b)
{
  return b << (uint32_t )1 ^ (b >> (uint32_t )7 & (uint8_t )1) * (uint8_t )0x1b;
}

uint8_t Crypto_Symmetric_AES_multiply(uint8_t a, uint8_t b)
{
  return
    a
    * (b & (uint8_t )1)
    ^
      Crypto_Symmetric_AES_xtime(a)
      * (b >> (uint32_t )1 & (uint8_t )1)
      ^
        Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(a))
        * (b >> (uint32_t )2 & (uint8_t )1)
        ^
          Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(a)))
          * (b >> (uint32_t )3 & (uint8_t )1)
          ^
            Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(a))))
            * (b >> (uint32_t )4 & (uint8_t )1)
            ^
              Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(a)))))
              * (b >> (uint32_t )5 & (uint8_t )1)
              ^
                Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(a))))))
                * (b >> (uint32_t )6 & (uint8_t )1)
                ^
                  Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(Crypto_Symmetric_AES_xtime(a)))))))
                  * (b >> (uint32_t )7 & (uint8_t )1);
}

void Crypto_Symmetric_AES_mk_sbox(uint8_t *sbox)
{
  sbox[(uint32_t )0] = (uint8_t )0x63;
  sbox[(uint32_t )1] = (uint8_t )0x7c;
  sbox[(uint32_t )2] = (uint8_t )0x77;
  sbox[(uint32_t )3] = (uint8_t )0x7b;
  sbox[(uint32_t )4] = (uint8_t )0xf2;
  sbox[(uint32_t )5] = (uint8_t )0x6b;
  sbox[(uint32_t )6] = (uint8_t )0x6f;
  sbox[(uint32_t )7] = (uint8_t )0xc5;
  sbox[(uint32_t )8] = (uint8_t )0x30;
  sbox[(uint32_t )9] = (uint8_t )0x01;
  sbox[(uint32_t )10] = (uint8_t )0x67;
  sbox[(uint32_t )11] = (uint8_t )0x2b;
  sbox[(uint32_t )12] = (uint8_t )0xfe;
  sbox[(uint32_t )13] = (uint8_t )0xd7;
  sbox[(uint32_t )14] = (uint8_t )0xab;
  sbox[(uint32_t )15] = (uint8_t )0x76;
  sbox[(uint32_t )16] = (uint8_t )0xca;
  sbox[(uint32_t )17] = (uint8_t )0x82;
  sbox[(uint32_t )18] = (uint8_t )0xc9;
  sbox[(uint32_t )19] = (uint8_t )0x7d;
  sbox[(uint32_t )20] = (uint8_t )0xfa;
  sbox[(uint32_t )21] = (uint8_t )0x59;
  sbox[(uint32_t )22] = (uint8_t )0x47;
  sbox[(uint32_t )23] = (uint8_t )0xf0;
  sbox[(uint32_t )24] = (uint8_t )0xad;
  sbox[(uint32_t )25] = (uint8_t )0xd4;
  sbox[(uint32_t )26] = (uint8_t )0xa2;
  sbox[(uint32_t )27] = (uint8_t )0xaf;
  sbox[(uint32_t )28] = (uint8_t )0x9c;
  sbox[(uint32_t )29] = (uint8_t )0xa4;
  sbox[(uint32_t )30] = (uint8_t )0x72;
  sbox[(uint32_t )31] = (uint8_t )0xc0;
  sbox[(uint32_t )32] = (uint8_t )0xb7;
  sbox[(uint32_t )33] = (uint8_t )0xfd;
  sbox[(uint32_t )34] = (uint8_t )0x93;
  sbox[(uint32_t )35] = (uint8_t )0x26;
  sbox[(uint32_t )36] = (uint8_t )0x36;
  sbox[(uint32_t )37] = (uint8_t )0x3f;
  sbox[(uint32_t )38] = (uint8_t )0xf7;
  sbox[(uint32_t )39] = (uint8_t )0xcc;
  sbox[(uint32_t )40] = (uint8_t )0x34;
  sbox[(uint32_t )41] = (uint8_t )0xa5;
  sbox[(uint32_t )42] = (uint8_t )0xe5;
  sbox[(uint32_t )43] = (uint8_t )0xf1;
  sbox[(uint32_t )44] = (uint8_t )0x71;
  sbox[(uint32_t )45] = (uint8_t )0xd8;
  sbox[(uint32_t )46] = (uint8_t )0x31;
  sbox[(uint32_t )47] = (uint8_t )0x15;
  sbox[(uint32_t )48] = (uint8_t )0x04;
  sbox[(uint32_t )49] = (uint8_t )0xc7;
  sbox[(uint32_t )50] = (uint8_t )0x23;
  sbox[(uint32_t )51] = (uint8_t )0xc3;
  sbox[(uint32_t )52] = (uint8_t )0x18;
  sbox[(uint32_t )53] = (uint8_t )0x96;
  sbox[(uint32_t )54] = (uint8_t )0x05;
  sbox[(uint32_t )55] = (uint8_t )0x9a;
  sbox[(uint32_t )56] = (uint8_t )0x07;
  sbox[(uint32_t )57] = (uint8_t )0x12;
  sbox[(uint32_t )58] = (uint8_t )0x80;
  sbox[(uint32_t )59] = (uint8_t )0xe2;
  sbox[(uint32_t )60] = (uint8_t )0xeb;
  sbox[(uint32_t )61] = (uint8_t )0x27;
  sbox[(uint32_t )62] = (uint8_t )0xb2;
  sbox[(uint32_t )63] = (uint8_t )0x75;
  sbox[(uint32_t )64] = (uint8_t )0x09;
  sbox[(uint32_t )65] = (uint8_t )0x83;
  sbox[(uint32_t )66] = (uint8_t )0x2c;
  sbox[(uint32_t )67] = (uint8_t )0x1a;
  sbox[(uint32_t )68] = (uint8_t )0x1b;
  sbox[(uint32_t )69] = (uint8_t )0x6e;
  sbox[(uint32_t )70] = (uint8_t )0x5a;
  sbox[(uint32_t )71] = (uint8_t )0xa0;
  sbox[(uint32_t )72] = (uint8_t )0x52;
  sbox[(uint32_t )73] = (uint8_t )0x3b;
  sbox[(uint32_t )74] = (uint8_t )0xd6;
  sbox[(uint32_t )75] = (uint8_t )0xb3;
  sbox[(uint32_t )76] = (uint8_t )0x29;
  sbox[(uint32_t )77] = (uint8_t )0xe3;
  sbox[(uint32_t )78] = (uint8_t )0x2f;
  sbox[(uint32_t )79] = (uint8_t )0x84;
  sbox[(uint32_t )80] = (uint8_t )0x53;
  sbox[(uint32_t )81] = (uint8_t )0xd1;
  sbox[(uint32_t )82] = (uint8_t )0x00;
  sbox[(uint32_t )83] = (uint8_t )0xed;
  sbox[(uint32_t )84] = (uint8_t )0x20;
  sbox[(uint32_t )85] = (uint8_t )0xfc;
  sbox[(uint32_t )86] = (uint8_t )0xb1;
  sbox[(uint32_t )87] = (uint8_t )0x5b;
  sbox[(uint32_t )88] = (uint8_t )0x6a;
  sbox[(uint32_t )89] = (uint8_t )0xcb;
  sbox[(uint32_t )90] = (uint8_t )0xbe;
  sbox[(uint32_t )91] = (uint8_t )0x39;
  sbox[(uint32_t )92] = (uint8_t )0x4a;
  sbox[(uint32_t )93] = (uint8_t )0x4c;
  sbox[(uint32_t )94] = (uint8_t )0x58;
  sbox[(uint32_t )95] = (uint8_t )0xcf;
  sbox[(uint32_t )96] = (uint8_t )0xd0;
  sbox[(uint32_t )97] = (uint8_t )0xef;
  sbox[(uint32_t )98] = (uint8_t )0xaa;
  sbox[(uint32_t )99] = (uint8_t )0xfb;
  sbox[(uint32_t )100] = (uint8_t )0x43;
  sbox[(uint32_t )101] = (uint8_t )0x4d;
  sbox[(uint32_t )102] = (uint8_t )0x33;
  sbox[(uint32_t )103] = (uint8_t )0x85;
  sbox[(uint32_t )104] = (uint8_t )0x45;
  sbox[(uint32_t )105] = (uint8_t )0xf9;
  sbox[(uint32_t )106] = (uint8_t )0x02;
  sbox[(uint32_t )107] = (uint8_t )0x7f;
  sbox[(uint32_t )108] = (uint8_t )0x50;
  sbox[(uint32_t )109] = (uint8_t )0x3c;
  sbox[(uint32_t )110] = (uint8_t )0x9f;
  sbox[(uint32_t )111] = (uint8_t )0xa8;
  sbox[(uint32_t )112] = (uint8_t )0x51;
  sbox[(uint32_t )113] = (uint8_t )0xa3;
  sbox[(uint32_t )114] = (uint8_t )0x40;
  sbox[(uint32_t )115] = (uint8_t )0x8f;
  sbox[(uint32_t )116] = (uint8_t )0x92;
  sbox[(uint32_t )117] = (uint8_t )0x9d;
  sbox[(uint32_t )118] = (uint8_t )0x38;
  sbox[(uint32_t )119] = (uint8_t )0xf5;
  sbox[(uint32_t )120] = (uint8_t )0xbc;
  sbox[(uint32_t )121] = (uint8_t )0xb6;
  sbox[(uint32_t )122] = (uint8_t )0xda;
  sbox[(uint32_t )123] = (uint8_t )0x21;
  sbox[(uint32_t )124] = (uint8_t )0x10;
  sbox[(uint32_t )125] = (uint8_t )0xff;
  sbox[(uint32_t )126] = (uint8_t )0xf3;
  sbox[(uint32_t )127] = (uint8_t )0xd2;
  sbox[(uint32_t )128] = (uint8_t )0xcd;
  sbox[(uint32_t )129] = (uint8_t )0x0c;
  sbox[(uint32_t )130] = (uint8_t )0x13;
  sbox[(uint32_t )131] = (uint8_t )0xec;
  sbox[(uint32_t )132] = (uint8_t )0x5f;
  sbox[(uint32_t )133] = (uint8_t )0x97;
  sbox[(uint32_t )134] = (uint8_t )0x44;
  sbox[(uint32_t )135] = (uint8_t )0x17;
  sbox[(uint32_t )136] = (uint8_t )0xc4;
  sbox[(uint32_t )137] = (uint8_t )0xa7;
  sbox[(uint32_t )138] = (uint8_t )0x7e;
  sbox[(uint32_t )139] = (uint8_t )0x3d;
  sbox[(uint32_t )140] = (uint8_t )0x64;
  sbox[(uint32_t )141] = (uint8_t )0x5d;
  sbox[(uint32_t )142] = (uint8_t )0x19;
  sbox[(uint32_t )143] = (uint8_t )0x73;
  sbox[(uint32_t )144] = (uint8_t )0x60;
  sbox[(uint32_t )145] = (uint8_t )0x81;
  sbox[(uint32_t )146] = (uint8_t )0x4f;
  sbox[(uint32_t )147] = (uint8_t )0xdc;
  sbox[(uint32_t )148] = (uint8_t )0x22;
  sbox[(uint32_t )149] = (uint8_t )0x2a;
  sbox[(uint32_t )150] = (uint8_t )0x90;
  sbox[(uint32_t )151] = (uint8_t )0x88;
  sbox[(uint32_t )152] = (uint8_t )0x46;
  sbox[(uint32_t )153] = (uint8_t )0xee;
  sbox[(uint32_t )154] = (uint8_t )0xb8;
  sbox[(uint32_t )155] = (uint8_t )0x14;
  sbox[(uint32_t )156] = (uint8_t )0xde;
  sbox[(uint32_t )157] = (uint8_t )0x5e;
  sbox[(uint32_t )158] = (uint8_t )0x0b;
  sbox[(uint32_t )159] = (uint8_t )0xdb;
  sbox[(uint32_t )160] = (uint8_t )0xe0;
  sbox[(uint32_t )161] = (uint8_t )0x32;
  sbox[(uint32_t )162] = (uint8_t )0x3a;
  sbox[(uint32_t )163] = (uint8_t )0x0a;
  sbox[(uint32_t )164] = (uint8_t )0x49;
  sbox[(uint32_t )165] = (uint8_t )0x06;
  sbox[(uint32_t )166] = (uint8_t )0x24;
  sbox[(uint32_t )167] = (uint8_t )0x5c;
  sbox[(uint32_t )168] = (uint8_t )0xc2;
  sbox[(uint32_t )169] = (uint8_t )0xd3;
  sbox[(uint32_t )170] = (uint8_t )0xac;
  sbox[(uint32_t )171] = (uint8_t )0x62;
  sbox[(uint32_t )172] = (uint8_t )0x91;
  sbox[(uint32_t )173] = (uint8_t )0x95;
  sbox[(uint32_t )174] = (uint8_t )0xe4;
  sbox[(uint32_t )175] = (uint8_t )0x79;
  sbox[(uint32_t )176] = (uint8_t )0xe7;
  sbox[(uint32_t )177] = (uint8_t )0xc8;
  sbox[(uint32_t )178] = (uint8_t )0x37;
  sbox[(uint32_t )179] = (uint8_t )0x6d;
  sbox[(uint32_t )180] = (uint8_t )0x8d;
  sbox[(uint32_t )181] = (uint8_t )0xd5;
  sbox[(uint32_t )182] = (uint8_t )0x4e;
  sbox[(uint32_t )183] = (uint8_t )0xa9;
  sbox[(uint32_t )184] = (uint8_t )0x6c;
  sbox[(uint32_t )185] = (uint8_t )0x56;
  sbox[(uint32_t )186] = (uint8_t )0xf4;
  sbox[(uint32_t )187] = (uint8_t )0xea;
  sbox[(uint32_t )188] = (uint8_t )0x65;
  sbox[(uint32_t )189] = (uint8_t )0x7a;
  sbox[(uint32_t )190] = (uint8_t )0xae;
  sbox[(uint32_t )191] = (uint8_t )0x08;
  sbox[(uint32_t )192] = (uint8_t )0xba;
  sbox[(uint32_t )193] = (uint8_t )0x78;
  sbox[(uint32_t )194] = (uint8_t )0x25;
  sbox[(uint32_t )195] = (uint8_t )0x2e;
  sbox[(uint32_t )196] = (uint8_t )0x1c;
  sbox[(uint32_t )197] = (uint8_t )0xa6;
  sbox[(uint32_t )198] = (uint8_t )0xb4;
  sbox[(uint32_t )199] = (uint8_t )0xc6;
  sbox[(uint32_t )200] = (uint8_t )0xe8;
  sbox[(uint32_t )201] = (uint8_t )0xdd;
  sbox[(uint32_t )202] = (uint8_t )0x74;
  sbox[(uint32_t )203] = (uint8_t )0x1f;
  sbox[(uint32_t )204] = (uint8_t )0x4b;
  sbox[(uint32_t )205] = (uint8_t )0xbd;
  sbox[(uint32_t )206] = (uint8_t )0x8b;
  sbox[(uint32_t )207] = (uint8_t )0x8a;
  sbox[(uint32_t )208] = (uint8_t )0x70;
  sbox[(uint32_t )209] = (uint8_t )0x3e;
  sbox[(uint32_t )210] = (uint8_t )0xb5;
  sbox[(uint32_t )211] = (uint8_t )0x66;
  sbox[(uint32_t )212] = (uint8_t )0x48;
  sbox[(uint32_t )213] = (uint8_t )0x03;
  sbox[(uint32_t )214] = (uint8_t )0xf6;
  sbox[(uint32_t )215] = (uint8_t )0x0e;
  sbox[(uint32_t )216] = (uint8_t )0x61;
  sbox[(uint32_t )217] = (uint8_t )0x35;
  sbox[(uint32_t )218] = (uint8_t )0x57;
  sbox[(uint32_t )219] = (uint8_t )0xb9;
  sbox[(uint32_t )220] = (uint8_t )0x86;
  sbox[(uint32_t )221] = (uint8_t )0xc1;
  sbox[(uint32_t )222] = (uint8_t )0x1d;
  sbox[(uint32_t )223] = (uint8_t )0x9e;
  sbox[(uint32_t )224] = (uint8_t )0xe1;
  sbox[(uint32_t )225] = (uint8_t )0xf8;
  sbox[(uint32_t )226] = (uint8_t )0x98;
  sbox[(uint32_t )227] = (uint8_t )0x11;
  sbox[(uint32_t )228] = (uint8_t )0x69;
  sbox[(uint32_t )229] = (uint8_t )0xd9;
  sbox[(uint32_t )230] = (uint8_t )0x8e;
  sbox[(uint32_t )231] = (uint8_t )0x94;
  sbox[(uint32_t )232] = (uint8_t )0x9b;
  sbox[(uint32_t )233] = (uint8_t )0x1e;
  sbox[(uint32_t )234] = (uint8_t )0x87;
  sbox[(uint32_t )235] = (uint8_t )0xe9;
  sbox[(uint32_t )236] = (uint8_t )0xce;
  sbox[(uint32_t )237] = (uint8_t )0x55;
  sbox[(uint32_t )238] = (uint8_t )0x28;
  sbox[(uint32_t )239] = (uint8_t )0xdf;
  sbox[(uint32_t )240] = (uint8_t )0x8c;
  sbox[(uint32_t )241] = (uint8_t )0xa1;
  sbox[(uint32_t )242] = (uint8_t )0x89;
  sbox[(uint32_t )243] = (uint8_t )0x0d;
  sbox[(uint32_t )244] = (uint8_t )0xbf;
  sbox[(uint32_t )245] = (uint8_t )0xe6;
  sbox[(uint32_t )246] = (uint8_t )0x42;
  sbox[(uint32_t )247] = (uint8_t )0x68;
  sbox[(uint32_t )248] = (uint8_t )0x41;
  sbox[(uint32_t )249] = (uint8_t )0x99;
  sbox[(uint32_t )250] = (uint8_t )0x2d;
  sbox[(uint32_t )251] = (uint8_t )0x0f;
  sbox[(uint32_t )252] = (uint8_t )0xb0;
  sbox[(uint32_t )253] = (uint8_t )0x54;
  sbox[(uint32_t )254] = (uint8_t )0xbb;
  sbox[(uint32_t )255] = (uint8_t )0x16;
}

void Crypto_Symmetric_AES_mk_inv_sbox(uint8_t *sbox)
{
  sbox[(uint32_t )0] = (uint8_t )0x52;
  sbox[(uint32_t )1] = (uint8_t )0x09;
  sbox[(uint32_t )2] = (uint8_t )0x6a;
  sbox[(uint32_t )3] = (uint8_t )0xd5;
  sbox[(uint32_t )4] = (uint8_t )0x30;
  sbox[(uint32_t )5] = (uint8_t )0x36;
  sbox[(uint32_t )6] = (uint8_t )0xa5;
  sbox[(uint32_t )7] = (uint8_t )0x38;
  sbox[(uint32_t )8] = (uint8_t )0xbf;
  sbox[(uint32_t )9] = (uint8_t )0x40;
  sbox[(uint32_t )10] = (uint8_t )0xa3;
  sbox[(uint32_t )11] = (uint8_t )0x9e;
  sbox[(uint32_t )12] = (uint8_t )0x81;
  sbox[(uint32_t )13] = (uint8_t )0xf3;
  sbox[(uint32_t )14] = (uint8_t )0xd7;
  sbox[(uint32_t )15] = (uint8_t )0xfb;
  sbox[(uint32_t )16] = (uint8_t )0x7c;
  sbox[(uint32_t )17] = (uint8_t )0xe3;
  sbox[(uint32_t )18] = (uint8_t )0x39;
  sbox[(uint32_t )19] = (uint8_t )0x82;
  sbox[(uint32_t )20] = (uint8_t )0x9b;
  sbox[(uint32_t )21] = (uint8_t )0x2f;
  sbox[(uint32_t )22] = (uint8_t )0xff;
  sbox[(uint32_t )23] = (uint8_t )0x87;
  sbox[(uint32_t )24] = (uint8_t )0x34;
  sbox[(uint32_t )25] = (uint8_t )0x8e;
  sbox[(uint32_t )26] = (uint8_t )0x43;
  sbox[(uint32_t )27] = (uint8_t )0x44;
  sbox[(uint32_t )28] = (uint8_t )0xc4;
  sbox[(uint32_t )29] = (uint8_t )0xde;
  sbox[(uint32_t )30] = (uint8_t )0xe9;
  sbox[(uint32_t )31] = (uint8_t )0xcb;
  sbox[(uint32_t )32] = (uint8_t )0x54;
  sbox[(uint32_t )33] = (uint8_t )0x7b;
  sbox[(uint32_t )34] = (uint8_t )0x94;
  sbox[(uint32_t )35] = (uint8_t )0x32;
  sbox[(uint32_t )36] = (uint8_t )0xa6;
  sbox[(uint32_t )37] = (uint8_t )0xc2;
  sbox[(uint32_t )38] = (uint8_t )0x23;
  sbox[(uint32_t )39] = (uint8_t )0x3d;
  sbox[(uint32_t )40] = (uint8_t )0xee;
  sbox[(uint32_t )41] = (uint8_t )0x4c;
  sbox[(uint32_t )42] = (uint8_t )0x95;
  sbox[(uint32_t )43] = (uint8_t )0x0b;
  sbox[(uint32_t )44] = (uint8_t )0x42;
  sbox[(uint32_t )45] = (uint8_t )0xfa;
  sbox[(uint32_t )46] = (uint8_t )0xc3;
  sbox[(uint32_t )47] = (uint8_t )0x4e;
  sbox[(uint32_t )48] = (uint8_t )0x08;
  sbox[(uint32_t )49] = (uint8_t )0x2e;
  sbox[(uint32_t )50] = (uint8_t )0xa1;
  sbox[(uint32_t )51] = (uint8_t )0x66;
  sbox[(uint32_t )52] = (uint8_t )0x28;
  sbox[(uint32_t )53] = (uint8_t )0xd9;
  sbox[(uint32_t )54] = (uint8_t )0x24;
  sbox[(uint32_t )55] = (uint8_t )0xb2;
  sbox[(uint32_t )56] = (uint8_t )0x76;
  sbox[(uint32_t )57] = (uint8_t )0x5b;
  sbox[(uint32_t )58] = (uint8_t )0xa2;
  sbox[(uint32_t )59] = (uint8_t )0x49;
  sbox[(uint32_t )60] = (uint8_t )0x6d;
  sbox[(uint32_t )61] = (uint8_t )0x8b;
  sbox[(uint32_t )62] = (uint8_t )0xd1;
  sbox[(uint32_t )63] = (uint8_t )0x25;
  sbox[(uint32_t )64] = (uint8_t )0x72;
  sbox[(uint32_t )65] = (uint8_t )0xf8;
  sbox[(uint32_t )66] = (uint8_t )0xf6;
  sbox[(uint32_t )67] = (uint8_t )0x64;
  sbox[(uint32_t )68] = (uint8_t )0x86;
  sbox[(uint32_t )69] = (uint8_t )0x68;
  sbox[(uint32_t )70] = (uint8_t )0x98;
  sbox[(uint32_t )71] = (uint8_t )0x16;
  sbox[(uint32_t )72] = (uint8_t )0xd4;
  sbox[(uint32_t )73] = (uint8_t )0xa4;
  sbox[(uint32_t )74] = (uint8_t )0x5c;
  sbox[(uint32_t )75] = (uint8_t )0xcc;
  sbox[(uint32_t )76] = (uint8_t )0x5d;
  sbox[(uint32_t )77] = (uint8_t )0x65;
  sbox[(uint32_t )78] = (uint8_t )0xb6;
  sbox[(uint32_t )79] = (uint8_t )0x92;
  sbox[(uint32_t )80] = (uint8_t )0x6c;
  sbox[(uint32_t )81] = (uint8_t )0x70;
  sbox[(uint32_t )82] = (uint8_t )0x48;
  sbox[(uint32_t )83] = (uint8_t )0x50;
  sbox[(uint32_t )84] = (uint8_t )0xfd;
  sbox[(uint32_t )85] = (uint8_t )0xed;
  sbox[(uint32_t )86] = (uint8_t )0xb9;
  sbox[(uint32_t )87] = (uint8_t )0xda;
  sbox[(uint32_t )88] = (uint8_t )0x5e;
  sbox[(uint32_t )89] = (uint8_t )0x15;
  sbox[(uint32_t )90] = (uint8_t )0x46;
  sbox[(uint32_t )91] = (uint8_t )0x57;
  sbox[(uint32_t )92] = (uint8_t )0xa7;
  sbox[(uint32_t )93] = (uint8_t )0x8d;
  sbox[(uint32_t )94] = (uint8_t )0x9d;
  sbox[(uint32_t )95] = (uint8_t )0x84;
  sbox[(uint32_t )96] = (uint8_t )0x90;
  sbox[(uint32_t )97] = (uint8_t )0xd8;
  sbox[(uint32_t )98] = (uint8_t )0xab;
  sbox[(uint32_t )99] = (uint8_t )0x00;
  sbox[(uint32_t )100] = (uint8_t )0x8c;
  sbox[(uint32_t )101] = (uint8_t )0xbc;
  sbox[(uint32_t )102] = (uint8_t )0xd3;
  sbox[(uint32_t )103] = (uint8_t )0x0a;
  sbox[(uint32_t )104] = (uint8_t )0xf7;
  sbox[(uint32_t )105] = (uint8_t )0xe4;
  sbox[(uint32_t )106] = (uint8_t )0x58;
  sbox[(uint32_t )107] = (uint8_t )0x05;
  sbox[(uint32_t )108] = (uint8_t )0xb8;
  sbox[(uint32_t )109] = (uint8_t )0xb3;
  sbox[(uint32_t )110] = (uint8_t )0x45;
  sbox[(uint32_t )111] = (uint8_t )0x06;
  sbox[(uint32_t )112] = (uint8_t )0xd0;
  sbox[(uint32_t )113] = (uint8_t )0x2c;
  sbox[(uint32_t )114] = (uint8_t )0x1e;
  sbox[(uint32_t )115] = (uint8_t )0x8f;
  sbox[(uint32_t )116] = (uint8_t )0xca;
  sbox[(uint32_t )117] = (uint8_t )0x3f;
  sbox[(uint32_t )118] = (uint8_t )0x0f;
  sbox[(uint32_t )119] = (uint8_t )0x02;
  sbox[(uint32_t )120] = (uint8_t )0xc1;
  sbox[(uint32_t )121] = (uint8_t )0xaf;
  sbox[(uint32_t )122] = (uint8_t )0xbd;
  sbox[(uint32_t )123] = (uint8_t )0x03;
  sbox[(uint32_t )124] = (uint8_t )0x01;
  sbox[(uint32_t )125] = (uint8_t )0x13;
  sbox[(uint32_t )126] = (uint8_t )0x8a;
  sbox[(uint32_t )127] = (uint8_t )0x6b;
  sbox[(uint32_t )128] = (uint8_t )0x3a;
  sbox[(uint32_t )129] = (uint8_t )0x91;
  sbox[(uint32_t )130] = (uint8_t )0x11;
  sbox[(uint32_t )131] = (uint8_t )0x41;
  sbox[(uint32_t )132] = (uint8_t )0x4f;
  sbox[(uint32_t )133] = (uint8_t )0x67;
  sbox[(uint32_t )134] = (uint8_t )0xdc;
  sbox[(uint32_t )135] = (uint8_t )0xea;
  sbox[(uint32_t )136] = (uint8_t )0x97;
  sbox[(uint32_t )137] = (uint8_t )0xf2;
  sbox[(uint32_t )138] = (uint8_t )0xcf;
  sbox[(uint32_t )139] = (uint8_t )0xce;
  sbox[(uint32_t )140] = (uint8_t )0xf0;
  sbox[(uint32_t )141] = (uint8_t )0xb4;
  sbox[(uint32_t )142] = (uint8_t )0xe6;
  sbox[(uint32_t )143] = (uint8_t )0x73;
  sbox[(uint32_t )144] = (uint8_t )0x96;
  sbox[(uint32_t )145] = (uint8_t )0xac;
  sbox[(uint32_t )146] = (uint8_t )0x74;
  sbox[(uint32_t )147] = (uint8_t )0x22;
  sbox[(uint32_t )148] = (uint8_t )0xe7;
  sbox[(uint32_t )149] = (uint8_t )0xad;
  sbox[(uint32_t )150] = (uint8_t )0x35;
  sbox[(uint32_t )151] = (uint8_t )0x85;
  sbox[(uint32_t )152] = (uint8_t )0xe2;
  sbox[(uint32_t )153] = (uint8_t )0xf9;
  sbox[(uint32_t )154] = (uint8_t )0x37;
  sbox[(uint32_t )155] = (uint8_t )0xe8;
  sbox[(uint32_t )156] = (uint8_t )0x1c;
  sbox[(uint32_t )157] = (uint8_t )0x75;
  sbox[(uint32_t )158] = (uint8_t )0xdf;
  sbox[(uint32_t )159] = (uint8_t )0x6e;
  sbox[(uint32_t )160] = (uint8_t )0x47;
  sbox[(uint32_t )161] = (uint8_t )0xf1;
  sbox[(uint32_t )162] = (uint8_t )0x1a;
  sbox[(uint32_t )163] = (uint8_t )0x71;
  sbox[(uint32_t )164] = (uint8_t )0x1d;
  sbox[(uint32_t )165] = (uint8_t )0x29;
  sbox[(uint32_t )166] = (uint8_t )0xc5;
  sbox[(uint32_t )167] = (uint8_t )0x89;
  sbox[(uint32_t )168] = (uint8_t )0x6f;
  sbox[(uint32_t )169] = (uint8_t )0xb7;
  sbox[(uint32_t )170] = (uint8_t )0x62;
  sbox[(uint32_t )171] = (uint8_t )0x0e;
  sbox[(uint32_t )172] = (uint8_t )0xaa;
  sbox[(uint32_t )173] = (uint8_t )0x18;
  sbox[(uint32_t )174] = (uint8_t )0xbe;
  sbox[(uint32_t )175] = (uint8_t )0x1b;
  sbox[(uint32_t )176] = (uint8_t )0xfc;
  sbox[(uint32_t )177] = (uint8_t )0x56;
  sbox[(uint32_t )178] = (uint8_t )0x3e;
  sbox[(uint32_t )179] = (uint8_t )0x4b;
  sbox[(uint32_t )180] = (uint8_t )0xc6;
  sbox[(uint32_t )181] = (uint8_t )0xd2;
  sbox[(uint32_t )182] = (uint8_t )0x79;
  sbox[(uint32_t )183] = (uint8_t )0x20;
  sbox[(uint32_t )184] = (uint8_t )0x9a;
  sbox[(uint32_t )185] = (uint8_t )0xdb;
  sbox[(uint32_t )186] = (uint8_t )0xc0;
  sbox[(uint32_t )187] = (uint8_t )0xfe;
  sbox[(uint32_t )188] = (uint8_t )0x78;
  sbox[(uint32_t )189] = (uint8_t )0xcd;
  sbox[(uint32_t )190] = (uint8_t )0x5a;
  sbox[(uint32_t )191] = (uint8_t )0xf4;
  sbox[(uint32_t )192] = (uint8_t )0x1f;
  sbox[(uint32_t )193] = (uint8_t )0xdd;
  sbox[(uint32_t )194] = (uint8_t )0xa8;
  sbox[(uint32_t )195] = (uint8_t )0x33;
  sbox[(uint32_t )196] = (uint8_t )0x88;
  sbox[(uint32_t )197] = (uint8_t )0x07;
  sbox[(uint32_t )198] = (uint8_t )0xc7;
  sbox[(uint32_t )199] = (uint8_t )0x31;
  sbox[(uint32_t )200] = (uint8_t )0xb1;
  sbox[(uint32_t )201] = (uint8_t )0x12;
  sbox[(uint32_t )202] = (uint8_t )0x10;
  sbox[(uint32_t )203] = (uint8_t )0x59;
  sbox[(uint32_t )204] = (uint8_t )0x27;
  sbox[(uint32_t )205] = (uint8_t )0x80;
  sbox[(uint32_t )206] = (uint8_t )0xec;
  sbox[(uint32_t )207] = (uint8_t )0x5f;
  sbox[(uint32_t )208] = (uint8_t )0x60;
  sbox[(uint32_t )209] = (uint8_t )0x51;
  sbox[(uint32_t )210] = (uint8_t )0x7f;
  sbox[(uint32_t )211] = (uint8_t )0xa9;
  sbox[(uint32_t )212] = (uint8_t )0x19;
  sbox[(uint32_t )213] = (uint8_t )0xb5;
  sbox[(uint32_t )214] = (uint8_t )0x4a;
  sbox[(uint32_t )215] = (uint8_t )0x0d;
  sbox[(uint32_t )216] = (uint8_t )0x2d;
  sbox[(uint32_t )217] = (uint8_t )0xe5;
  sbox[(uint32_t )218] = (uint8_t )0x7a;
  sbox[(uint32_t )219] = (uint8_t )0x9f;
  sbox[(uint32_t )220] = (uint8_t )0x93;
  sbox[(uint32_t )221] = (uint8_t )0xc9;
  sbox[(uint32_t )222] = (uint8_t )0x9c;
  sbox[(uint32_t )223] = (uint8_t )0xef;
  sbox[(uint32_t )224] = (uint8_t )0xa0;
  sbox[(uint32_t )225] = (uint8_t )0xe0;
  sbox[(uint32_t )226] = (uint8_t )0x3b;
  sbox[(uint32_t )227] = (uint8_t )0x4d;
  sbox[(uint32_t )228] = (uint8_t )0xae;
  sbox[(uint32_t )229] = (uint8_t )0x2a;
  sbox[(uint32_t )230] = (uint8_t )0xf5;
  sbox[(uint32_t )231] = (uint8_t )0xb0;
  sbox[(uint32_t )232] = (uint8_t )0xc8;
  sbox[(uint32_t )233] = (uint8_t )0xeb;
  sbox[(uint32_t )234] = (uint8_t )0xbb;
  sbox[(uint32_t )235] = (uint8_t )0x3c;
  sbox[(uint32_t )236] = (uint8_t )0x83;
  sbox[(uint32_t )237] = (uint8_t )0x53;
  sbox[(uint32_t )238] = (uint8_t )0x99;
  sbox[(uint32_t )239] = (uint8_t )0x61;
  sbox[(uint32_t )240] = (uint8_t )0x17;
  sbox[(uint32_t )241] = (uint8_t )0x2b;
  sbox[(uint32_t )242] = (uint8_t )0x04;
  sbox[(uint32_t )243] = (uint8_t )0x7e;
  sbox[(uint32_t )244] = (uint8_t )0xba;
  sbox[(uint32_t )245] = (uint8_t )0x77;
  sbox[(uint32_t )246] = (uint8_t )0xd6;
  sbox[(uint32_t )247] = (uint8_t )0x26;
  sbox[(uint32_t )248] = (uint8_t )0xe1;
  sbox[(uint32_t )249] = (uint8_t )0x69;
  sbox[(uint32_t )250] = (uint8_t )0x14;
  sbox[(uint32_t )251] = (uint8_t )0x63;
  sbox[(uint32_t )252] = (uint8_t )0x55;
  sbox[(uint32_t )253] = (uint8_t )0x21;
  sbox[(uint32_t )254] = (uint8_t )0x0c;
  sbox[(uint32_t )255] = (uint8_t )0x7d;
}

uint8_t Crypto_Symmetric_AES_access_aux(uint8_t *sbox, uint8_t i, uint32_t ctr, uint8_t tmp)
{
  if (ctr == (uint32_t )256)
    return tmp;
  else
  {
    uint8_t mask = FStar_UInt8_eq_mask(i, (uint8_t )ctr);
    uint8_t _0_36 = sbox[ctr];
    uint8_t _0_37 = mask & _0_36;
    uint8_t tmp0 = tmp | _0_37;
    return Crypto_Symmetric_AES_access_aux(sbox, i, ctr + (uint32_t )1, tmp0);
  }
}

uint8_t Crypto_Symmetric_AES_access(uint8_t *sbox, uint8_t i)
{
  return sbox[(uint32_t )i];
}

void Crypto_Symmetric_AES_subBytes_aux_sbox(uint8_t *state, uint8_t *sbox, uint32_t ctr)
{
  if (ctr != (uint32_t )16)
  {
    uint8_t si = state[ctr];
    uint8_t si_ = Crypto_Symmetric_AES_access(sbox, si);
    state[ctr] = si_;
    Crypto_Symmetric_AES_subBytes_aux_sbox(state, sbox, ctr + (uint32_t )1);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_AES_subBytes_sbox(uint8_t *state, uint8_t *sbox)
{
  Crypto_Symmetric_AES_subBytes_aux_sbox(state, sbox, (uint32_t )0);
  return;
}

void Crypto_Symmetric_AES_shiftRows(uint8_t *state)
{
  uint32_t i = (uint32_t )1;
  uint8_t tmp0 = state[i];
  uint8_t _0_38 = state[i + (uint32_t )4];
  state[i] = _0_38;
  uint8_t _0_39 = state[i + (uint32_t )8];
  state[i + (uint32_t )4] = _0_39;
  uint8_t _0_40 = state[i + (uint32_t )12];
  state[i + (uint32_t )8] = _0_40;
  state[i + (uint32_t )12] = tmp0;
  uint32_t i0 = (uint32_t )2;
  uint8_t tmp1 = state[i0];
  uint8_t _0_41 = state[i0 + (uint32_t )8];
  state[i0] = _0_41;
  state[i0 + (uint32_t )8] = tmp1;
  uint8_t tmp2 = state[i0 + (uint32_t )4];
  uint8_t _0_42 = state[i0 + (uint32_t )12];
  state[i0 + (uint32_t )4] = _0_42;
  state[i0 + (uint32_t )12] = tmp2;
  uint32_t i1 = (uint32_t )3;
  uint8_t tmp = state[i1];
  uint8_t _0_43 = state[i1 + (uint32_t )12];
  state[i1] = _0_43;
  uint8_t _0_44 = state[i1 + (uint32_t )8];
  state[i1 + (uint32_t )12] = _0_44;
  uint8_t _0_45 = state[i1 + (uint32_t )4];
  state[i1 + (uint32_t )8] = _0_45;
  state[i1 + (uint32_t )4] = tmp;
}

void Crypto_Symmetric_AES_mixColumns_(uint8_t *state, uint32_t c)
{
  uint8_t *s = state + (uint32_t )4 * c;
  uint8_t s0 = s[(uint32_t )0];
  uint8_t s1 = s[(uint32_t )1];
  uint8_t s2 = s[(uint32_t )2];
  uint8_t s3 = s[(uint32_t )3];
  s[(uint32_t )0] =
    Crypto_Symmetric_AES_multiply((uint8_t )0x2,
      s0)
    ^ Crypto_Symmetric_AES_multiply((uint8_t )0x3, s1) ^ s2 ^ s3;
  s[(uint32_t )1] =
    Crypto_Symmetric_AES_multiply((uint8_t )0x2,
      s1)
    ^ Crypto_Symmetric_AES_multiply((uint8_t )0x3, s2) ^ s3 ^ s0;
  s[(uint32_t )2] =
    Crypto_Symmetric_AES_multiply((uint8_t )0x2,
      s2)
    ^ Crypto_Symmetric_AES_multiply((uint8_t )0x3, s3) ^ s0 ^ s1;
  s[(uint32_t )3] =
    Crypto_Symmetric_AES_multiply((uint8_t )0x2,
      s3)
    ^ Crypto_Symmetric_AES_multiply((uint8_t )0x3, s0) ^ s1 ^ s2;
}

void Crypto_Symmetric_AES_mixColumns(uint8_t *state)
{
  Crypto_Symmetric_AES_mixColumns_(state, (uint32_t )0);
  Crypto_Symmetric_AES_mixColumns_(state, (uint32_t )1);
  Crypto_Symmetric_AES_mixColumns_(state, (uint32_t )2);
  Crypto_Symmetric_AES_mixColumns_(state, (uint32_t )3);
  return;
}

void Crypto_Symmetric_AES_addRoundKey_(uint8_t *state, uint8_t *w, uint32_t round, uint32_t c)
{
  uint8_t *target = state + (uint32_t )4 * c;
  uint8_t *subkey = w + Crypto_Symmetric_AES_blocklen * round + (uint32_t )4 * c;
  uint8_t _0_47 = target[(uint32_t )0];
  uint8_t _0_46 = subkey[(uint32_t )0];
  uint8_t _0_48 = _0_47 ^ _0_46;
  target[(uint32_t )0] = _0_48;
  uint8_t _0_50 = target[(uint32_t )1];
  uint8_t _0_49 = subkey[(uint32_t )1];
  uint8_t _0_51 = _0_50 ^ _0_49;
  target[(uint32_t )1] = _0_51;
  uint8_t _0_53 = target[(uint32_t )2];
  uint8_t _0_52 = subkey[(uint32_t )2];
  uint8_t _0_54 = _0_53 ^ _0_52;
  target[(uint32_t )2] = _0_54;
  uint8_t _0_56 = target[(uint32_t )3];
  uint8_t _0_55 = subkey[(uint32_t )3];
  uint8_t _0_57 = _0_56 ^ _0_55;
  target[(uint32_t )3] = _0_57;
}

void Crypto_Symmetric_AES_addRoundKey(uint8_t *state, uint8_t *w, uint32_t round)
{
  Crypto_Symmetric_AES_addRoundKey_(state, w, round, (uint32_t )0);
  Crypto_Symmetric_AES_addRoundKey_(state, w, round, (uint32_t )1);
  Crypto_Symmetric_AES_addRoundKey_(state, w, round, (uint32_t )2);
  Crypto_Symmetric_AES_addRoundKey_(state, w, round, (uint32_t )3);
  return;
}

void
Crypto_Symmetric_AES_cipher_loop(uint8_t *state, uint8_t *w, uint8_t *sbox, uint32_t round)
{
  if (round != (uint32_t )14)
  {
    Crypto_Symmetric_AES_subBytes_sbox(state, sbox);
    Crypto_Symmetric_AES_shiftRows(state);
    Crypto_Symmetric_AES_mixColumns(state);
    Crypto_Symmetric_AES_addRoundKey(state, w, round);
    Crypto_Symmetric_AES_cipher_loop(state, w, sbox, round + (uint32_t )1);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_AES_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox)
{
  uint8_t state[Crypto_Symmetric_AES_blocklen];
  memset(state, 0, Crypto_Symmetric_AES_blocklen * sizeof state[0]);
  memcpy(state, input, Crypto_Symmetric_AES_blocklen * sizeof input[0]);
  Crypto_Symmetric_AES_addRoundKey(state, w, (uint32_t )0);
  Crypto_Symmetric_AES_cipher_loop(state, w, sbox, (uint32_t )1);
  Crypto_Symmetric_AES_subBytes_sbox(state, sbox);
  Crypto_Symmetric_AES_shiftRows(state);
  Crypto_Symmetric_AES_addRoundKey(state, w, (uint32_t )14);
  memcpy(out, state, Crypto_Symmetric_AES_blocklen * sizeof state[0]);
}

void Crypto_Symmetric_AES_rotWord(uint8_t *word)
{
  uint8_t w0 = word[(uint32_t )0];
  uint8_t w1 = word[(uint32_t )1];
  uint8_t w2 = word[(uint32_t )2];
  uint8_t w3 = word[(uint32_t )3];
  word[(uint32_t )0] = w1;
  word[(uint32_t )1] = w2;
  word[(uint32_t )2] = w3;
  word[(uint32_t )3] = w0;
}

void Crypto_Symmetric_AES_subWord(uint8_t *word, uint8_t *sbox)
{
  uint8_t _0_58 = word[(uint32_t )0];
  uint8_t _0_59 = Crypto_Symmetric_AES_access(sbox, _0_58);
  word[(uint32_t )0] = _0_59;
  uint8_t _0_60 = word[(uint32_t )1];
  uint8_t _0_61 = Crypto_Symmetric_AES_access(sbox, _0_60);
  word[(uint32_t )1] = _0_61;
  uint8_t _0_62 = word[(uint32_t )2];
  uint8_t _0_63 = Crypto_Symmetric_AES_access(sbox, _0_62);
  word[(uint32_t )2] = _0_63;
  uint8_t _0_64 = word[(uint32_t )3];
  uint8_t _0_65 = Crypto_Symmetric_AES_access(sbox, _0_64);
  word[(uint32_t )3] = _0_65;
}

uint8_t Crypto_Symmetric_AES_rcon(uint32_t i, uint8_t tmp)
{
  if (i == (uint32_t )1)
    return tmp;
  else
    return
      Crypto_Symmetric_AES_rcon(i - (uint32_t )1,
        Crypto_Symmetric_AES_multiply((uint8_t )0x2, tmp));
}

void
Crypto_Symmetric_AES_keyExpansion_aux_0(uint8_t *w, uint8_t *temp, uint8_t *sbox, uint32_t j)
{
  memcpy(temp, w + (uint32_t )4 * j - (uint32_t )4, (uint32_t )4 * sizeof w[0]);
  if (j % (uint32_t )8 == (uint32_t )0)
  {
    Crypto_Symmetric_AES_rotWord(temp);
    Crypto_Symmetric_AES_subWord(temp, sbox);
    uint8_t t0 = temp[(uint32_t )0];
    uint8_t rc = Crypto_Symmetric_AES_rcon(j / (uint32_t )8, (uint8_t )1);
    uint8_t z = t0 ^ rc;
    temp[(uint32_t )0] = z;
  }
  else if (j % (uint32_t )8 == (uint32_t )4)
  {
    Crypto_Symmetric_AES_subWord(temp, sbox);
    return;
  }
  else
    return;
}

void
Crypto_Symmetric_AES_keyExpansion_aux_1(uint8_t *w, uint8_t *temp, uint8_t *sbox, uint32_t j)
{
  uint32_t i = (uint32_t )4 * j;
  uint8_t w0 = w[i + (uint32_t )0 - Crypto_Symmetric_AES_keylen];
  uint8_t w1 = w[i + (uint32_t )1 - Crypto_Symmetric_AES_keylen];
  uint8_t w2 = w[i + (uint32_t )2 - Crypto_Symmetric_AES_keylen];
  uint8_t w3 = w[i + (uint32_t )3 - Crypto_Symmetric_AES_keylen];
  uint8_t t0 = temp[(uint32_t )0];
  uint8_t t1 = temp[(uint32_t )1];
  uint8_t t2 = temp[(uint32_t )2];
  uint8_t t3 = temp[(uint32_t )3];
  w[i + (uint32_t )0] = t0 ^ w0;
  w[i + (uint32_t )1] = t1 ^ w1;
  w[i + (uint32_t )2] = t2 ^ w2;
  w[i + (uint32_t )3] = t3 ^ w3;
}

void
Crypto_Symmetric_AES_keyExpansion_aux(uint8_t *w, uint8_t *temp, uint8_t *sbox, uint32_t j)
{
  if (j < Crypto_Symmetric_AES_xkeylen / (uint32_t )4)
  {
    Crypto_Symmetric_AES_keyExpansion_aux_0(w, temp, sbox, j);
    Crypto_Symmetric_AES_keyExpansion_aux_1(w, temp, sbox, j);
    Crypto_Symmetric_AES_keyExpansion_aux(w, temp, sbox, j + (uint32_t )1);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_AES_keyExpansion(uint8_t *key, uint8_t *w, uint8_t *sbox)
{
  uint8_t temp[4] = { 0 };
  memcpy(w, key, Crypto_Symmetric_AES_keylen * sizeof key[0]);
  Crypto_Symmetric_AES_keyExpansion_aux(w, temp, sbox, (uint32_t )8);
}

void Crypto_Symmetric_AES_invSubBytes_aux_sbox(uint8_t *state, uint8_t *sbox, uint32_t ctr)
{
  if (ctr == (uint32_t )16)
    return;
  else
  {
    uint8_t si = state[ctr];
    uint8_t si_ = Crypto_Symmetric_AES_access(sbox, si);
    state[ctr] = si_;
    Crypto_Symmetric_AES_invSubBytes_aux_sbox(state, sbox, ctr + (uint32_t )1);
    return;
  }
}

void Crypto_Symmetric_AES_invSubBytes_sbox(uint8_t *state, uint8_t *sbox)
{
  Crypto_Symmetric_AES_invSubBytes_aux_sbox(state, sbox, (uint32_t )0);
  return;
}

void Crypto_Symmetric_AES_invShiftRows(uint8_t *state)
{
  uint32_t i = (uint32_t )3;
  uint8_t tmp0 = state[i];
  uint8_t _0_66 = state[i + (uint32_t )4];
  state[i] = _0_66;
  uint8_t _0_67 = state[i + (uint32_t )8];
  state[i + (uint32_t )4] = _0_67;
  uint8_t _0_68 = state[i + (uint32_t )12];
  state[i + (uint32_t )8] = _0_68;
  state[i + (uint32_t )12] = tmp0;
  uint32_t i0 = (uint32_t )2;
  uint8_t tmp1 = state[i0];
  uint8_t _0_69 = state[i0 + (uint32_t )8];
  state[i0] = _0_69;
  state[i0 + (uint32_t )8] = tmp1;
  uint8_t tmp2 = state[i0 + (uint32_t )4];
  uint8_t _0_70 = state[i0 + (uint32_t )12];
  state[i0 + (uint32_t )4] = _0_70;
  state[i0 + (uint32_t )12] = tmp2;
  uint32_t i1 = (uint32_t )1;
  uint8_t tmp = state[i1];
  uint8_t _0_71 = state[i1 + (uint32_t )12];
  state[i1] = _0_71;
  uint8_t _0_72 = state[i1 + (uint32_t )8];
  state[i1 + (uint32_t )12] = _0_72;
  uint8_t _0_73 = state[i1 + (uint32_t )4];
  state[i1 + (uint32_t )8] = _0_73;
  state[i1 + (uint32_t )4] = tmp;
}

void Crypto_Symmetric_AES_invMixColumns_(uint8_t *state, uint32_t c)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void Crypto_Symmetric_AES_invMixColumns(uint8_t *state)
{
  Crypto_Symmetric_AES_invMixColumns_(state, (uint32_t )0);
  Crypto_Symmetric_AES_invMixColumns_(state, (uint32_t )1);
  Crypto_Symmetric_AES_invMixColumns_(state, (uint32_t )2);
  Crypto_Symmetric_AES_invMixColumns_(state, (uint32_t )3);
  return;
}

void
Crypto_Symmetric_AES_inv_cipher_loop(uint8_t *state, uint8_t *w, uint8_t *sbox, uint32_t round)
{
  if (round != (uint32_t )0)
  {
    Crypto_Symmetric_AES_invShiftRows(state);
    Crypto_Symmetric_AES_invSubBytes_sbox(state, sbox);
    Crypto_Symmetric_AES_addRoundKey(state, w, round);
    Crypto_Symmetric_AES_invMixColumns(state);
    Crypto_Symmetric_AES_inv_cipher_loop(state, w, sbox, round - (uint32_t )1);
    return;
  }
  else
    return;
}

void Crypto_Symmetric_AES_inv_cipher(uint8_t *out, uint8_t *input, uint8_t *w, uint8_t *sbox)
{
  uint8_t state[Crypto_Symmetric_AES_blocklen];
  memset(state, 0, Crypto_Symmetric_AES_blocklen * sizeof state[0]);
  memcpy(state, input, Crypto_Symmetric_AES_blocklen * sizeof input[0]);
  Crypto_Symmetric_AES_addRoundKey(state, w, (uint32_t )14);
  Crypto_Symmetric_AES_inv_cipher_loop(state, w, sbox, (uint32_t )13);
  Crypto_Symmetric_AES_invShiftRows(state);
  Crypto_Symmetric_AES_invSubBytes_sbox(state, sbox);
  Crypto_Symmetric_AES_addRoundKey(state, w, (uint32_t )0);
  memcpy(out, state, Crypto_Symmetric_AES_blocklen * sizeof state[0]);
}

