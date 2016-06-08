module Crypto.AES

open FStar.Ghost
open FStar.Heap
open SInt
open SInt.UInt8
open SBytes
open SBuffer

#set-options "--lax"

// Parameters for AES-256 
let nk = 8
let nb = 4
let nr = 14

val xtime: b:uint8 -> Tot uint8 
let xtime b = 
  (b ^<< 1) ^^ (((b ^>> 7) ^& one) ^*% of_string "0x1b")

val multiply: a:uint8 -> b:uint8 -> Tot uint8
let multiply a b =
  ((a ^*% (b ^& one))
  ^^ (xtime a ^*% ((b ^>> 1) ^& one))
  ^^ (xtime (xtime a) ^*% ((b ^>> 2) ^& one))
  ^^ (xtime (xtime (xtime a)) ^*% ((b ^>> 3) ^& one))
  ^^ (xtime (xtime (xtime (xtime a))) ^*% ((b ^>> 4) ^& one))
  ^^ (xtime (xtime (xtime (xtime (xtime a)))) ^*% ((b ^>> 5) ^& one))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime a))))) ^*% ((b ^>> 6) ^& one))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime (xtime a)))))) ^*% ((b ^>> 7) ^& one)))

// Code taken from http://www.literatecode.com/get/aes256.c
// and made constant time
val alog_aux: x:uint8 -> y:uint8 -> mask:uint8 -> ctr:nat{ctr <= 256} -> Tot uint8 (decreases (256 - ctr))
let rec alog_aux x y mask ctr =
  match ctr with
  | 256 -> y
  | _ -> 
    let mask = lognot(gte (of_int ctr) x) in
    let y = y ^^ (xtime(y) ^& mask) in
    alog_aux x y mask (ctr+1)

val alog: x:uint8 -> Tot uint8
let alog x =
  let y = one in
  let mask = zero in
  alog_aux x y mask 0

val log_aux: x:uint8 -> y:uint8 -> j:uint8 -> mask:uint8 -> ctr:nat{ctr <= 256} -> Tot uint8 (decreases (256 - ctr))
let rec log_aux x y j mask ctr =
  match ctr with
  | 256 -> j
  | _ ->
    let j = j ^+% (one ^& mask) in
    let y = y ^^ xtime y in
    let mask = mask ^& (lognot (eq x y)) in
    log_aux x y j mask (ctr+1)

val log: uint8 -> Tot uint8
let log x =
  let y = one in
  let j = zero in
  let mask = lognot(eq x zero) in
  log_aux x y j mask 0

val inverse: uint8 -> Tot uint8 
let inverse x = (lognot (eq x zero)) ^& (alog (of_int 255 ^-% log x))

val mk_sbox: sbox:uint8s{length sbox = 64} -> St unit
let mk_sbox sbox = 
  upd sbox 0   (SInt.UInt8.of_int 0x63); upd sbox 1   (SInt.UInt8.of_int 0x7c); upd sbox 2   (SInt.UInt8.of_int 0x77); upd sbox 3   (SInt.UInt8.of_int 0x7b); 
  upd sbox 4   (SInt.UInt8.of_int 0xf2); upd sbox 5   (SInt.UInt8.of_int 0x6b); upd sbox 6   (SInt.UInt8.of_int 0x6f); upd sbox 7   (SInt.UInt8.of_int 0xc5); 
  upd sbox 8   (SInt.UInt8.of_int 0x30); upd sbox 9   (SInt.UInt8.of_int 0x01); upd sbox 10  (SInt.UInt8.of_int 0x67); upd sbox 11  (SInt.UInt8.of_int 0x2b); 
  upd sbox 12  (SInt.UInt8.of_int 0xfe); upd sbox 13  (SInt.UInt8.of_int 0xd7); upd sbox 14  (SInt.UInt8.of_int 0xab); upd sbox 15  (SInt.UInt8.of_int 0x76); 
  upd sbox 16  (SInt.UInt8.of_int 0xca); upd sbox 17  (SInt.UInt8.of_int 0x82); upd sbox 18  (SInt.UInt8.of_int 0xc9); upd sbox 19  (SInt.UInt8.of_int 0x7d); 
  upd sbox 20  (SInt.UInt8.of_int 0xfa); upd sbox 21  (SInt.UInt8.of_int 0x59); upd sbox 22  (SInt.UInt8.of_int 0x47); upd sbox 23  (SInt.UInt8.of_int 0xf0); 
  upd sbox 24  (SInt.UInt8.of_int 0xad); upd sbox 25  (SInt.UInt8.of_int 0xd4); upd sbox 26  (SInt.UInt8.of_int 0xa2); upd sbox 27  (SInt.UInt8.of_int 0xaf); 
  upd sbox 28  (SInt.UInt8.of_int 0x9c); upd sbox 29  (SInt.UInt8.of_int 0xa4); upd sbox 30  (SInt.UInt8.of_int 0x72); upd sbox 31  (SInt.UInt8.of_int 0xc0); 
  upd sbox 32  (SInt.UInt8.of_int 0xb7); upd sbox 33  (SInt.UInt8.of_int 0xfd); upd sbox 34  (SInt.UInt8.of_int 0x93); upd sbox 35  (SInt.UInt8.of_int 0x26); 
  upd sbox 36  (SInt.UInt8.of_int 0x36); upd sbox 37  (SInt.UInt8.of_int 0x3f); upd sbox 38  (SInt.UInt8.of_int 0xf7); upd sbox 39  (SInt.UInt8.of_int 0xcc); 
  upd sbox 40  (SInt.UInt8.of_int 0x34); upd sbox 41  (SInt.UInt8.of_int 0xa5); upd sbox 42  (SInt.UInt8.of_int 0xe5); upd sbox 43  (SInt.UInt8.of_int 0xf1); 
  upd sbox 44  (SInt.UInt8.of_int 0x71); upd sbox 45  (SInt.UInt8.of_int 0xd8); upd sbox 46  (SInt.UInt8.of_int 0x31); upd sbox 47  (SInt.UInt8.of_int 0x15); 
  upd sbox 48  (SInt.UInt8.of_int 0x04); upd sbox 49  (SInt.UInt8.of_int 0xc7); upd sbox 50  (SInt.UInt8.of_int 0x23); upd sbox 51  (SInt.UInt8.of_int 0xc3); 
  upd sbox 52  (SInt.UInt8.of_int 0x18); upd sbox 53  (SInt.UInt8.of_int 0x96); upd sbox 54  (SInt.UInt8.of_int 0x05); upd sbox 55  (SInt.UInt8.of_int 0x9a); 
  upd sbox 56  (SInt.UInt8.of_int 0x07); upd sbox 57  (SInt.UInt8.of_int 0x12); upd sbox 58  (SInt.UInt8.of_int 0x80); upd sbox 59  (SInt.UInt8.of_int 0xe2); 
  upd sbox 60  (SInt.UInt8.of_int 0xeb); upd sbox 61  (SInt.UInt8.of_int 0x27); upd sbox 62  (SInt.UInt8.of_int 0xb2); upd sbox 63  (SInt.UInt8.of_int 0x75); 
  upd sbox 64  (SInt.UInt8.of_int 0x09); upd sbox 65  (SInt.UInt8.of_int 0x83); upd sbox 66  (SInt.UInt8.of_int 0x2c); upd sbox 67  (SInt.UInt8.of_int 0x1a); 
  upd sbox 68  (SInt.UInt8.of_int 0x1b); upd sbox 69  (SInt.UInt8.of_int 0x6e); upd sbox 70  (SInt.UInt8.of_int 0x5a); upd sbox 71  (SInt.UInt8.of_int 0xa0); 
  upd sbox 72  (SInt.UInt8.of_int 0x52); upd sbox 73  (SInt.UInt8.of_int 0x3b); upd sbox 74  (SInt.UInt8.of_int 0xd6); upd sbox 75  (SInt.UInt8.of_int 0xb3); 
  upd sbox 76  (SInt.UInt8.of_int 0x29); upd sbox 77  (SInt.UInt8.of_int 0xe3); upd sbox 78  (SInt.UInt8.of_int 0x2f); upd sbox 79  (SInt.UInt8.of_int 0x84); 
  upd sbox 80  (SInt.UInt8.of_int 0x53); upd sbox 81  (SInt.UInt8.of_int 0xd1); upd sbox 82  (SInt.UInt8.of_int 0x00); upd sbox 83  (SInt.UInt8.of_int 0xed); 
  upd sbox 84  (SInt.UInt8.of_int 0x20); upd sbox 85  (SInt.UInt8.of_int 0xfc); upd sbox 86  (SInt.UInt8.of_int 0xb1); upd sbox 87  (SInt.UInt8.of_int 0x5b); 
  upd sbox 88  (SInt.UInt8.of_int 0x6a); upd sbox 89  (SInt.UInt8.of_int 0xcb); upd sbox 90  (SInt.UInt8.of_int 0xbe); upd sbox 91  (SInt.UInt8.of_int 0x39); 
  upd sbox 92  (SInt.UInt8.of_int 0x4a); upd sbox 93  (SInt.UInt8.of_int 0x4c); upd sbox 94  (SInt.UInt8.of_int 0x58); upd sbox 95  (SInt.UInt8.of_int 0xcf); 
  upd sbox 96  (SInt.UInt8.of_int 0xd0); upd sbox 97  (SInt.UInt8.of_int 0xef); upd sbox 98  (SInt.UInt8.of_int 0xaa); upd sbox 99  (SInt.UInt8.of_int 0xfb); 
  upd sbox 100 (SInt.UInt8.of_int 0x43); upd sbox 101 (SInt.UInt8.of_int 0x4d); upd sbox 102 (SInt.UInt8.of_int 0x33); upd sbox 103 (SInt.UInt8.of_int 0x85); 
  upd sbox 104 (SInt.UInt8.of_int 0x45); upd sbox 105 (SInt.UInt8.of_int 0xf9); upd sbox 106 (SInt.UInt8.of_int 0x02); upd sbox 107 (SInt.UInt8.of_int 0x7f); 
  upd sbox 108 (SInt.UInt8.of_int 0x50); upd sbox 109 (SInt.UInt8.of_int 0x3c); upd sbox 110 (SInt.UInt8.of_int 0x9f); upd sbox 111 (SInt.UInt8.of_int 0xa8); 
  upd sbox 112 (SInt.UInt8.of_int 0x51); upd sbox 113 (SInt.UInt8.of_int 0xa3); upd sbox 114 (SInt.UInt8.of_int 0x40); upd sbox 115 (SInt.UInt8.of_int 0x8f); 
  upd sbox 116 (SInt.UInt8.of_int 0x92); upd sbox 117 (SInt.UInt8.of_int 0x9d); upd sbox 118 (SInt.UInt8.of_int 0x38); upd sbox 119 (SInt.UInt8.of_int 0xf5); 
  upd sbox 120 (SInt.UInt8.of_int 0xbc); upd sbox 121 (SInt.UInt8.of_int 0xb6); upd sbox 122 (SInt.UInt8.of_int 0xda); upd sbox 123 (SInt.UInt8.of_int 0x21); 
  upd sbox 124 (SInt.UInt8.of_int 0x10); upd sbox 125 (SInt.UInt8.of_int 0xff); upd sbox 126 (SInt.UInt8.of_int 0xf3); upd sbox 127 (SInt.UInt8.of_int 0xd2); 
  upd sbox 128 (SInt.UInt8.of_int 0xcd); upd sbox 129 (SInt.UInt8.of_int 0x0c); upd sbox 130 (SInt.UInt8.of_int 0x13); upd sbox 131 (SInt.UInt8.of_int 0xec); 
  upd sbox 132 (SInt.UInt8.of_int 0x5f); upd sbox 133 (SInt.UInt8.of_int 0x97); upd sbox 134 (SInt.UInt8.of_int 0x44); upd sbox 135 (SInt.UInt8.of_int 0x17); 
  upd sbox 136 (SInt.UInt8.of_int 0xc4); upd sbox 137 (SInt.UInt8.of_int 0xa7); upd sbox 138 (SInt.UInt8.of_int 0x7e); upd sbox 139 (SInt.UInt8.of_int 0x3d); 
  upd sbox 140 (SInt.UInt8.of_int 0x64); upd sbox 141 (SInt.UInt8.of_int 0x5d); upd sbox 142 (SInt.UInt8.of_int 0x19); upd sbox 143 (SInt.UInt8.of_int 0x73); 
  upd sbox 144 (SInt.UInt8.of_int 0x60); upd sbox 145 (SInt.UInt8.of_int 0x81); upd sbox 146 (SInt.UInt8.of_int 0x4f); upd sbox 147 (SInt.UInt8.of_int 0xdc); 
  upd sbox 148 (SInt.UInt8.of_int 0x22); upd sbox 149 (SInt.UInt8.of_int 0x2a); upd sbox 150 (SInt.UInt8.of_int 0x90); upd sbox 151 (SInt.UInt8.of_int 0x88); 
  upd sbox 152 (SInt.UInt8.of_int 0x46); upd sbox 153 (SInt.UInt8.of_int 0xee); upd sbox 154 (SInt.UInt8.of_int 0xb8); upd sbox 155 (SInt.UInt8.of_int 0x14); 
  upd sbox 156 (SInt.UInt8.of_int 0xde); upd sbox 157 (SInt.UInt8.of_int 0x5e); upd sbox 158 (SInt.UInt8.of_int 0x0b); upd sbox 159 (SInt.UInt8.of_int 0xdb); 
  upd sbox 160 (SInt.UInt8.of_int 0xe0); upd sbox 161 (SInt.UInt8.of_int 0x32); upd sbox 162 (SInt.UInt8.of_int 0x3a); upd sbox 163 (SInt.UInt8.of_int 0x0a); 
  upd sbox 164 (SInt.UInt8.of_int 0x49); upd sbox 165 (SInt.UInt8.of_int 0x06); upd sbox 166 (SInt.UInt8.of_int 0x24); upd sbox 167 (SInt.UInt8.of_int 0x5c); 
  upd sbox 168 (SInt.UInt8.of_int 0xc2); upd sbox 169 (SInt.UInt8.of_int 0xd3); upd sbox 170 (SInt.UInt8.of_int 0xac); upd sbox 171 (SInt.UInt8.of_int 0x62); 
  upd sbox 172 (SInt.UInt8.of_int 0x91); upd sbox 173 (SInt.UInt8.of_int 0x95); upd sbox 174 (SInt.UInt8.of_int 0xe4); upd sbox 175 (SInt.UInt8.of_int 0x79); 
  upd sbox 176 (SInt.UInt8.of_int 0xe7); upd sbox 177 (SInt.UInt8.of_int 0xc8); upd sbox 178 (SInt.UInt8.of_int 0x37); upd sbox 179 (SInt.UInt8.of_int 0x6d); 
  upd sbox 180 (SInt.UInt8.of_int 0x8d); upd sbox 181 (SInt.UInt8.of_int 0xd5); upd sbox 182 (SInt.UInt8.of_int 0x4e); upd sbox 183 (SInt.UInt8.of_int 0xa9); 
  upd sbox 184 (SInt.UInt8.of_int 0x6c); upd sbox 185 (SInt.UInt8.of_int 0x56); upd sbox 186 (SInt.UInt8.of_int 0xf4); upd sbox 187 (SInt.UInt8.of_int 0xea); 
  upd sbox 188 (SInt.UInt8.of_int 0x65); upd sbox 189 (SInt.UInt8.of_int 0x7a); upd sbox 190 (SInt.UInt8.of_int 0xae); upd sbox 191 (SInt.UInt8.of_int 0x08); 
  upd sbox 192 (SInt.UInt8.of_int 0xba); upd sbox 193 (SInt.UInt8.of_int 0x78); upd sbox 194 (SInt.UInt8.of_int 0x25); upd sbox 195 (SInt.UInt8.of_int 0x2e); 
  upd sbox 196 (SInt.UInt8.of_int 0x1c); upd sbox 197 (SInt.UInt8.of_int 0xa6); upd sbox 198 (SInt.UInt8.of_int 0xb4); upd sbox 199 (SInt.UInt8.of_int 0xc6); 
  upd sbox 200 (SInt.UInt8.of_int 0xe8); upd sbox 201 (SInt.UInt8.of_int 0xdd); upd sbox 202 (SInt.UInt8.of_int 0x74); upd sbox 203 (SInt.UInt8.of_int 0x1f); 
  upd sbox 204 (SInt.UInt8.of_int 0x4b); upd sbox 205 (SInt.UInt8.of_int 0xbd); upd sbox 206 (SInt.UInt8.of_int 0x8b); upd sbox 207 (SInt.UInt8.of_int 0x8a); 
  upd sbox 208 (SInt.UInt8.of_int 0x70); upd sbox 209 (SInt.UInt8.of_int 0x3e); upd sbox 210 (SInt.UInt8.of_int 0xb5); upd sbox 211 (SInt.UInt8.of_int 0x66); 
  upd sbox 212 (SInt.UInt8.of_int 0x48); upd sbox 213 (SInt.UInt8.of_int 0x03); upd sbox 214 (SInt.UInt8.of_int 0xf6); upd sbox 215 (SInt.UInt8.of_int 0x0e); 
  upd sbox 216 (SInt.UInt8.of_int 0x61); upd sbox 217 (SInt.UInt8.of_int 0x35); upd sbox 218 (SInt.UInt8.of_int 0x57); upd sbox 219 (SInt.UInt8.of_int 0xb9); 
  upd sbox 220 (SInt.UInt8.of_int 0x86); upd sbox 221 (SInt.UInt8.of_int 0xc1); upd sbox 222 (SInt.UInt8.of_int 0x1d); upd sbox 223 (SInt.UInt8.of_int 0x9e); 
  upd sbox 224 (SInt.UInt8.of_int 0xe1); upd sbox 225 (SInt.UInt8.of_int 0xf8); upd sbox 226 (SInt.UInt8.of_int 0x98); upd sbox 227 (SInt.UInt8.of_int 0x11); 
  upd sbox 228 (SInt.UInt8.of_int 0x69); upd sbox 229 (SInt.UInt8.of_int 0xd9); upd sbox 230 (SInt.UInt8.of_int 0x8e); upd sbox 231 (SInt.UInt8.of_int 0x94); 
  upd sbox 232 (SInt.UInt8.of_int 0x9b); upd sbox 233 (SInt.UInt8.of_int 0x1e); upd sbox 234 (SInt.UInt8.of_int 0x87); upd sbox 235 (SInt.UInt8.of_int 0xe9); 
  upd sbox 236 (SInt.UInt8.of_int 0xce); upd sbox 237 (SInt.UInt8.of_int 0x55); upd sbox 238 (SInt.UInt8.of_int 0x28); upd sbox 239 (SInt.UInt8.of_int 0xdf); 
  upd sbox 240 (SInt.UInt8.of_int 0x8c); upd sbox 241 (SInt.UInt8.of_int 0xa1); upd sbox 242 (SInt.UInt8.of_int 0x89); upd sbox 243 (SInt.UInt8.of_int 0x0d); 
  upd sbox 244 (SInt.UInt8.of_int 0xbf); upd sbox 245 (SInt.UInt8.of_int 0xe6); upd sbox 246 (SInt.UInt8.of_int 0x42); upd sbox 247 (SInt.UInt8.of_int 0x68); 
  upd sbox 248 (SInt.UInt8.of_int 0x41); upd sbox 249 (SInt.UInt8.of_int 0x99); upd sbox 250 (SInt.UInt8.of_int 0x2d); upd sbox 251 (SInt.UInt8.of_int 0x0f); 
  upd sbox 252 (SInt.UInt8.of_int 0xb0); upd sbox 253 (SInt.UInt8.of_int 0x54); upd sbox 254 (SInt.UInt8.of_int 0xbb); upd sbox 255 (SInt.UInt8.of_int 0x16)

val mk_inv_sbox: sbox:uint8s{length sbox = 64} -> St unit
let mk_inv_sbox sbox = 
  upd sbox 0   (SInt.UInt8.of_int 0x52); upd sbox 1   (SInt.UInt8.of_int 0x09); upd sbox 2   (SInt.UInt8.of_int 0x6a); upd sbox 3   (SInt.UInt8.of_int 0xd5); 
  upd sbox 4   (SInt.UInt8.of_int 0x30); upd sbox 5   (SInt.UInt8.of_int 0x36); upd sbox 6   (SInt.UInt8.of_int 0xa5); upd sbox 7   (SInt.UInt8.of_int 0x38); 
  upd sbox 8   (SInt.UInt8.of_int 0xbf); upd sbox 9   (SInt.UInt8.of_int 0x40); upd sbox 10  (SInt.UInt8.of_int 0xa3); upd sbox 11  (SInt.UInt8.of_int 0x9e); 
  upd sbox 12  (SInt.UInt8.of_int 0x81); upd sbox 13  (SInt.UInt8.of_int 0xf3); upd sbox 14  (SInt.UInt8.of_int 0xd7); upd sbox 15  (SInt.UInt8.of_int 0xfb); 
  upd sbox 16  (SInt.UInt8.of_int 0x7c); upd sbox 17  (SInt.UInt8.of_int 0xe3); upd sbox 18  (SInt.UInt8.of_int 0x39); upd sbox 19  (SInt.UInt8.of_int 0x82); 
  upd sbox 20  (SInt.UInt8.of_int 0x9b); upd sbox 21  (SInt.UInt8.of_int 0x2f); upd sbox 22  (SInt.UInt8.of_int 0xff); upd sbox 23  (SInt.UInt8.of_int 0x87); 
  upd sbox 24  (SInt.UInt8.of_int 0x34); upd sbox 25  (SInt.UInt8.of_int 0x8e); upd sbox 26  (SInt.UInt8.of_int 0x43); upd sbox 27  (SInt.UInt8.of_int 0x44); 
  upd sbox 28  (SInt.UInt8.of_int 0xc4); upd sbox 29  (SInt.UInt8.of_int 0xde); upd sbox 30  (SInt.UInt8.of_int 0xe9); upd sbox 31  (SInt.UInt8.of_int 0xcb); 
  upd sbox 32  (SInt.UInt8.of_int 0x54); upd sbox 33  (SInt.UInt8.of_int 0x7b); upd sbox 34  (SInt.UInt8.of_int 0x94); upd sbox 35  (SInt.UInt8.of_int 0x32); 
  upd sbox 36  (SInt.UInt8.of_int 0xa6); upd sbox 37  (SInt.UInt8.of_int 0xc2); upd sbox 38  (SInt.UInt8.of_int 0x23); upd sbox 39  (SInt.UInt8.of_int 0x3d); 
  upd sbox 40  (SInt.UInt8.of_int 0xee); upd sbox 41  (SInt.UInt8.of_int 0x4c); upd sbox 42  (SInt.UInt8.of_int 0x95); upd sbox 43  (SInt.UInt8.of_int 0x0b); 
  upd sbox 44  (SInt.UInt8.of_int 0x42); upd sbox 45  (SInt.UInt8.of_int 0xfa); upd sbox 46  (SInt.UInt8.of_int 0xc3); upd sbox 47  (SInt.UInt8.of_int 0x4e); 
  upd sbox 48  (SInt.UInt8.of_int 0x08); upd sbox 49  (SInt.UInt8.of_int 0x2e); upd sbox 50  (SInt.UInt8.of_int 0xa1); upd sbox 51  (SInt.UInt8.of_int 0x66); 
  upd sbox 52  (SInt.UInt8.of_int 0x28); upd sbox 53  (SInt.UInt8.of_int 0xd9); upd sbox 54  (SInt.UInt8.of_int 0x24); upd sbox 55  (SInt.UInt8.of_int 0xb2); 
  upd sbox 56  (SInt.UInt8.of_int 0x76); upd sbox 57  (SInt.UInt8.of_int 0x5b); upd sbox 58  (SInt.UInt8.of_int 0xa2); upd sbox 59  (SInt.UInt8.of_int 0x49); 
  upd sbox 60  (SInt.UInt8.of_int 0x6d); upd sbox 61  (SInt.UInt8.of_int 0x8b); upd sbox 62  (SInt.UInt8.of_int 0xd1); upd sbox 63  (SInt.UInt8.of_int 0x25); 
  upd sbox 64  (SInt.UInt8.of_int 0x72); upd sbox 65  (SInt.UInt8.of_int 0xf8); upd sbox 66  (SInt.UInt8.of_int 0xf6); upd sbox 67  (SInt.UInt8.of_int 0x64); 
  upd sbox 68  (SInt.UInt8.of_int 0x86); upd sbox 69  (SInt.UInt8.of_int 0x68); upd sbox 70  (SInt.UInt8.of_int 0x98); upd sbox 71  (SInt.UInt8.of_int 0x16); 
  upd sbox 72  (SInt.UInt8.of_int 0xd4); upd sbox 73  (SInt.UInt8.of_int 0xa4); upd sbox 74  (SInt.UInt8.of_int 0x5c); upd sbox 75  (SInt.UInt8.of_int 0xcc); 
  upd sbox 76  (SInt.UInt8.of_int 0x5d); upd sbox 77  (SInt.UInt8.of_int 0x65); upd sbox 78  (SInt.UInt8.of_int 0xb6); upd sbox 79  (SInt.UInt8.of_int 0x92); 
  upd sbox 80  (SInt.UInt8.of_int 0x6c); upd sbox 81  (SInt.UInt8.of_int 0x70); upd sbox 82  (SInt.UInt8.of_int 0x48); upd sbox 83  (SInt.UInt8.of_int 0x50); 
  upd sbox 84  (SInt.UInt8.of_int 0xfd); upd sbox 85  (SInt.UInt8.of_int 0xed); upd sbox 86  (SInt.UInt8.of_int 0xb9); upd sbox 87  (SInt.UInt8.of_int 0xda); 
  upd sbox 88  (SInt.UInt8.of_int 0x5e); upd sbox 89  (SInt.UInt8.of_int 0x15); upd sbox 90  (SInt.UInt8.of_int 0x46); upd sbox 91  (SInt.UInt8.of_int 0x57); 
  upd sbox 92  (SInt.UInt8.of_int 0xa7); upd sbox 93  (SInt.UInt8.of_int 0x8d); upd sbox 94  (SInt.UInt8.of_int 0x9d); upd sbox 95  (SInt.UInt8.of_int 0x84); 
  upd sbox 96  (SInt.UInt8.of_int 0x90); upd sbox 97  (SInt.UInt8.of_int 0xd8); upd sbox 98  (SInt.UInt8.of_int 0xab); upd sbox 99  (SInt.UInt8.of_int 0x00); 
  upd sbox 100 (SInt.UInt8.of_int 0x8c); upd sbox 101 (SInt.UInt8.of_int 0xbc); upd sbox 102 (SInt.UInt8.of_int 0xd3); upd sbox 103 (SInt.UInt8.of_int 0x0a); 
  upd sbox 104 (SInt.UInt8.of_int 0xf7); upd sbox 105 (SInt.UInt8.of_int 0xe4); upd sbox 106 (SInt.UInt8.of_int 0x58); upd sbox 107 (SInt.UInt8.of_int 0x05); 
  upd sbox 108 (SInt.UInt8.of_int 0xb8); upd sbox 109 (SInt.UInt8.of_int 0xb3); upd sbox 110 (SInt.UInt8.of_int 0x45); upd sbox 111 (SInt.UInt8.of_int 0x06); 
  upd sbox 112 (SInt.UInt8.of_int 0xd0); upd sbox 113 (SInt.UInt8.of_int 0x2c); upd sbox 114 (SInt.UInt8.of_int 0x1e); upd sbox 115 (SInt.UInt8.of_int 0x8f); 
  upd sbox 116 (SInt.UInt8.of_int 0xca); upd sbox 117 (SInt.UInt8.of_int 0x3f); upd sbox 118 (SInt.UInt8.of_int 0x0f); upd sbox 119 (SInt.UInt8.of_int 0x02); 
  upd sbox 120 (SInt.UInt8.of_int 0xc1); upd sbox 121 (SInt.UInt8.of_int 0xaf); upd sbox 122 (SInt.UInt8.of_int 0xbd); upd sbox 123 (SInt.UInt8.of_int 0x03); 
  upd sbox 124 (SInt.UInt8.of_int 0x01); upd sbox 125 (SInt.UInt8.of_int 0x13); upd sbox 126 (SInt.UInt8.of_int 0x8a); upd sbox 127 (SInt.UInt8.of_int 0x6b); 
  upd sbox 128 (SInt.UInt8.of_int 0x3a); upd sbox 129 (SInt.UInt8.of_int 0x91); upd sbox 130 (SInt.UInt8.of_int 0x11); upd sbox 131 (SInt.UInt8.of_int 0x41); 
  upd sbox 132 (SInt.UInt8.of_int 0x4f); upd sbox 133 (SInt.UInt8.of_int 0x67); upd sbox 134 (SInt.UInt8.of_int 0xdc); upd sbox 135 (SInt.UInt8.of_int 0xea); 
  upd sbox 136 (SInt.UInt8.of_int 0x97); upd sbox 137 (SInt.UInt8.of_int 0xf2); upd sbox 138 (SInt.UInt8.of_int 0xcf); upd sbox 139 (SInt.UInt8.of_int 0xce); 
  upd sbox 140 (SInt.UInt8.of_int 0xf0); upd sbox 141 (SInt.UInt8.of_int 0xb4); upd sbox 142 (SInt.UInt8.of_int 0xe6); upd sbox 143 (SInt.UInt8.of_int 0x73); 
  upd sbox 144 (SInt.UInt8.of_int 0x96); upd sbox 145 (SInt.UInt8.of_int 0xac); upd sbox 146 (SInt.UInt8.of_int 0x74); upd sbox 147 (SInt.UInt8.of_int 0x22); 
  upd sbox 148 (SInt.UInt8.of_int 0xe7); upd sbox 149 (SInt.UInt8.of_int 0xad); upd sbox 150 (SInt.UInt8.of_int 0x35); upd sbox 151 (SInt.UInt8.of_int 0x85); 
  upd sbox 152 (SInt.UInt8.of_int 0xe2); upd sbox 153 (SInt.UInt8.of_int 0xf9); upd sbox 154 (SInt.UInt8.of_int 0x37); upd sbox 155 (SInt.UInt8.of_int 0xe8); 
  upd sbox 156 (SInt.UInt8.of_int 0x1c); upd sbox 157 (SInt.UInt8.of_int 0x75); upd sbox 158 (SInt.UInt8.of_int 0xdf); upd sbox 159 (SInt.UInt8.of_int 0x6e); 
  upd sbox 160 (SInt.UInt8.of_int 0x47); upd sbox 161 (SInt.UInt8.of_int 0xf1); upd sbox 162 (SInt.UInt8.of_int 0x1a); upd sbox 163 (SInt.UInt8.of_int 0x71); 
  upd sbox 164 (SInt.UInt8.of_int 0x1d); upd sbox 165 (SInt.UInt8.of_int 0x29); upd sbox 166 (SInt.UInt8.of_int 0xc5); upd sbox 167 (SInt.UInt8.of_int 0x89); 
  upd sbox 168 (SInt.UInt8.of_int 0x6f); upd sbox 169 (SInt.UInt8.of_int 0xb7); upd sbox 170 (SInt.UInt8.of_int 0x62); upd sbox 171 (SInt.UInt8.of_int 0x0e); 
  upd sbox 172 (SInt.UInt8.of_int 0xaa); upd sbox 173 (SInt.UInt8.of_int 0x18); upd sbox 174 (SInt.UInt8.of_int 0xbe); upd sbox 175 (SInt.UInt8.of_int 0x1b); 
  upd sbox 176 (SInt.UInt8.of_int 0xfc); upd sbox 177 (SInt.UInt8.of_int 0x56); upd sbox 178 (SInt.UInt8.of_int 0x3e); upd sbox 179 (SInt.UInt8.of_int 0x4b); 
  upd sbox 180 (SInt.UInt8.of_int 0xc6); upd sbox 181 (SInt.UInt8.of_int 0xd2); upd sbox 182 (SInt.UInt8.of_int 0x79); upd sbox 183 (SInt.UInt8.of_int 0x20); 
  upd sbox 184 (SInt.UInt8.of_int 0x9a); upd sbox 185 (SInt.UInt8.of_int 0xdb); upd sbox 186 (SInt.UInt8.of_int 0xc0); upd sbox 187 (SInt.UInt8.of_int 0xfe); 
  upd sbox 188 (SInt.UInt8.of_int 0x78); upd sbox 189 (SInt.UInt8.of_int 0xcd); upd sbox 190 (SInt.UInt8.of_int 0x5a); upd sbox 191 (SInt.UInt8.of_int 0xf4); 
  upd sbox 192 (SInt.UInt8.of_int 0x1f); upd sbox 193 (SInt.UInt8.of_int 0xdd); upd sbox 194 (SInt.UInt8.of_int 0xa8); upd sbox 195 (SInt.UInt8.of_int 0x33); 
  upd sbox 196 (SInt.UInt8.of_int 0x88); upd sbox 197 (SInt.UInt8.of_int 0x07); upd sbox 198 (SInt.UInt8.of_int 0xc7); upd sbox 199 (SInt.UInt8.of_int 0x31); 
  upd sbox 200 (SInt.UInt8.of_int 0xb1); upd sbox 201 (SInt.UInt8.of_int 0x12); upd sbox 202 (SInt.UInt8.of_int 0x10); upd sbox 203 (SInt.UInt8.of_int 0x59); 
  upd sbox 204 (SInt.UInt8.of_int 0x27); upd sbox 205 (SInt.UInt8.of_int 0x80); upd sbox 206 (SInt.UInt8.of_int 0xec); upd sbox 207 (SInt.UInt8.of_int 0x5f); 
  upd sbox 208 (SInt.UInt8.of_int 0x60); upd sbox 209 (SInt.UInt8.of_int 0x51); upd sbox 210 (SInt.UInt8.of_int 0x7f); upd sbox 211 (SInt.UInt8.of_int 0xa9); 
  upd sbox 212 (SInt.UInt8.of_int 0x19); upd sbox 213 (SInt.UInt8.of_int 0xb5); upd sbox 214 (SInt.UInt8.of_int 0x4a); upd sbox 215 (SInt.UInt8.of_int 0x0d); 
  upd sbox 216 (SInt.UInt8.of_int 0x2d); upd sbox 217 (SInt.UInt8.of_int 0xe5); upd sbox 218 (SInt.UInt8.of_int 0x7a); upd sbox 219 (SInt.UInt8.of_int 0x9f); 
  upd sbox 220 (SInt.UInt8.of_int 0x93); upd sbox 221 (SInt.UInt8.of_int 0xc9); upd sbox 222 (SInt.UInt8.of_int 0x9c); upd sbox 223 (SInt.UInt8.of_int 0xef); 
  upd sbox 224 (SInt.UInt8.of_int 0xa0); upd sbox 225 (SInt.UInt8.of_int 0xe0); upd sbox 226 (SInt.UInt8.of_int 0x3b); upd sbox 227 (SInt.UInt8.of_int 0x4d); 
  upd sbox 228 (SInt.UInt8.of_int 0xae); upd sbox 229 (SInt.UInt8.of_int 0x2a); upd sbox 230 (SInt.UInt8.of_int 0xf5); upd sbox 231 (SInt.UInt8.of_int 0xb0); 
  upd sbox 232 (SInt.UInt8.of_int 0xc8); upd sbox 233 (SInt.UInt8.of_int 0xeb); upd sbox 234 (SInt.UInt8.of_int 0xbb); upd sbox 235 (SInt.UInt8.of_int 0x3c); 
  upd sbox 236 (SInt.UInt8.of_int 0x83); upd sbox 237 (SInt.UInt8.of_int 0x53); upd sbox 238 (SInt.UInt8.of_int 0x99); upd sbox 239 (SInt.UInt8.of_int 0x61); 
  upd sbox 240 (SInt.UInt8.of_int 0x17); upd sbox 241 (SInt.UInt8.of_int 0x2b); upd sbox 242 (SInt.UInt8.of_int 0x04); upd sbox 243 (SInt.UInt8.of_int 0x7e); 
  upd sbox 244 (SInt.UInt8.of_int 0xba); upd sbox 245 (SInt.UInt8.of_int 0x77); upd sbox 246 (SInt.UInt8.of_int 0xd6); upd sbox 247 (SInt.UInt8.of_int 0x26); 
  upd sbox 248 (SInt.UInt8.of_int 0xe1); upd sbox 249 (SInt.UInt8.of_int 0x69); upd sbox 250 (SInt.UInt8.of_int 0x14); upd sbox 251 (SInt.UInt8.of_int 0x63); 
  upd sbox 252 (SInt.UInt8.of_int 0x55); upd sbox 253 (SInt.UInt8.of_int 0x21); upd sbox 254 (SInt.UInt8.of_int 0x0c); upd sbox 255 (SInt.UInt8.of_int 0x7d)

val access: sbox:uint8s -> idx:uint8 -> St uint8
let access sbox i =
  let rec access_aux: uint8s -> uint8 -> nat -> uint8 -> St uint8 = fun sbox i ctr tmp -> 
    if ctr = 256 then tmp 
    else let mask = SInt.UInt8.eq i (of_int ctr) in
	 let tmp = tmp ^| (mask ^& index sbox ctr) in
	 access_aux sbox i (ctr+1) tmp in
  access_aux sbox i 0 SInt.UInt8.zero

(* val subBytes_: uint8 -> St uint8 *)
(* let subBytes_ x = *)
(*   let b = inverse x in *)
(*   let b4 = rotate_right b 4 in *)
(*   let b5 = rotate_right b 5 in *)
(*   let b6 = rotate_right b 6 in *)
(*   let b7 = rotate_right b 7 in *)
(*   b ^^ b4 ^^ b5 ^^ b6 ^^ b7 ^^ of_int 0x63 *)

(* val subBytes_aux: state:uint8s -> ctr:nat -> St unit *)
(* let rec subBytes_aux state ctr = *)
(*   admit(); *)
(*   match ctr with *)
(*   | 16 -> () *)
(*   | _ -> *)
(*     let si = index state ctr in *)
(*     let si' = subBytes_ si in *)
(*     upd state ctr si'; *)
(*     subBytes_aux state (ctr+1); *)
(*     () *)

val subBytes_aux_sbox: state:uint8s -> uint8s -> ctr:nat -> St unit
let rec subBytes_aux_sbox state sbox ctr =
  if ctr = 16 then ()
  else 
  begin
    let si = index state ctr in
    let si' = access sbox si in
    upd state ctr si';
    subBytes_aux_sbox state sbox (ctr+1)
  end

(* val subBytes: state:uint8s -> St unit *)
(* let subBytes state =  *)
(*   admit(); *)
(*   subBytes_aux state 0 *)

val subBytes_sbox: state:uint8s -> uint8s -> St unit
let subBytes_sbox state sbox =
  subBytes_aux_sbox state sbox 0

val shiftRows: state:uint8s{length state = 16} -> St unit
let shiftRows state =
  admit();
  let i = 1 in
  let tmp = index state i in
  upd state i      (index state (i+4)); 
  upd state (i+4)  (index state (i+8)); 
  upd state (i+8)  (index state (i+12)); 
  upd state (i+12) tmp;
  let i = 2 in
  let tmp = index state i in
  upd state i      (index state (i+8)); 
  upd state (i+8)  tmp; 
  let tmp = index state (i+4) in
  upd state (i+4)  (index state (i+12)); 
  upd state (i+12) tmp;
  let i = 3 in
  let tmp = index state i in
  upd state i      (index state (i+12)); 
  upd state (i+12) (index state (i+8));
  upd state (i+8)  (index state (i+4)); 
  upd state (i+4)  tmp; 
  ()

val multiply_2: uint8 -> uint8 -> Tot uint8 
let multiply_2 x y =
  (((y ^& one) ^*% x) 
  ^^ (((y ^>> 1) ^& one) ^*% xtime(x))
  ^^ (((y ^>> 2) ^& one) ^*% xtime(xtime(x)))
  ^^ (((y ^>> 3) ^& one) ^*% xtime(xtime(xtime(x)))))
       
let op_Star = Prims.op_Multiply

val mixColumns: uint8s -> St unit
let mixColumns state =
  admit();
  let c = 0 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state (4*c+0) (multiply (of_int 0x2) s0 ^^ multiply (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state (4*c+1) (multiply (of_int 0x2) s1 ^^ multiply (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state (4*c+2) (multiply (of_int 0x2) s2 ^^ multiply (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state (4*c+3) (multiply (of_int 0x2) s3 ^^ multiply (of_int 0x3) s0 ^^ s1 ^^ s2);
  let c = 1 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state (4*c+0) (multiply (of_int 0x2) s0 ^^ multiply (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state (4*c+1) (multiply (of_int 0x2) s1 ^^ multiply (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state (4*c+2) (multiply (of_int 0x2) s2 ^^ multiply (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state (4*c+3) (multiply (of_int 0x2) s3 ^^ multiply (of_int 0x3) s0 ^^ s1 ^^ s2);
  let c = 2 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state (4*c+0) (multiply (of_int 0x2) s0 ^^ multiply (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state (4*c+1) (multiply (of_int 0x2) s1 ^^ multiply (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state (4*c+2) (multiply (of_int 0x2) s2 ^^ multiply (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state (4*c+3) (multiply (of_int 0x2) s3 ^^ multiply (of_int 0x3) s0 ^^ s1 ^^ s2);
  let c = 3 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state (4*c+0) (multiply (of_int 0x2) s0 ^^ multiply (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state (4*c+1) (multiply (of_int 0x2) s1 ^^ multiply (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state (4*c+2) (multiply (of_int 0x2) s2 ^^ multiply (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state (4*c+3) (multiply (of_int 0x2) s3 ^^ multiply (of_int 0x3) s0 ^^ s1 ^^ s2);
  ()

val addRoundKey: uint8s -> uint8s -> nat -> St unit
let addRoundKey state w round =
  admit();
  let c = 0 in
  let s0 = index state (4*c+0) in
  let s1 = index state (4*c+1) in
  let s2 = index state (4*c+2) in
  let s3 = index state (4*c+3) in
  let w0 = index w (4*round*nb+4*c+0) in
  let w1 = index w (4*round*nb+4*c+1) in
  let w2 = index w (4*round*nb+4*c+2) in
  let w3 = index w (4*round*nb+4*c+3) in
  upd state (4*c+0) (s0 ^^ w0);
  upd state (4*c+1) (s1 ^^ w1);
  upd state (4*c+2) (s2 ^^ w2);
  upd state (4*c+3) (s3 ^^ w3);
  let c = 1 in
  let s0 = index state (4*c+0) in
  let s1 = index state (4*c+1) in
  let s2 = index state (4*c+2) in
  let s3 = index state (4*c+3) in
  let w0 = index w (4*round*nb+4*c+0) in
  let w1 = index w (4*round*nb+4*c+1) in
  let w2 = index w (4*round*nb+4*c+2) in
  let w3 = index w (4*round*nb+4*c+3) in
  upd state (4*c+0) (s0 ^^ w0);
  upd state (4*c+1) (s1 ^^ w1);
  upd state (4*c+2) (s2 ^^ w2);
  upd state (4*c+3) (s3 ^^ w3);
  let c = 2 in
  let s0 = index state (4*c+0) in
  let s1 = index state (4*c+1) in
  let s2 = index state (4*c+2) in
  let s3 = index state (4*c+3) in
  let w0 = index w (4*round*nb+4*c+0) in
  let w1 = index w (4*round*nb+4*c+1) in
  let w2 = index w (4*round*nb+4*c+2) in
  let w3 = index w (4*round*nb+4*c+3) in
  upd state (4*c+0) (s0 ^^ w0);
  upd state (4*c+1) (s1 ^^ w1);
  upd state (4*c+2) (s2 ^^ w2);
  upd state (4*c+3) (s3 ^^ w3);
  let c = 3 in
  let s0 = index state (4*c+0) in
  let s1 = index state (4*c+1) in
  let s2 = index state (4*c+2) in
  let s3 = index state (4*c+3) in
  let w0 = index w (4*round*nb+4*c+0) in
  let w1 = index w (4*round*nb+4*c+1) in
  let w2 = index w (4*round*nb+4*c+2) in
  let w3 = index w (4*round*nb+4*c+3) in
  upd state (4*c+0) (s0 ^^ w0);
  upd state (4*c+1) (s1 ^^ w1);
  upd state (4*c+2) (s2 ^^ w2);
  upd state (4*c+3) (s3 ^^ w3);
  ()

val cipher_loop: state:uint8s -> w:uint8s -> uint8s -> round:nat -> St unit
let rec cipher_loop state w sbox round = 
  if round = 14 then ()
  else begin
    subBytes_sbox state sbox;
    shiftRows state;
    mixColumns state;
    addRoundKey state w round; 
    cipher_loop state w sbox (round+1)
  end

(* val cipher_loop: state:uint8s -> w:uint8s -> round:nat -> St unit *)
(* let rec cipher_loop state w round =  *)
(*   admit(); *)
(*   match round with *)
(*   | 14 -> () *)
(*   | _ ->  *)
(*     subBytes state; *)
(*     shiftRows state; *)
(*     mixColumns state; *)
(*     addRoundKey state w round;  *)
(*     cipher_loop state w (round+1); *)
(*     () *)

val cipher: out:uint8s{length out = 4 * nb} -> input:uint8s{length input = 4*nb} -> w:uint8s{length w = 4 * (nr+1)} -> sbox:uint8s{length sbox = 256} -> St unit
let cipher out input w sbox =
  let state = create SInt.UInt8.zero (4*nb) in
  blit input 0 state 0 (4*nb);
  addRoundKey state w 0;
  cipher_loop state w sbox 1;
  subBytes_sbox state sbox;
  shiftRows state;
  addRoundKey state w nr;
  blit state 0 out 0 (4*nb);
  ()

(* val cipher: out:uint8s{length out = 4 * nb} -> input:uint8s{length input = 4*nb} -> w:uint8s{length w = 4 * (nr+1)} -> St unit *)
(* let cipher out input w = *)
(*   admit(); *)
(*   let state = create SInt.UInt8.zero (4*nb) in *)
(*   blit input 0 state 0 (4*nb); *)
(*   addRoundKey state w 0; *)
(*   cipher_loop state w 1; *)
(*   subBytes state; *)
(*   shiftRows state; *)
(*   addRoundKey state w nr; *)
(*   blit state 0 out 0 (4*nb); *)
(*   () *)

val rotWord: word:uint8s{length word = 4} -> St unit
let rotWord word =
  let w0 = index word 0 in
  let w1 = index word 1 in
  let w2 = index word 2 in
  let w3 = index word 3 in
  upd word 0 w1;
  upd word 1 w2;
  upd word 2 w3;
  upd word 3 w0;
  ()
  
val subWord: word:uint8s{length word = 4} -> sbox:uint8s -> St unit
let subWord word sbox =
  let w0 = index word 0 in
  let w1 = index word 1 in
  let w2 = index word 2 in
  let w3 = index word 3 in
  upd word 0 (access sbox w0);
  upd word 1 (access sbox w1);
  upd word 2 (access sbox w2);
  upd word 3 (access sbox w3);
  ()  
  
(* val subWord: word:uint8s{length word = 4} -> St unit *)
(* let subWord word = *)
(*   let w0 = index word 0 in *)
(*   let w1 = index word 1 in *)
(*   let w2 = index word 2 in *)
(*   let w3 = index word 3 in *)
(*   upd word 0 (subBytes_ w0); *)
(*   upd word 1 (subBytes_ w1); *)
(*   upd word 2 (subBytes_ w2); *)
(*   upd word 3 (subBytes_ w3); *)
(*   ()   *)

(* TODO: use table ? *)
val rcon: nat -> uint8 -> Tot uint8
let rec rcon i tmp =
  if i = 1 then tmp
  else begin
    let tmp = multiply (of_int 0x2) tmp in    
    rcon (i-1) tmp
  end

val keyExpansion_aux: uint8s -> uint8s -> uint8s -> uint8s -> nat -> St unit
let rec keyExpansion_aux key w temp sbox i =
  if i = 240 then ()
  else begin
    blit w (i-4) temp 0 4;
    if (i/4) % nk = 0 then (
      rotWord temp;
      subWord temp sbox;
      upd temp 0 (index temp 0 ^^ rcon ((i/4)/nk) one) 
    ) else if ((i/4) % nk = 4) then (
      subWord temp sbox
    );
    let w0 = index w (i+0-4*nk) in
    let w1 = index w (i+1-4*nk) in
    let w2 = index w (i+2-4*nk) in
    let w3 = index w (i+3-4*nk) in
    let t0 = index temp (0) in
    let t1 = index temp (1) in
    let t2 = index temp (2) in
    let t3 = index temp (3) in
    upd w (i+0) (t0 ^^ w0);
    upd w (i+1) (t1 ^^ w1);
    upd w (i+2) (t2 ^^ w2);
    upd w (i+3) (t3 ^^ w3);
    keyExpansion_aux key w temp sbox (i+4)
  end
  
(* val keyExpansion_aux: uint8s -> uint8s -> uint8s -> nat -> St unit *)
(* let rec keyExpansion_aux key w temp i = *)
(*   admit(); *)
(*   match i with *)
(*   | 240 -> () *)
(*   | _ -> *)
(*     blit w (i-4) temp 0 4; *)
(*     if (i/4) % nk = 0 then ( *)
(*       rotWord temp; *)
(*       subWord temp; *)
(*       upd temp 0 (index temp 0 ^^ rcon ((i/4)/nk) one)  *)
(*     ) else if ((i/4) % nk = 4) then ( *)
(*       subWord(temp) *)
(*     ); *)
(*     let w0 = index w (i+0-4*nk) in *)
(*     let w1 = index w (i+1-4*nk) in *)
(*     let w2 = index w (i+2-4*nk) in *)
(*     let w3 = index w (i+3-4*nk) in *)
(*     let t0 = index temp (0) in *)
(*     let t1 = index temp (1) in *)
(*     let t2 = index temp (2) in *)
(*     let t3 = index temp (3) in *)
(*     upd w (i+0) (t0 ^^ w0); *)
(*     upd w (i+1) (t1 ^^ w1); *)
(*     upd w (i+2) (t2 ^^ w2); *)
(*     upd w (i+3) (t3 ^^ w3); *)
(*     keyExpansion_aux key w temp (i+4); *)
(*     () *)
    
val keyExpansion: key:uint8s{length key = 4 * nk} -> w:uint8s{length w = 4 * (nb * (nr+1))} -> sbox:uint8s -> St unit
let keyExpansion key w sbox =
  let temp = create #8 zero 4 in
  blit key 0 w 0 (4*nk);
  let i = 4 * nk in
  keyExpansion_aux key w temp sbox i

val invShiftRows: state:uint8s{length state = 16} -> St unit
let invShiftRows state =
  let i = 3 in
  let tmp = index state i in
  upd state i      (index state (i+4)); 
  upd state (i+4)  (index state (i+8)); 
  upd state (i+8)  (index state (i+12)); 
  upd state (i+12) tmp;
  let i = 2 in
  let tmp = index state i in
  upd state i      (index state (i+8)); 
  upd state (i+8)  tmp; 
  let tmp = index state (i+4) in
  upd state (i+4)  (index state (i+12)); 
  upd state (i+12) tmp;
  let i = 1 in
  let tmp = index state i in
  upd state i      (index state (i+12)); 
  upd state (i+12) (index state (i+8));
  upd state (i+8)  (index state (i+4)); 
  upd state (i+4)  tmp; 
  ()

(* val invSubBytes_: uint8 -> St uint8 *)
(* let invSubBytes_ x = *)
(*   let b = x ^^ of_int 0x63 in *)
(*   let b1 = rotate_left b 1 in *)
(*   let b3 = rotate_left b 3 in *)
(*   let b6 = rotate_left b 6 in *)
(*   let b = b1 ^^ b3 ^^ b6 in *)
(*   inverse b *)

(* val invSubBytes_aux: state:uint8s -> ctr:nat -> St unit *)
(* let rec invSubBytes_aux state ctr = *)
(*   admit(); *)
(*   match ctr with *)
(*   | 16 -> () *)
(*   | _ -> *)
(*     let si = index state ctr in *)
(*     let si' = invSubBytes_ si in *)
(*     upd state ctr si'; *)
(*     invSubBytes_aux state (ctr+1); *)
(*     () *)

val invSubBytes_aux_sbox: state:uint8s -> sbox:uint8s -> ctr:nat -> St unit
let rec invSubBytes_aux_sbox state sbox ctr =
  if ctr = 16 then () 
  else begin 
    let si = index state ctr in
    let si' = access sbox si in
    upd state ctr si';
    invSubBytes_aux_sbox state sbox (ctr+1)
  end

val invSubBytes_sbox: state:uint8s -> uint8s -> St unit
let invSubBytes_sbox state sbox = 
  invSubBytes_aux_sbox state sbox 0
       
val invMixColumns: uint8s -> St unit
let invMixColumns state =
  let c = 0 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state (4*c+0) (multiply (of_int 0xe) s0 ^^ multiply (of_int 0xb) s1 
	       ^^ multiply (of_int 0xd) s2 ^^ multiply (of_int 0x9) s3);
  upd state (4*c+1) (multiply (of_int 0xe) s1 ^^ multiply (of_int 0xb) s2 
	       ^^ multiply (of_int 0xd) s3 ^^ multiply (of_int 0x9) s0);
  upd state (4*c+2) (multiply (of_int 0xe) s2 ^^ multiply (of_int 0xb) s3 
	       ^^ multiply (of_int 0xd) s0 ^^ multiply (of_int 0x9) s1);
  upd state (4*c+3) (multiply (of_int 0xe) s3 ^^ multiply (of_int 0xb) s0 
	       ^^ multiply (of_int 0xd) s1 ^^ multiply (of_int 0x9) s2);
  let c = 1 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state (4*c+0) (multiply (of_int 0xe) s0 ^^ multiply (of_int 0xb) s1 
	       ^^ multiply (of_int 0xd) s2 ^^ multiply (of_int 0x9) s3);
  upd state (4*c+1) (multiply (of_int 0xe) s1 ^^ multiply (of_int 0xb) s2 
	       ^^ multiply (of_int 0xd) s3 ^^ multiply (of_int 0x9) s0);
  upd state (4*c+2) (multiply (of_int 0xe) s2 ^^ multiply (of_int 0xb) s3 
	       ^^ multiply (of_int 0xd) s0 ^^ multiply (of_int 0x9) s1);
  upd state (4*c+3) (multiply (of_int 0xe) s3 ^^ multiply (of_int 0xb) s0 
	       ^^ multiply (of_int 0xd) s1 ^^ multiply (of_int 0x9) s2);
  let c = 2 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state (4*c+0) (multiply (of_int 0xe) s0 ^^ multiply (of_int 0xb) s1 
	       ^^ multiply (of_int 0xd) s2 ^^ multiply (of_int 0x9) s3);
  upd state (4*c+1) (multiply (of_int 0xe) s1 ^^ multiply (of_int 0xb) s2 
	       ^^ multiply (of_int 0xd) s3 ^^ multiply (of_int 0x9) s0);
  upd state (4*c+2) (multiply (of_int 0xe) s2 ^^ multiply (of_int 0xb) s3 
	       ^^ multiply (of_int 0xd) s0 ^^ multiply (of_int 0x9) s1);
  upd state (4*c+3) (multiply (of_int 0xe) s3 ^^ multiply (of_int 0xb) s0 
	       ^^ multiply (of_int 0xd) s1 ^^ multiply (of_int 0x9) s2);
  let c = 3 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state (4*c+0) (multiply (of_int 0xe) s0 ^^ multiply (of_int 0xb) s1 
	       ^^ multiply (of_int 0xd) s2 ^^ multiply (of_int 0x9) s3);
  upd state (4*c+1) (multiply (of_int 0xe) s1 ^^ multiply (of_int 0xb) s2 
	       ^^ multiply (of_int 0xd) s3 ^^ multiply (of_int 0x9) s0);
  upd state (4*c+2) (multiply (of_int 0xe) s2 ^^ multiply (of_int 0xb) s3 
	       ^^ multiply (of_int 0xd) s0 ^^ multiply (of_int 0x9) s1);
  upd state (4*c+3) (multiply (of_int 0xe) s3 ^^ multiply (of_int 0xb) s0 
	       ^^ multiply (of_int 0xd) s1 ^^ multiply (of_int 0x9) s2);
  ()

val inv_cipher_loop: state:uint8s -> w:uint8s -> uint8s -> round:nat -> St unit
let rec inv_cipher_loop state w sbox round = 
  if round = 0 then ()
  else begin
    invShiftRows state;
    invSubBytes_sbox state sbox;
    addRoundKey state w round; 
    invMixColumns state;
    inv_cipher_loop state w sbox (round-1)
  end

val inv_cipher: out:uint8s{length out = 4 * nb} -> input:uint8s{length input = 4*nb} -> w:uint8s{length w = 4 * (nr+1)} -> sbox:uint8s{length sbox = 256} -> St unit
let inv_cipher out input w sbox =
  let state = create SInt.UInt8.zero (4*nb) in
  blit input 0 state 0 (4*nb);
  addRoundKey state w nr;
  inv_cipher_loop state w sbox 13;
  invShiftRows state;
  invSubBytes_sbox state sbox;
  addRoundKey state w 0;
  blit state 0 out 0 (4*nb)
