module AES

open FStar.Ghost
open FStar.StackHeap2
open FStar.SST
open SInt
open SInt.UInt8
open FStar.Buffer

#set-options "--lax"

(* JK: bug, it is necessary to add this type abbreviation to make things typecheck *)
type suint8 = uint8   // 
type uint32 = UInt32.t
type suint8s = buffer suint8

// Parameters for AES-256 
let nk = UInt32.uint_to_t 8
let nb = UInt32.uint_to_t 4
let nr = UInt32.uint_to_t 14

val xtime: b:suint8 -> Tot suint8 
let xtime b = 
  (b ^<< 1) ^^ (((b ^>> 7) ^& one) ^*% of_string "0x1b")

val multiply: a:suint8 -> b:suint8 -> Tot suint8
let multiply a b =
  ((a ^*% (b ^& one))
  ^^ (xtime a ^*% ((b ^>> 1) ^& one))
  ^^ (xtime (xtime a) ^*% ((b ^>> 2) ^& one))
  ^^ (xtime (xtime (xtime a)) ^*% ((b ^>> 3) ^& one))
  ^^ (xtime (xtime (xtime (xtime a))) ^*% ((b ^>> 4) ^& one))
  ^^ (xtime (xtime (xtime (xtime (xtime a)))) ^*% ((b ^>> 5) ^& one))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime a))))) ^*% ((b ^>> 6) ^& one))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime (xtime a)))))) ^*% ((b ^>> 7) ^& one)))

val mk_sbox: sbox:suint8s{length sbox = 64} -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let mk_sbox sbox = 
  upd sbox (UInt32.uint_to_t 0   ) (SInt.UInt8.of_int 0x63); upd sbox (UInt32.uint_to_t 1   ) (SInt.UInt8.of_int 0x7c); upd sbox (UInt32.uint_to_t 2   ) (SInt.UInt8.of_int 0x77); upd sbox (UInt32.uint_to_t 3   ) (SInt.UInt8.of_int 0x7b); 
  upd sbox (UInt32.uint_to_t 4   ) (SInt.UInt8.of_int 0xf2); upd sbox (UInt32.uint_to_t 5   ) (SInt.UInt8.of_int 0x6b); upd sbox (UInt32.uint_to_t 6   ) (SInt.UInt8.of_int 0x6f); upd sbox (UInt32.uint_to_t 7   ) (SInt.UInt8.of_int 0xc5); 
  upd sbox (UInt32.uint_to_t 8   ) (SInt.UInt8.of_int 0x30); upd sbox (UInt32.uint_to_t 9   ) (SInt.UInt8.of_int 0x01); upd sbox (UInt32.uint_to_t 10  ) (SInt.UInt8.of_int 0x67); upd sbox (UInt32.uint_to_t 11  ) (SInt.UInt8.of_int 0x2b); 
  upd sbox (UInt32.uint_to_t 12  ) (SInt.UInt8.of_int 0xfe); upd sbox (UInt32.uint_to_t 13  ) (SInt.UInt8.of_int 0xd7); upd sbox (UInt32.uint_to_t 14  ) (SInt.UInt8.of_int 0xab); upd sbox (UInt32.uint_to_t 15  ) (SInt.UInt8.of_int 0x76); 
  upd sbox (UInt32.uint_to_t 16  ) (SInt.UInt8.of_int 0xca); upd sbox (UInt32.uint_to_t 17  ) (SInt.UInt8.of_int 0x82); upd sbox (UInt32.uint_to_t 18  ) (SInt.UInt8.of_int 0xc9); upd sbox (UInt32.uint_to_t 19  ) (SInt.UInt8.of_int 0x7d); 
  upd sbox (UInt32.uint_to_t 20  ) (SInt.UInt8.of_int 0xfa); upd sbox (UInt32.uint_to_t 21  ) (SInt.UInt8.of_int 0x59); upd sbox (UInt32.uint_to_t 22  ) (SInt.UInt8.of_int 0x47); upd sbox (UInt32.uint_to_t 23  ) (SInt.UInt8.of_int 0xf0); 
  upd sbox (UInt32.uint_to_t 24  ) (SInt.UInt8.of_int 0xad); upd sbox (UInt32.uint_to_t 25  ) (SInt.UInt8.of_int 0xd4); upd sbox (UInt32.uint_to_t 26  ) (SInt.UInt8.of_int 0xa2); upd sbox (UInt32.uint_to_t 27  ) (SInt.UInt8.of_int 0xaf); 
  upd sbox (UInt32.uint_to_t 28  ) (SInt.UInt8.of_int 0x9c); upd sbox (UInt32.uint_to_t 29  ) (SInt.UInt8.of_int 0xa4); upd sbox (UInt32.uint_to_t 30  ) (SInt.UInt8.of_int 0x72); upd sbox (UInt32.uint_to_t 31  ) (SInt.UInt8.of_int 0xc0); 
  upd sbox (UInt32.uint_to_t 32  ) (SInt.UInt8.of_int 0xb7); upd sbox (UInt32.uint_to_t 33  ) (SInt.UInt8.of_int 0xfd); upd sbox (UInt32.uint_to_t 34  ) (SInt.UInt8.of_int 0x93); upd sbox (UInt32.uint_to_t 35  ) (SInt.UInt8.of_int 0x26); 
  upd sbox (UInt32.uint_to_t 36  ) (SInt.UInt8.of_int 0x36); upd sbox (UInt32.uint_to_t 37  ) (SInt.UInt8.of_int 0x3f); upd sbox (UInt32.uint_to_t 38  ) (SInt.UInt8.of_int 0xf7); upd sbox (UInt32.uint_to_t 39  ) (SInt.UInt8.of_int 0xcc); 
  upd sbox (UInt32.uint_to_t 40  ) (SInt.UInt8.of_int 0x34); upd sbox (UInt32.uint_to_t 41  ) (SInt.UInt8.of_int 0xa5); upd sbox (UInt32.uint_to_t 42  ) (SInt.UInt8.of_int 0xe5); upd sbox (UInt32.uint_to_t 43  ) (SInt.UInt8.of_int 0xf1); 
  upd sbox (UInt32.uint_to_t 44  ) (SInt.UInt8.of_int 0x71); upd sbox (UInt32.uint_to_t 45  ) (SInt.UInt8.of_int 0xd8); upd sbox (UInt32.uint_to_t 46  ) (SInt.UInt8.of_int 0x31); upd sbox (UInt32.uint_to_t 47  ) (SInt.UInt8.of_int 0x15); 
  upd sbox (UInt32.uint_to_t 48  ) (SInt.UInt8.of_int 0x04); upd sbox (UInt32.uint_to_t 49  ) (SInt.UInt8.of_int 0xc7); upd sbox (UInt32.uint_to_t 50  ) (SInt.UInt8.of_int 0x23); upd sbox (UInt32.uint_to_t 51  ) (SInt.UInt8.of_int 0xc3); 
  upd sbox (UInt32.uint_to_t 52  ) (SInt.UInt8.of_int 0x18); upd sbox (UInt32.uint_to_t 53  ) (SInt.UInt8.of_int 0x96); upd sbox (UInt32.uint_to_t 54  ) (SInt.UInt8.of_int 0x05); upd sbox (UInt32.uint_to_t 55  ) (SInt.UInt8.of_int 0x9a); 
  upd sbox (UInt32.uint_to_t 56  ) (SInt.UInt8.of_int 0x07); upd sbox (UInt32.uint_to_t 57  ) (SInt.UInt8.of_int 0x12); upd sbox (UInt32.uint_to_t 58  ) (SInt.UInt8.of_int 0x80); upd sbox (UInt32.uint_to_t 59  ) (SInt.UInt8.of_int 0xe2); 
  upd sbox (UInt32.uint_to_t 60  ) (SInt.UInt8.of_int 0xeb); upd sbox (UInt32.uint_to_t 61  ) (SInt.UInt8.of_int 0x27); upd sbox (UInt32.uint_to_t 62  ) (SInt.UInt8.of_int 0xb2); upd sbox (UInt32.uint_to_t 63  ) (SInt.UInt8.of_int 0x75); 
  upd sbox (UInt32.uint_to_t 64  ) (SInt.UInt8.of_int 0x09); upd sbox (UInt32.uint_to_t 65  ) (SInt.UInt8.of_int 0x83); upd sbox (UInt32.uint_to_t 66  ) (SInt.UInt8.of_int 0x2c); upd sbox (UInt32.uint_to_t 67  ) (SInt.UInt8.of_int 0x1a); 
  upd sbox (UInt32.uint_to_t 68  ) (SInt.UInt8.of_int 0x1b); upd sbox (UInt32.uint_to_t 69  ) (SInt.UInt8.of_int 0x6e); upd sbox (UInt32.uint_to_t 70  ) (SInt.UInt8.of_int 0x5a); upd sbox (UInt32.uint_to_t 71  ) (SInt.UInt8.of_int 0xa0); 
  upd sbox (UInt32.uint_to_t 72  ) (SInt.UInt8.of_int 0x52); upd sbox (UInt32.uint_to_t 73  ) (SInt.UInt8.of_int 0x3b); upd sbox (UInt32.uint_to_t 74  ) (SInt.UInt8.of_int 0xd6); upd sbox (UInt32.uint_to_t 75  ) (SInt.UInt8.of_int 0xb3); 
  upd sbox (UInt32.uint_to_t 76  ) (SInt.UInt8.of_int 0x29); upd sbox (UInt32.uint_to_t 77  ) (SInt.UInt8.of_int 0xe3); upd sbox (UInt32.uint_to_t 78  ) (SInt.UInt8.of_int 0x2f); upd sbox (UInt32.uint_to_t 79  ) (SInt.UInt8.of_int 0x84); 
  upd sbox (UInt32.uint_to_t 80  ) (SInt.UInt8.of_int 0x53); upd sbox (UInt32.uint_to_t 81  ) (SInt.UInt8.of_int 0xd1); upd sbox (UInt32.uint_to_t 82  ) (SInt.UInt8.of_int 0x00); upd sbox (UInt32.uint_to_t 83  ) (SInt.UInt8.of_int 0xed); 
  upd sbox (UInt32.uint_to_t 84  ) (SInt.UInt8.of_int 0x20); upd sbox (UInt32.uint_to_t 85  ) (SInt.UInt8.of_int 0xfc); upd sbox (UInt32.uint_to_t 86  ) (SInt.UInt8.of_int 0xb1); upd sbox (UInt32.uint_to_t 87  ) (SInt.UInt8.of_int 0x5b); 
  upd sbox (UInt32.uint_to_t 88  ) (SInt.UInt8.of_int 0x6a); upd sbox (UInt32.uint_to_t 89  ) (SInt.UInt8.of_int 0xcb); upd sbox (UInt32.uint_to_t 90  ) (SInt.UInt8.of_int 0xbe); upd sbox (UInt32.uint_to_t 91  ) (SInt.UInt8.of_int 0x39); 
  upd sbox (UInt32.uint_to_t 92  ) (SInt.UInt8.of_int 0x4a); upd sbox (UInt32.uint_to_t 93  ) (SInt.UInt8.of_int 0x4c); upd sbox (UInt32.uint_to_t 94  ) (SInt.UInt8.of_int 0x58); upd sbox (UInt32.uint_to_t 95  ) (SInt.UInt8.of_int 0xcf); 
  upd sbox (UInt32.uint_to_t 96  ) (SInt.UInt8.of_int 0xd0); upd sbox (UInt32.uint_to_t 97  ) (SInt.UInt8.of_int 0xef); upd sbox (UInt32.uint_to_t 98  ) (SInt.UInt8.of_int 0xaa); upd sbox (UInt32.uint_to_t 99  ) (SInt.UInt8.of_int 0xfb); 
  upd sbox (UInt32.uint_to_t 100 ) (SInt.UInt8.of_int 0x43); upd sbox (UInt32.uint_to_t 101 ) (SInt.UInt8.of_int 0x4d); upd sbox (UInt32.uint_to_t 102 ) (SInt.UInt8.of_int 0x33); upd sbox (UInt32.uint_to_t 103 ) (SInt.UInt8.of_int 0x85); 
  upd sbox (UInt32.uint_to_t 104 ) (SInt.UInt8.of_int 0x45); upd sbox (UInt32.uint_to_t 105 ) (SInt.UInt8.of_int 0xf9); upd sbox (UInt32.uint_to_t 106 ) (SInt.UInt8.of_int 0x02); upd sbox (UInt32.uint_to_t 107 ) (SInt.UInt8.of_int 0x7f); 
  upd sbox (UInt32.uint_to_t 108 ) (SInt.UInt8.of_int 0x50); upd sbox (UInt32.uint_to_t 109 ) (SInt.UInt8.of_int 0x3c); upd sbox (UInt32.uint_to_t 110 ) (SInt.UInt8.of_int 0x9f); upd sbox (UInt32.uint_to_t 111 ) (SInt.UInt8.of_int 0xa8); 
  upd sbox (UInt32.uint_to_t 112 ) (SInt.UInt8.of_int 0x51); upd sbox (UInt32.uint_to_t 113 ) (SInt.UInt8.of_int 0xa3); upd sbox (UInt32.uint_to_t 114 ) (SInt.UInt8.of_int 0x40); upd sbox (UInt32.uint_to_t 115 ) (SInt.UInt8.of_int 0x8f); 
  upd sbox (UInt32.uint_to_t 116 ) (SInt.UInt8.of_int 0x92); upd sbox (UInt32.uint_to_t 117 ) (SInt.UInt8.of_int 0x9d); upd sbox (UInt32.uint_to_t 118 ) (SInt.UInt8.of_int 0x38); upd sbox (UInt32.uint_to_t 119 ) (SInt.UInt8.of_int 0xf5); 
  upd sbox (UInt32.uint_to_t 120 ) (SInt.UInt8.of_int 0xbc); upd sbox (UInt32.uint_to_t 121 ) (SInt.UInt8.of_int 0xb6); upd sbox (UInt32.uint_to_t 122 ) (SInt.UInt8.of_int 0xda); upd sbox (UInt32.uint_to_t 123 ) (SInt.UInt8.of_int 0x21); 
  upd sbox (UInt32.uint_to_t 124 ) (SInt.UInt8.of_int 0x10); upd sbox (UInt32.uint_to_t 125 ) (SInt.UInt8.of_int 0xff); upd sbox (UInt32.uint_to_t 126 ) (SInt.UInt8.of_int 0xf3); upd sbox (UInt32.uint_to_t 127 ) (SInt.UInt8.of_int 0xd2); 
  upd sbox (UInt32.uint_to_t 128 ) (SInt.UInt8.of_int 0xcd); upd sbox (UInt32.uint_to_t 129 ) (SInt.UInt8.of_int 0x0c); upd sbox (UInt32.uint_to_t 130 ) (SInt.UInt8.of_int 0x13); upd sbox (UInt32.uint_to_t 131 ) (SInt.UInt8.of_int 0xec); 
  upd sbox (UInt32.uint_to_t 132 ) (SInt.UInt8.of_int 0x5f); upd sbox (UInt32.uint_to_t 133 ) (SInt.UInt8.of_int 0x97); upd sbox (UInt32.uint_to_t 134 ) (SInt.UInt8.of_int 0x44); upd sbox (UInt32.uint_to_t 135 ) (SInt.UInt8.of_int 0x17); 
  upd sbox (UInt32.uint_to_t 136 ) (SInt.UInt8.of_int 0xc4); upd sbox (UInt32.uint_to_t 137 ) (SInt.UInt8.of_int 0xa7); upd sbox (UInt32.uint_to_t 138 ) (SInt.UInt8.of_int 0x7e); upd sbox (UInt32.uint_to_t 139 ) (SInt.UInt8.of_int 0x3d); 
  upd sbox (UInt32.uint_to_t 140 ) (SInt.UInt8.of_int 0x64); upd sbox (UInt32.uint_to_t 141 ) (SInt.UInt8.of_int 0x5d); upd sbox (UInt32.uint_to_t 142 ) (SInt.UInt8.of_int 0x19); upd sbox (UInt32.uint_to_t 143 ) (SInt.UInt8.of_int 0x73); 
  upd sbox (UInt32.uint_to_t 144 ) (SInt.UInt8.of_int 0x60); upd sbox (UInt32.uint_to_t 145 ) (SInt.UInt8.of_int 0x81); upd sbox (UInt32.uint_to_t 146 ) (SInt.UInt8.of_int 0x4f); upd sbox (UInt32.uint_to_t 147 ) (SInt.UInt8.of_int 0xdc); 
  upd sbox (UInt32.uint_to_t 148 ) (SInt.UInt8.of_int 0x22); upd sbox (UInt32.uint_to_t 149 ) (SInt.UInt8.of_int 0x2a); upd sbox (UInt32.uint_to_t 150 ) (SInt.UInt8.of_int 0x90); upd sbox (UInt32.uint_to_t 151 ) (SInt.UInt8.of_int 0x88); 
  upd sbox (UInt32.uint_to_t 152 ) (SInt.UInt8.of_int 0x46); upd sbox (UInt32.uint_to_t 153 ) (SInt.UInt8.of_int 0xee); upd sbox (UInt32.uint_to_t 154 ) (SInt.UInt8.of_int 0xb8); upd sbox (UInt32.uint_to_t 155 ) (SInt.UInt8.of_int 0x14); 
  upd sbox (UInt32.uint_to_t 156 ) (SInt.UInt8.of_int 0xde); upd sbox (UInt32.uint_to_t 157 ) (SInt.UInt8.of_int 0x5e); upd sbox (UInt32.uint_to_t 158 ) (SInt.UInt8.of_int 0x0b); upd sbox (UInt32.uint_to_t 159 ) (SInt.UInt8.of_int 0xdb); 
  upd sbox (UInt32.uint_to_t 160 ) (SInt.UInt8.of_int 0xe0); upd sbox (UInt32.uint_to_t 161 ) (SInt.UInt8.of_int 0x32); upd sbox (UInt32.uint_to_t 162 ) (SInt.UInt8.of_int 0x3a); upd sbox (UInt32.uint_to_t 163 ) (SInt.UInt8.of_int 0x0a); 
  upd sbox (UInt32.uint_to_t 164 ) (SInt.UInt8.of_int 0x49); upd sbox (UInt32.uint_to_t 165 ) (SInt.UInt8.of_int 0x06); upd sbox (UInt32.uint_to_t 166 ) (SInt.UInt8.of_int 0x24); upd sbox (UInt32.uint_to_t 167 ) (SInt.UInt8.of_int 0x5c); 
  upd sbox (UInt32.uint_to_t 168 ) (SInt.UInt8.of_int 0xc2); upd sbox (UInt32.uint_to_t 169 ) (SInt.UInt8.of_int 0xd3); upd sbox (UInt32.uint_to_t 170 ) (SInt.UInt8.of_int 0xac); upd sbox (UInt32.uint_to_t 171 ) (SInt.UInt8.of_int 0x62); 
  upd sbox (UInt32.uint_to_t 172 ) (SInt.UInt8.of_int 0x91); upd sbox (UInt32.uint_to_t 173 ) (SInt.UInt8.of_int 0x95); upd sbox (UInt32.uint_to_t 174 ) (SInt.UInt8.of_int 0xe4); upd sbox (UInt32.uint_to_t 175 ) (SInt.UInt8.of_int 0x79); 
  upd sbox (UInt32.uint_to_t 176 ) (SInt.UInt8.of_int 0xe7); upd sbox (UInt32.uint_to_t 177 ) (SInt.UInt8.of_int 0xc8); upd sbox (UInt32.uint_to_t 178 ) (SInt.UInt8.of_int 0x37); upd sbox (UInt32.uint_to_t 179 ) (SInt.UInt8.of_int 0x6d); 
  upd sbox (UInt32.uint_to_t 180 ) (SInt.UInt8.of_int 0x8d); upd sbox (UInt32.uint_to_t 181 ) (SInt.UInt8.of_int 0xd5); upd sbox (UInt32.uint_to_t 182 ) (SInt.UInt8.of_int 0x4e); upd sbox (UInt32.uint_to_t 183 ) (SInt.UInt8.of_int 0xa9); 
  upd sbox (UInt32.uint_to_t 184 ) (SInt.UInt8.of_int 0x6c); upd sbox (UInt32.uint_to_t 185 ) (SInt.UInt8.of_int 0x56); upd sbox (UInt32.uint_to_t 186 ) (SInt.UInt8.of_int 0xf4); upd sbox (UInt32.uint_to_t 187 ) (SInt.UInt8.of_int 0xea); 
  upd sbox (UInt32.uint_to_t 188 ) (SInt.UInt8.of_int 0x65); upd sbox (UInt32.uint_to_t 189 ) (SInt.UInt8.of_int 0x7a); upd sbox (UInt32.uint_to_t 190 ) (SInt.UInt8.of_int 0xae); upd sbox (UInt32.uint_to_t 191 ) (SInt.UInt8.of_int 0x08); 
  upd sbox (UInt32.uint_to_t 192 ) (SInt.UInt8.of_int 0xba); upd sbox (UInt32.uint_to_t 193 ) (SInt.UInt8.of_int 0x78); upd sbox (UInt32.uint_to_t 194 ) (SInt.UInt8.of_int 0x25); upd sbox (UInt32.uint_to_t 195 ) (SInt.UInt8.of_int 0x2e); 
  upd sbox (UInt32.uint_to_t 196 ) (SInt.UInt8.of_int 0x1c); upd sbox (UInt32.uint_to_t 197 ) (SInt.UInt8.of_int 0xa6); upd sbox (UInt32.uint_to_t 198 ) (SInt.UInt8.of_int 0xb4); upd sbox (UInt32.uint_to_t 199 ) (SInt.UInt8.of_int 0xc6); 
  upd sbox (UInt32.uint_to_t 200 ) (SInt.UInt8.of_int 0xe8); upd sbox (UInt32.uint_to_t 201 ) (SInt.UInt8.of_int 0xdd); upd sbox (UInt32.uint_to_t 202 ) (SInt.UInt8.of_int 0x74); upd sbox (UInt32.uint_to_t 203 ) (SInt.UInt8.of_int 0x1f); 
  upd sbox (UInt32.uint_to_t 204 ) (SInt.UInt8.of_int 0x4b); upd sbox (UInt32.uint_to_t 205 ) (SInt.UInt8.of_int 0xbd); upd sbox (UInt32.uint_to_t 206 ) (SInt.UInt8.of_int 0x8b); upd sbox (UInt32.uint_to_t 207 ) (SInt.UInt8.of_int 0x8a); 
  upd sbox (UInt32.uint_to_t 208 ) (SInt.UInt8.of_int 0x70); upd sbox (UInt32.uint_to_t 209 ) (SInt.UInt8.of_int 0x3e); upd sbox (UInt32.uint_to_t 210 ) (SInt.UInt8.of_int 0xb5); upd sbox (UInt32.uint_to_t 211 ) (SInt.UInt8.of_int 0x66); 
  upd sbox (UInt32.uint_to_t 212 ) (SInt.UInt8.of_int 0x48); upd sbox (UInt32.uint_to_t 213 ) (SInt.UInt8.of_int 0x03); upd sbox (UInt32.uint_to_t 214 ) (SInt.UInt8.of_int 0xf6); upd sbox (UInt32.uint_to_t 215 ) (SInt.UInt8.of_int 0x0e); 
  upd sbox (UInt32.uint_to_t 216 ) (SInt.UInt8.of_int 0x61); upd sbox (UInt32.uint_to_t 217 ) (SInt.UInt8.of_int 0x35); upd sbox (UInt32.uint_to_t 218 ) (SInt.UInt8.of_int 0x57); upd sbox (UInt32.uint_to_t 219 ) (SInt.UInt8.of_int 0xb9); 
  upd sbox (UInt32.uint_to_t 220 ) (SInt.UInt8.of_int 0x86); upd sbox (UInt32.uint_to_t 221 ) (SInt.UInt8.of_int 0xc1); upd sbox (UInt32.uint_to_t 222 ) (SInt.UInt8.of_int 0x1d); upd sbox (UInt32.uint_to_t 223 ) (SInt.UInt8.of_int 0x9e); 
  upd sbox (UInt32.uint_to_t 224 ) (SInt.UInt8.of_int 0xe1); upd sbox (UInt32.uint_to_t 225 ) (SInt.UInt8.of_int 0xf8); upd sbox (UInt32.uint_to_t 226 ) (SInt.UInt8.of_int 0x98); upd sbox (UInt32.uint_to_t 227 ) (SInt.UInt8.of_int 0x11); 
  upd sbox (UInt32.uint_to_t 228 ) (SInt.UInt8.of_int 0x69); upd sbox (UInt32.uint_to_t 229 ) (SInt.UInt8.of_int 0xd9); upd sbox (UInt32.uint_to_t 230 ) (SInt.UInt8.of_int 0x8e); upd sbox (UInt32.uint_to_t 231 ) (SInt.UInt8.of_int 0x94); 
  upd sbox (UInt32.uint_to_t 232 ) (SInt.UInt8.of_int 0x9b); upd sbox (UInt32.uint_to_t 233 ) (SInt.UInt8.of_int 0x1e); upd sbox (UInt32.uint_to_t 234 ) (SInt.UInt8.of_int 0x87); upd sbox (UInt32.uint_to_t 235 ) (SInt.UInt8.of_int 0xe9); 
  upd sbox (UInt32.uint_to_t 236 ) (SInt.UInt8.of_int 0xce); upd sbox (UInt32.uint_to_t 237 ) (SInt.UInt8.of_int 0x55); upd sbox (UInt32.uint_to_t 238 ) (SInt.UInt8.of_int 0x28); upd sbox (UInt32.uint_to_t 239 ) (SInt.UInt8.of_int 0xdf); 
  upd sbox (UInt32.uint_to_t 240 ) (SInt.UInt8.of_int 0x8c); upd sbox (UInt32.uint_to_t 241 ) (SInt.UInt8.of_int 0xa1); upd sbox (UInt32.uint_to_t 242 ) (SInt.UInt8.of_int 0x89); upd sbox (UInt32.uint_to_t 243 ) (SInt.UInt8.of_int 0x0d); 
  upd sbox (UInt32.uint_to_t 244 ) (SInt.UInt8.of_int 0xbf); upd sbox (UInt32.uint_to_t 245 ) (SInt.UInt8.of_int 0xe6); upd sbox (UInt32.uint_to_t 246 ) (SInt.UInt8.of_int 0x42); upd sbox (UInt32.uint_to_t 247 ) (SInt.UInt8.of_int 0x68); 
  upd sbox (UInt32.uint_to_t 248 ) (SInt.UInt8.of_int 0x41); upd sbox (UInt32.uint_to_t 249 ) (SInt.UInt8.of_int 0x99); upd sbox (UInt32.uint_to_t 250 ) (SInt.UInt8.of_int 0x2d); upd sbox (UInt32.uint_to_t 251 ) (SInt.UInt8.of_int 0x0f); 
  upd sbox (UInt32.uint_to_t 252 ) (SInt.UInt8.of_int 0xb0); upd sbox (UInt32.uint_to_t 253 ) (SInt.UInt8.of_int 0x54); upd sbox (UInt32.uint_to_t 254 ) (SInt.UInt8.of_int 0xbb); upd sbox (UInt32.uint_to_t 255 ) (SInt.UInt8.of_int 0x16)

val mk_inv_sbox: sbox:suint8s{length sbox = 64} -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let mk_inv_sbox sbox = 
  upd sbox (UInt32.uint_to_t 0   ) (SInt.UInt8.of_int 0x52); upd sbox (UInt32.uint_to_t 1   ) (SInt.UInt8.of_int 0x09); upd sbox (UInt32.uint_to_t 2   ) (SInt.UInt8.of_int 0x6a); upd sbox (UInt32.uint_to_t 3   ) (SInt.UInt8.of_int 0xd5); 
  upd sbox (UInt32.uint_to_t 4   ) (SInt.UInt8.of_int 0x30); upd sbox (UInt32.uint_to_t 5   ) (SInt.UInt8.of_int 0x36); upd sbox (UInt32.uint_to_t 6   ) (SInt.UInt8.of_int 0xa5); upd sbox (UInt32.uint_to_t 7   ) (SInt.UInt8.of_int 0x38); 
  upd sbox (UInt32.uint_to_t 8   ) (SInt.UInt8.of_int 0xbf); upd sbox (UInt32.uint_to_t 9   ) (SInt.UInt8.of_int 0x40); upd sbox (UInt32.uint_to_t 10  ) (SInt.UInt8.of_int 0xa3); upd sbox (UInt32.uint_to_t 11  ) (SInt.UInt8.of_int 0x9e); 
  upd sbox (UInt32.uint_to_t 12  ) (SInt.UInt8.of_int 0x81); upd sbox (UInt32.uint_to_t 13  ) (SInt.UInt8.of_int 0xf3); upd sbox (UInt32.uint_to_t 14  ) (SInt.UInt8.of_int 0xd7); upd sbox (UInt32.uint_to_t 15  ) (SInt.UInt8.of_int 0xfb); 
  upd sbox (UInt32.uint_to_t 16  ) (SInt.UInt8.of_int 0x7c); upd sbox (UInt32.uint_to_t 17  ) (SInt.UInt8.of_int 0xe3); upd sbox (UInt32.uint_to_t 18  ) (SInt.UInt8.of_int 0x39); upd sbox (UInt32.uint_to_t 19  ) (SInt.UInt8.of_int 0x82); 
  upd sbox (UInt32.uint_to_t 20  ) (SInt.UInt8.of_int 0x9b); upd sbox (UInt32.uint_to_t 21  ) (SInt.UInt8.of_int 0x2f); upd sbox (UInt32.uint_to_t 22  ) (SInt.UInt8.of_int 0xff); upd sbox (UInt32.uint_to_t 23  ) (SInt.UInt8.of_int 0x87); 
  upd sbox (UInt32.uint_to_t 24  ) (SInt.UInt8.of_int 0x34); upd sbox (UInt32.uint_to_t 25  ) (SInt.UInt8.of_int 0x8e); upd sbox (UInt32.uint_to_t 26  ) (SInt.UInt8.of_int 0x43); upd sbox (UInt32.uint_to_t 27  ) (SInt.UInt8.of_int 0x44); 
  upd sbox (UInt32.uint_to_t 28  ) (SInt.UInt8.of_int 0xc4); upd sbox (UInt32.uint_to_t 29  ) (SInt.UInt8.of_int 0xde); upd sbox (UInt32.uint_to_t 30  ) (SInt.UInt8.of_int 0xe9); upd sbox (UInt32.uint_to_t 31  ) (SInt.UInt8.of_int 0xcb); 
  upd sbox (UInt32.uint_to_t 32  ) (SInt.UInt8.of_int 0x54); upd sbox (UInt32.uint_to_t 33  ) (SInt.UInt8.of_int 0x7b); upd sbox (UInt32.uint_to_t 34  ) (SInt.UInt8.of_int 0x94); upd sbox (UInt32.uint_to_t 35  ) (SInt.UInt8.of_int 0x32); 
  upd sbox (UInt32.uint_to_t 36  ) (SInt.UInt8.of_int 0xa6); upd sbox (UInt32.uint_to_t 37  ) (SInt.UInt8.of_int 0xc2); upd sbox (UInt32.uint_to_t 38  ) (SInt.UInt8.of_int 0x23); upd sbox (UInt32.uint_to_t 39  ) (SInt.UInt8.of_int 0x3d); 
  upd sbox (UInt32.uint_to_t 40  ) (SInt.UInt8.of_int 0xee); upd sbox (UInt32.uint_to_t 41  ) (SInt.UInt8.of_int 0x4c); upd sbox (UInt32.uint_to_t 42  ) (SInt.UInt8.of_int 0x95); upd sbox (UInt32.uint_to_t 43  ) (SInt.UInt8.of_int 0x0b); 
  upd sbox (UInt32.uint_to_t 44  ) (SInt.UInt8.of_int 0x42); upd sbox (UInt32.uint_to_t 45  ) (SInt.UInt8.of_int 0xfa); upd sbox (UInt32.uint_to_t 46  ) (SInt.UInt8.of_int 0xc3); upd sbox (UInt32.uint_to_t 47  ) (SInt.UInt8.of_int 0x4e); 
  upd sbox (UInt32.uint_to_t 48  ) (SInt.UInt8.of_int 0x08); upd sbox (UInt32.uint_to_t 49  ) (SInt.UInt8.of_int 0x2e); upd sbox (UInt32.uint_to_t 50  ) (SInt.UInt8.of_int 0xa1); upd sbox (UInt32.uint_to_t 51  ) (SInt.UInt8.of_int 0x66); 
  upd sbox (UInt32.uint_to_t 52  ) (SInt.UInt8.of_int 0x28); upd sbox (UInt32.uint_to_t 53  ) (SInt.UInt8.of_int 0xd9); upd sbox (UInt32.uint_to_t 54  ) (SInt.UInt8.of_int 0x24); upd sbox (UInt32.uint_to_t 55  ) (SInt.UInt8.of_int 0xb2); 
  upd sbox (UInt32.uint_to_t 56  ) (SInt.UInt8.of_int 0x76); upd sbox (UInt32.uint_to_t 57  ) (SInt.UInt8.of_int 0x5b); upd sbox (UInt32.uint_to_t 58  ) (SInt.UInt8.of_int 0xa2); upd sbox (UInt32.uint_to_t 59  ) (SInt.UInt8.of_int 0x49); 
  upd sbox (UInt32.uint_to_t 60  ) (SInt.UInt8.of_int 0x6d); upd sbox (UInt32.uint_to_t 61  ) (SInt.UInt8.of_int 0x8b); upd sbox (UInt32.uint_to_t 62  ) (SInt.UInt8.of_int 0xd1); upd sbox (UInt32.uint_to_t 63  ) (SInt.UInt8.of_int 0x25); 
  upd sbox (UInt32.uint_to_t 64  ) (SInt.UInt8.of_int 0x72); upd sbox (UInt32.uint_to_t 65  ) (SInt.UInt8.of_int 0xf8); upd sbox (UInt32.uint_to_t 66  ) (SInt.UInt8.of_int 0xf6); upd sbox (UInt32.uint_to_t 67  ) (SInt.UInt8.of_int 0x64); 
  upd sbox (UInt32.uint_to_t 68  ) (SInt.UInt8.of_int 0x86); upd sbox (UInt32.uint_to_t 69  ) (SInt.UInt8.of_int 0x68); upd sbox (UInt32.uint_to_t 70  ) (SInt.UInt8.of_int 0x98); upd sbox (UInt32.uint_to_t 71  ) (SInt.UInt8.of_int 0x16); 
  upd sbox (UInt32.uint_to_t 72  ) (SInt.UInt8.of_int 0xd4); upd sbox (UInt32.uint_to_t 73  ) (SInt.UInt8.of_int 0xa4); upd sbox (UInt32.uint_to_t 74  ) (SInt.UInt8.of_int 0x5c); upd sbox (UInt32.uint_to_t 75  ) (SInt.UInt8.of_int 0xcc); 
  upd sbox (UInt32.uint_to_t 76  ) (SInt.UInt8.of_int 0x5d); upd sbox (UInt32.uint_to_t 77  ) (SInt.UInt8.of_int 0x65); upd sbox (UInt32.uint_to_t 78  ) (SInt.UInt8.of_int 0xb6); upd sbox (UInt32.uint_to_t 79  ) (SInt.UInt8.of_int 0x92); 
  upd sbox (UInt32.uint_to_t 80  ) (SInt.UInt8.of_int 0x6c); upd sbox (UInt32.uint_to_t 81  ) (SInt.UInt8.of_int 0x70); upd sbox (UInt32.uint_to_t 82  ) (SInt.UInt8.of_int 0x48); upd sbox (UInt32.uint_to_t 83  ) (SInt.UInt8.of_int 0x50); 
  upd sbox (UInt32.uint_to_t 84  ) (SInt.UInt8.of_int 0xfd); upd sbox (UInt32.uint_to_t 85  ) (SInt.UInt8.of_int 0xed); upd sbox (UInt32.uint_to_t 86  ) (SInt.UInt8.of_int 0xb9); upd sbox (UInt32.uint_to_t 87  ) (SInt.UInt8.of_int 0xda); 
  upd sbox (UInt32.uint_to_t 88  ) (SInt.UInt8.of_int 0x5e); upd sbox (UInt32.uint_to_t 89  ) (SInt.UInt8.of_int 0x15); upd sbox (UInt32.uint_to_t 90  ) (SInt.UInt8.of_int 0x46); upd sbox (UInt32.uint_to_t 91  ) (SInt.UInt8.of_int 0x57); 
  upd sbox (UInt32.uint_to_t 92  ) (SInt.UInt8.of_int 0xa7); upd sbox (UInt32.uint_to_t 93  ) (SInt.UInt8.of_int 0x8d); upd sbox (UInt32.uint_to_t 94  ) (SInt.UInt8.of_int 0x9d); upd sbox (UInt32.uint_to_t 95  ) (SInt.UInt8.of_int 0x84); 
  upd sbox (UInt32.uint_to_t 96  ) (SInt.UInt8.of_int 0x90); upd sbox (UInt32.uint_to_t 97  ) (SInt.UInt8.of_int 0xd8); upd sbox (UInt32.uint_to_t 98  ) (SInt.UInt8.of_int 0xab); upd sbox (UInt32.uint_to_t 99  ) (SInt.UInt8.of_int 0x00); 
  upd sbox (UInt32.uint_to_t 100 ) (SInt.UInt8.of_int 0x8c); upd sbox (UInt32.uint_to_t 101 ) (SInt.UInt8.of_int 0xbc); upd sbox (UInt32.uint_to_t 102 ) (SInt.UInt8.of_int 0xd3); upd sbox (UInt32.uint_to_t 103 ) (SInt.UInt8.of_int 0x0a); 
  upd sbox (UInt32.uint_to_t 104 ) (SInt.UInt8.of_int 0xf7); upd sbox (UInt32.uint_to_t 105 ) (SInt.UInt8.of_int 0xe4); upd sbox (UInt32.uint_to_t 106 ) (SInt.UInt8.of_int 0x58); upd sbox (UInt32.uint_to_t 107 ) (SInt.UInt8.of_int 0x05); 
  upd sbox (UInt32.uint_to_t 108 ) (SInt.UInt8.of_int 0xb8); upd sbox (UInt32.uint_to_t 109 ) (SInt.UInt8.of_int 0xb3); upd sbox (UInt32.uint_to_t 110 ) (SInt.UInt8.of_int 0x45); upd sbox (UInt32.uint_to_t 111 ) (SInt.UInt8.of_int 0x06); 
  upd sbox (UInt32.uint_to_t 112 ) (SInt.UInt8.of_int 0xd0); upd sbox (UInt32.uint_to_t 113 ) (SInt.UInt8.of_int 0x2c); upd sbox (UInt32.uint_to_t 114 ) (SInt.UInt8.of_int 0x1e); upd sbox (UInt32.uint_to_t 115 ) (SInt.UInt8.of_int 0x8f); 
  upd sbox (UInt32.uint_to_t 116 ) (SInt.UInt8.of_int 0xca); upd sbox (UInt32.uint_to_t 117 ) (SInt.UInt8.of_int 0x3f); upd sbox (UInt32.uint_to_t 118 ) (SInt.UInt8.of_int 0x0f); upd sbox (UInt32.uint_to_t 119 ) (SInt.UInt8.of_int 0x02); 
  upd sbox (UInt32.uint_to_t 120 ) (SInt.UInt8.of_int 0xc1); upd sbox (UInt32.uint_to_t 121 ) (SInt.UInt8.of_int 0xaf); upd sbox (UInt32.uint_to_t 122 ) (SInt.UInt8.of_int 0xbd); upd sbox (UInt32.uint_to_t 123 ) (SInt.UInt8.of_int 0x03); 
  upd sbox (UInt32.uint_to_t 124 ) (SInt.UInt8.of_int 0x01); upd sbox (UInt32.uint_to_t 125 ) (SInt.UInt8.of_int 0x13); upd sbox (UInt32.uint_to_t 126 ) (SInt.UInt8.of_int 0x8a); upd sbox (UInt32.uint_to_t 127 ) (SInt.UInt8.of_int 0x6b); 
  upd sbox (UInt32.uint_to_t 128 ) (SInt.UInt8.of_int 0x3a); upd sbox (UInt32.uint_to_t 129 ) (SInt.UInt8.of_int 0x91); upd sbox (UInt32.uint_to_t 130 ) (SInt.UInt8.of_int 0x11); upd sbox (UInt32.uint_to_t 131 ) (SInt.UInt8.of_int 0x41); 
  upd sbox (UInt32.uint_to_t 132 ) (SInt.UInt8.of_int 0x4f); upd sbox (UInt32.uint_to_t 133 ) (SInt.UInt8.of_int 0x67); upd sbox (UInt32.uint_to_t 134 ) (SInt.UInt8.of_int 0xdc); upd sbox (UInt32.uint_to_t 135 ) (SInt.UInt8.of_int 0xea); 
  upd sbox (UInt32.uint_to_t 136 ) (SInt.UInt8.of_int 0x97); upd sbox (UInt32.uint_to_t 137 ) (SInt.UInt8.of_int 0xf2); upd sbox (UInt32.uint_to_t 138 ) (SInt.UInt8.of_int 0xcf); upd sbox (UInt32.uint_to_t 139 ) (SInt.UInt8.of_int 0xce); 
  upd sbox (UInt32.uint_to_t 140 ) (SInt.UInt8.of_int 0xf0); upd sbox (UInt32.uint_to_t 141 ) (SInt.UInt8.of_int 0xb4); upd sbox (UInt32.uint_to_t 142 ) (SInt.UInt8.of_int 0xe6); upd sbox (UInt32.uint_to_t 143 ) (SInt.UInt8.of_int 0x73); 
  upd sbox (UInt32.uint_to_t 144 ) (SInt.UInt8.of_int 0x96); upd sbox (UInt32.uint_to_t 145 ) (SInt.UInt8.of_int 0xac); upd sbox (UInt32.uint_to_t 146 ) (SInt.UInt8.of_int 0x74); upd sbox (UInt32.uint_to_t 147 ) (SInt.UInt8.of_int 0x22); 
  upd sbox (UInt32.uint_to_t 148 ) (SInt.UInt8.of_int 0xe7); upd sbox (UInt32.uint_to_t 149 ) (SInt.UInt8.of_int 0xad); upd sbox (UInt32.uint_to_t 150 ) (SInt.UInt8.of_int 0x35); upd sbox (UInt32.uint_to_t 151 ) (SInt.UInt8.of_int 0x85); 
  upd sbox (UInt32.uint_to_t 152 ) (SInt.UInt8.of_int 0xe2); upd sbox (UInt32.uint_to_t 153 ) (SInt.UInt8.of_int 0xf9); upd sbox (UInt32.uint_to_t 154 ) (SInt.UInt8.of_int 0x37); upd sbox (UInt32.uint_to_t 155 ) (SInt.UInt8.of_int 0xe8); 
  upd sbox (UInt32.uint_to_t 156 ) (SInt.UInt8.of_int 0x1c); upd sbox (UInt32.uint_to_t 157 ) (SInt.UInt8.of_int 0x75); upd sbox (UInt32.uint_to_t 158 ) (SInt.UInt8.of_int 0xdf); upd sbox (UInt32.uint_to_t 159 ) (SInt.UInt8.of_int 0x6e); 
  upd sbox (UInt32.uint_to_t 160 ) (SInt.UInt8.of_int 0x47); upd sbox (UInt32.uint_to_t 161 ) (SInt.UInt8.of_int 0xf1); upd sbox (UInt32.uint_to_t 162 ) (SInt.UInt8.of_int 0x1a); upd sbox (UInt32.uint_to_t 163 ) (SInt.UInt8.of_int 0x71); 
  upd sbox (UInt32.uint_to_t 164 ) (SInt.UInt8.of_int 0x1d); upd sbox (UInt32.uint_to_t 165 ) (SInt.UInt8.of_int 0x29); upd sbox (UInt32.uint_to_t 166 ) (SInt.UInt8.of_int 0xc5); upd sbox (UInt32.uint_to_t 167 ) (SInt.UInt8.of_int 0x89); 
  upd sbox (UInt32.uint_to_t 168 ) (SInt.UInt8.of_int 0x6f); upd sbox (UInt32.uint_to_t 169 ) (SInt.UInt8.of_int 0xb7); upd sbox (UInt32.uint_to_t 170 ) (SInt.UInt8.of_int 0x62); upd sbox (UInt32.uint_to_t 171 ) (SInt.UInt8.of_int 0x0e); 
  upd sbox (UInt32.uint_to_t 172 ) (SInt.UInt8.of_int 0xaa); upd sbox (UInt32.uint_to_t 173 ) (SInt.UInt8.of_int 0x18); upd sbox (UInt32.uint_to_t 174 ) (SInt.UInt8.of_int 0xbe); upd sbox (UInt32.uint_to_t 175 ) (SInt.UInt8.of_int 0x1b); 
  upd sbox (UInt32.uint_to_t 176 ) (SInt.UInt8.of_int 0xfc); upd sbox (UInt32.uint_to_t 177 ) (SInt.UInt8.of_int 0x56); upd sbox (UInt32.uint_to_t 178 ) (SInt.UInt8.of_int 0x3e); upd sbox (UInt32.uint_to_t 179 ) (SInt.UInt8.of_int 0x4b); 
  upd sbox (UInt32.uint_to_t 180 ) (SInt.UInt8.of_int 0xc6); upd sbox (UInt32.uint_to_t 181 ) (SInt.UInt8.of_int 0xd2); upd sbox (UInt32.uint_to_t 182 ) (SInt.UInt8.of_int 0x79); upd sbox (UInt32.uint_to_t 183 ) (SInt.UInt8.of_int 0x20); 
  upd sbox (UInt32.uint_to_t 184 ) (SInt.UInt8.of_int 0x9a); upd sbox (UInt32.uint_to_t 185 ) (SInt.UInt8.of_int 0xdb); upd sbox (UInt32.uint_to_t 186 ) (SInt.UInt8.of_int 0xc0); upd sbox (UInt32.uint_to_t 187 ) (SInt.UInt8.of_int 0xfe); 
  upd sbox (UInt32.uint_to_t 188 ) (SInt.UInt8.of_int 0x78); upd sbox (UInt32.uint_to_t 189 ) (SInt.UInt8.of_int 0xcd); upd sbox (UInt32.uint_to_t 190 ) (SInt.UInt8.of_int 0x5a); upd sbox (UInt32.uint_to_t 191 ) (SInt.UInt8.of_int 0xf4); 
  upd sbox (UInt32.uint_to_t 192 ) (SInt.UInt8.of_int 0x1f); upd sbox (UInt32.uint_to_t 193 ) (SInt.UInt8.of_int 0xdd); upd sbox (UInt32.uint_to_t 194 ) (SInt.UInt8.of_int 0xa8); upd sbox (UInt32.uint_to_t 195 ) (SInt.UInt8.of_int 0x33); 
  upd sbox (UInt32.uint_to_t 196 ) (SInt.UInt8.of_int 0x88); upd sbox (UInt32.uint_to_t 197 ) (SInt.UInt8.of_int 0x07); upd sbox (UInt32.uint_to_t 198 ) (SInt.UInt8.of_int 0xc7); upd sbox (UInt32.uint_to_t 199 ) (SInt.UInt8.of_int 0x31); 
  upd sbox (UInt32.uint_to_t 200 ) (SInt.UInt8.of_int 0xb1); upd sbox (UInt32.uint_to_t 201 ) (SInt.UInt8.of_int 0x12); upd sbox (UInt32.uint_to_t 202 ) (SInt.UInt8.of_int 0x10); upd sbox (UInt32.uint_to_t 203 ) (SInt.UInt8.of_int 0x59); 
  upd sbox (UInt32.uint_to_t 204 ) (SInt.UInt8.of_int 0x27); upd sbox (UInt32.uint_to_t 205 ) (SInt.UInt8.of_int 0x80); upd sbox (UInt32.uint_to_t 206 ) (SInt.UInt8.of_int 0xec); upd sbox (UInt32.uint_to_t 207 ) (SInt.UInt8.of_int 0x5f); 
  upd sbox (UInt32.uint_to_t 208 ) (SInt.UInt8.of_int 0x60); upd sbox (UInt32.uint_to_t 209 ) (SInt.UInt8.of_int 0x51); upd sbox (UInt32.uint_to_t 210 ) (SInt.UInt8.of_int 0x7f); upd sbox (UInt32.uint_to_t 211 ) (SInt.UInt8.of_int 0xa9); 
  upd sbox (UInt32.uint_to_t 212 ) (SInt.UInt8.of_int 0x19); upd sbox (UInt32.uint_to_t 213 ) (SInt.UInt8.of_int 0xb5); upd sbox (UInt32.uint_to_t 214 ) (SInt.UInt8.of_int 0x4a); upd sbox (UInt32.uint_to_t 215 ) (SInt.UInt8.of_int 0x0d); 
  upd sbox (UInt32.uint_to_t 216 ) (SInt.UInt8.of_int 0x2d); upd sbox (UInt32.uint_to_t 217 ) (SInt.UInt8.of_int 0xe5); upd sbox (UInt32.uint_to_t 218 ) (SInt.UInt8.of_int 0x7a); upd sbox (UInt32.uint_to_t 219 ) (SInt.UInt8.of_int 0x9f); 
  upd sbox (UInt32.uint_to_t 220 ) (SInt.UInt8.of_int 0x93); upd sbox (UInt32.uint_to_t 221 ) (SInt.UInt8.of_int 0xc9); upd sbox (UInt32.uint_to_t 222 ) (SInt.UInt8.of_int 0x9c); upd sbox (UInt32.uint_to_t 223 ) (SInt.UInt8.of_int 0xef); 
  upd sbox (UInt32.uint_to_t 224 ) (SInt.UInt8.of_int 0xa0); upd sbox (UInt32.uint_to_t 225 ) (SInt.UInt8.of_int 0xe0); upd sbox (UInt32.uint_to_t 226 ) (SInt.UInt8.of_int 0x3b); upd sbox (UInt32.uint_to_t 227 ) (SInt.UInt8.of_int 0x4d); 
  upd sbox (UInt32.uint_to_t 228 ) (SInt.UInt8.of_int 0xae); upd sbox (UInt32.uint_to_t 229 ) (SInt.UInt8.of_int 0x2a); upd sbox (UInt32.uint_to_t 230 ) (SInt.UInt8.of_int 0xf5); upd sbox (UInt32.uint_to_t 231 ) (SInt.UInt8.of_int 0xb0); 
  upd sbox (UInt32.uint_to_t 232 ) (SInt.UInt8.of_int 0xc8); upd sbox (UInt32.uint_to_t 233 ) (SInt.UInt8.of_int 0xeb); upd sbox (UInt32.uint_to_t 234 ) (SInt.UInt8.of_int 0xbb); upd sbox (UInt32.uint_to_t 235 ) (SInt.UInt8.of_int 0x3c); 
  upd sbox (UInt32.uint_to_t 236 ) (SInt.UInt8.of_int 0x83); upd sbox (UInt32.uint_to_t 237 ) (SInt.UInt8.of_int 0x53); upd sbox (UInt32.uint_to_t 238 ) (SInt.UInt8.of_int 0x99); upd sbox (UInt32.uint_to_t 239 ) (SInt.UInt8.of_int 0x61); 
  upd sbox (UInt32.uint_to_t 240 ) (SInt.UInt8.of_int 0x17); upd sbox (UInt32.uint_to_t 241 ) (SInt.UInt8.of_int 0x2b); upd sbox (UInt32.uint_to_t 242 ) (SInt.UInt8.of_int 0x04); upd sbox (UInt32.uint_to_t 243 ) (SInt.UInt8.of_int 0x7e); 
  upd sbox (UInt32.uint_to_t 244 ) (SInt.UInt8.of_int 0xba); upd sbox (UInt32.uint_to_t 245 ) (SInt.UInt8.of_int 0x77); upd sbox (UInt32.uint_to_t 246 ) (SInt.UInt8.of_int 0xd6); upd sbox (UInt32.uint_to_t 247 ) (SInt.UInt8.of_int 0x26); 
  upd sbox (UInt32.uint_to_t 248 ) (SInt.UInt8.of_int 0xe1); upd sbox (UInt32.uint_to_t 249 ) (SInt.UInt8.of_int 0x69); upd sbox (UInt32.uint_to_t 250 ) (SInt.UInt8.of_int 0x14); upd sbox (UInt32.uint_to_t 251 ) (SInt.UInt8.of_int 0x63); 
  upd sbox (UInt32.uint_to_t 252 ) (SInt.UInt8.of_int 0x55); upd sbox (UInt32.uint_to_t 253 ) (SInt.UInt8.of_int 0x21); upd sbox (UInt32.uint_to_t 254 ) (SInt.UInt8.of_int 0x0c); upd sbox (UInt32.uint_to_t 255 ) (SInt.UInt8.of_int 0x7d)

val access: sbox:suint8s -> idx:suint8 -> STL suint8
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True)) 
let access sbox i =
  let rec access_aux: suint8s -> suint8 -> uint32 -> suint8 -> STL suint8
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = fun sbox i ctr tmp -> 
      if UInt32.eq ctr (UInt32.uint_to_t 256) then tmp 
      else let mask = SInt.UInt8.eq i (of_uint32 ctr) in
	 let tmp = tmp ^| (mask ^& index sbox ctr) in
	 access_aux sbox i (UInt32.add ctr (UInt32.uint_to_t 1)) tmp in
  access_aux sbox i (UInt32.uint_to_t 0) SInt.UInt8.zero

val subBytes_aux_sbox: state:suint8s -> suint8s -> ctr:uint32 -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rec subBytes_aux_sbox state sbox ctr =
  if UInt32.eq ctr (UInt32.uint_to_t 16) then ()
  else 
  begin
    let si = index state ctr in
    let si' = access sbox si in
    upd state ctr si';
    subBytes_aux_sbox state sbox (UInt32.add ctr (UInt32.uint_to_t 1))
  end

val subBytes_sbox: state:suint8s -> suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let subBytes_sbox state sbox =
  subBytes_aux_sbox state sbox (UInt32.uint_to_t 0)

val shiftRows: state:suint8s{length state = 16} -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let shiftRows state =
  let i = (UInt32.uint_to_t 1) in
  let tmp = index state i in
  upd state i      (index state (UInt32.add i (UInt32.uint_to_t 4))); 
  upd state (UInt32.add i (UInt32.uint_to_t 4))  (index state (UInt32.add i (UInt32.uint_to_t 8))); 
  upd state (UInt32.add i (UInt32.uint_to_t 8))  (index state (UInt32.add i (UInt32.uint_to_t 12))); 
  upd state (UInt32.add i (UInt32.uint_to_t 12)) tmp;
  let i = UInt32.uint_to_t 2 in
  let tmp = index state i in
  upd state i (index state (UInt32.add i (UInt32.uint_to_t 8))); 
  upd state (UInt32.add i (UInt32.uint_to_t 8))  tmp; 
  let tmp = index state (UInt32.add i (UInt32.uint_to_t 4)) in
  upd state (UInt32.add i (UInt32.uint_to_t 4))  (index state (UInt32.add i (UInt32.uint_to_t 12))); 
  upd state (UInt32.add i (UInt32.uint_to_t 12)) tmp;
  let i = UInt32.uint_to_t 3 in
  let tmp = index state i in
  upd state i      (index state (UInt32.add i (UInt32.uint_to_t 12))); 
  upd state (UInt32.add i (UInt32.uint_to_t 12)) (index state (UInt32.add i (UInt32.uint_to_t 8)));
  upd state (UInt32.add i (UInt32.uint_to_t 8))  (index state (UInt32.add i (UInt32.uint_to_t 4))); 
  upd state (UInt32.add i (UInt32.uint_to_t 4))  tmp; 
  ()

val multiply_2: suint8 -> suint8 -> Tot suint8 
let multiply_2 x y =
  (((y ^& one) ^*% x) 
  ^^ (((y ^>> 1) ^& one) ^*% xtime(x))
  ^^ (((y ^>> 2) ^& one) ^*% xtime(xtime(x)))
  ^^ (((y ^>> 3) ^& one) ^*% xtime(xtime(xtime(x)))))
       
let op_Star = UInt32.mul
let op_At_Plus = UInt32.add
let op_At_Subtraction = UInt32.sub

val mixColumns: suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let mixColumns state =
  let c = (UInt32.uint_to_t 0) in
  let zero = (UInt32.uint_to_t 0) in
  let one = (UInt32.uint_to_t 1) in
  let two = UInt32.add one one in
  let three = UInt32.add two one in
  let four = UInt32.add two two in
  let s0 = index state (UInt32.add zero  (four*c)) in
  let s1 = index state (UInt32.add one   (four*c)) in
  let s2 = index state (UInt32.add two   (four*c)) in
  let s3 = index state (UInt32.add three (four*c)) in
  upd state ((four*c) @+ zero ) (multiply (of_int 0x2) s0 ^^ multiply (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state ((four*c) @+ one  ) (multiply (of_int 0x2) s1 ^^ multiply (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state ((four*c) @+ two  ) (multiply (of_int 0x2) s2 ^^ multiply (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state ((four*c) @+ three) (multiply (of_int 0x2) s3 ^^ multiply (of_int 0x3) s0 ^^ s1 ^^ s2);
  let c = one in
  let s0 = index state (zero  @+ (four*c)) in
  let s1 = index state (one   @+ (four*c)) in
  let s2 = index state (two   @+ (four*c)) in
  let s3 = index state (three @+ (four*c)) in
  upd state ((four*c) @+ zero ) (multiply (of_int 0x2) s0 ^^ multiply (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state ((four*c) @+ one  ) (multiply (of_int 0x2) s1 ^^ multiply (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state ((four*c) @+ two  ) (multiply (of_int 0x2) s2 ^^ multiply (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state ((four*c) @+ three) (multiply (of_int 0x2) s3 ^^ multiply (of_int 0x3) s0 ^^ s1 ^^ s2);
  let c = two in
  let s0 = index state (zero  @+ (four*c)) in
  let s1 = index state (one   @+ (four*c)) in
  let s2 = index state (two   @+ (four*c)) in
  let s3 = index state (three @+ (four*c)) in
  upd state ((four*c) @+ zero ) (multiply (of_int 0x2) s0 ^^ multiply (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state ((four*c) @+ one  ) (multiply (of_int 0x2) s1 ^^ multiply (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state ((four*c) @+ two  ) (multiply (of_int 0x2) s2 ^^ multiply (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state ((four*c) @+ three) (multiply (of_int 0x2) s3 ^^ multiply (of_int 0x3) s0 ^^ s1 ^^ s2);
  let c = three in
  let s0 = index state (zero  @+ (four*c)) in
  let s1 = index state (one   @+ (four*c)) in
  let s2 = index state (two   @+ (four*c)) in
  let s3 = index state (three @+ (four*c)) in
  upd state ((four*c) @+ zero ) (multiply (of_int 0x2) s0 ^^ multiply (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state ((four*c) @+ one  ) (multiply (of_int 0x2) s1 ^^ multiply (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state ((four*c) @+ two  ) (multiply (of_int 0x2) s2 ^^ multiply (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state ((four*c) @+ three) (multiply (of_int 0x2) s3 ^^ multiply (of_int 0x3) s0 ^^ s1 ^^ s2);
  ()

val addRoundKey: suint8s -> suint8s -> uint32 -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let addRoundKey state w round =
  let zero  = (UInt32.uint_to_t 0)  in
  let one   = (UInt32.uint_to_t 1)   in
  let two   = one @+ one in
  let three = one @+ two in
  let four  = two @+ two in
  let c = zero in
  let s0 = index state ((four*c) @+ zero ) in
  let s1 = index state ((four*c) @+ one  ) in
  let s2 = index state ((four*c) @+ two  ) in
  let s3 = index state ((four*c) @+ three) in
  let w0 = index w ((four*round*nb) @+ (four*c) @+ zero ) in
  let w1 = index w ((four*round*nb) @+ (four*c) @+ one  ) in
  let w2 = index w ((four*round*nb) @+ (four*c) @+ two  ) in
  let w3 = index w ((four*round*nb) @+ (four*c) @+ three) in
  upd state ((four*c) @+ zero ) (s0 ^^ w0);
  upd state ((four*c) @+ one  ) (s1 ^^ w1);
  upd state ((four*c) @+ two  ) (s2 ^^ w2);
  upd state ((four*c) @+ three) (s3 ^^ w3);
  let c = one in
  let s0 = index state ((four*c) @+ zero ) in
  let s1 = index state ((four*c) @+ one  ) in
  let s2 = index state ((four*c) @+ two  ) in
  let s3 = index state ((four*c) @+ three) in
  let w0 = index w ((four*round*nb) @+ (four*c) @+ zero ) in
  let w1 = index w ((four*round*nb) @+ (four*c) @+ one  ) in
  let w2 = index w ((four*round*nb) @+ (four*c) @+ two  ) in
  let w3 = index w ((four*round*nb) @+ (four*c) @+ three) in
  upd state ((four*c) @+ zero ) (s0 ^^ w0);
  upd state ((four*c) @+ one  ) (s1 ^^ w1);
  upd state ((four*c) @+ two  ) (s2 ^^ w2);
  upd state ((four*c) @+ three) (s3 ^^ w3);
  let c = two in
  let s0 = index state ((four*c) @+ zero ) in
  let s1 = index state ((four*c) @+ one  ) in
  let s2 = index state ((four*c) @+ two  ) in
  let s3 = index state ((four*c) @+ three) in
  let w0 = index w ((four*round*nb) @+ (four*c) @+ zero ) in
  let w1 = index w ((four*round*nb) @+ (four*c) @+ one  ) in
  let w2 = index w ((four*round*nb) @+ (four*c) @+ two  ) in
  let w3 = index w ((four*round*nb) @+ (four*c) @+ three) in
  upd state ((four*c) @+ zero ) (s0 ^^ w0);
  upd state ((four*c) @+ one  ) (s1 ^^ w1);
  upd state ((four*c) @+ two  ) (s2 ^^ w2);
  upd state ((four*c) @+ three) (s3 ^^ w3);
  let c = three in
  let s0 = index state ((four*c) @+ zero ) in
  let s1 = index state ((four*c) @+ one  ) in
  let s2 = index state ((four*c) @+ two  ) in
  let s3 = index state ((four*c) @+ three) in
  let w0 = index w ((four*round*nb) @+ (four*c) @+ zero ) in
  let w1 = index w ((four*round*nb) @+ (four*c) @+ one  ) in
  let w2 = index w ((four*round*nb) @+ (four*c) @+ two  ) in
  let w3 = index w ((four*round*nb) @+ (four*c) @+ three) in
  upd state ((four*c) @+ zero ) (s0 ^^ w0);
  upd state ((four*c) @+ one  ) (s1 ^^ w1);
  upd state ((four*c) @+ two  ) (s2 ^^ w2);
  upd state ((four*c) @+ three) (s3 ^^ w3);
  ()

val cipher_loop: state:suint8s -> w:suint8s -> suint8s -> round:uint32 -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rec cipher_loop state w sbox round = 
  if UInt32.eq round (UInt32.uint_to_t 14) then ()
  else begin
    subBytes_sbox state sbox;
    shiftRows state;
    mixColumns state;
    addRoundKey state w round; 
    cipher_loop state w sbox (round @+ (UInt32.uint_to_t 1))
  end

(* val cipher: out:suint8s{length out = Prims.op_Multiply 4 nb} -> input:suint8s{length input = 4*nb} -> w:suint8s{length w = 4 * (nr+1)} -> sbox:suint8s{length sbox = 256} -> STL unit *)
(*   (requires (fun h -> True)) *)
(*   (ensures (fun h0 _ h1 -> True)) *)
val cipher: out:suint8s -> input:suint8s -> w:suint8s -> sbox:suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let cipher out input w sbox =
  push_frame ();
  let state = create SInt.UInt8.zero ((UInt32.uint_to_t 4)*nb) in
  blit input (UInt32.uint_to_t 0) state (UInt32.uint_to_t 0) ((UInt32.uint_to_t 4)*nb);
  addRoundKey state w (UInt32.uint_to_t 0);
  cipher_loop state w sbox (UInt32.uint_to_t 1);
  subBytes_sbox state sbox;
  shiftRows state;
  addRoundKey state w nr;
  blit state (UInt32.uint_to_t 0) out (UInt32.uint_to_t 0) ((UInt32.uint_to_t 4)*nb);
  pop_frame ()

val rotWord: word:suint8s{length word = 4} -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rotWord word =
  let zero  = (UInt32.uint_to_t 0) in
  let one   = (UInt32.uint_to_t 1) in
  let two   = one @+ one in
  let three = one @+ two in
  let w0 = index word zero  in
  let w1 = index word one   in
  let w2 = index word two   in
  let w3 = index word three in
  upd word zero  w1;
  upd word one   w2;
  upd word two   w3;
  upd word three w0

val subWord: word:suint8s{length word = 4} -> sbox:suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let subWord word sbox =
  let zero  = (UInt32.uint_to_t 0) in
  let one   = (UInt32.uint_to_t 1) in
  let two   = one @+ one in
  let three = one @+ two in
  let w0 = index word zero in
  let w1 = index word one in
  let w2 = index word two in
  let w3 = index word three in
  upd word zero  (access sbox w0);
  upd word one   (access sbox w1);
  upd word two   (access sbox w2);
  upd word three (access sbox w3)

(* TODO: use table ? *)
val rcon: uint32 -> suint8 -> Tot suint8
let rec rcon i tmp =
  if UInt32.eq i (UInt32.uint_to_t 1) then tmp
  else begin
    let tmp = multiply (of_int 0x2) tmp in    
    rcon (i @- (UInt32.uint_to_t 1)) tmp
  end

let op_At_Slash = UInt32.div
let op_At_Percent = UInt32.rem

val keyExpansion_aux: suint8s -> suint8s -> suint8s -> suint8s -> uint32 -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rec keyExpansion_aux key w temp sbox i =
  if UInt32.eq i (UInt32.uint_to_t 240) then ()
  else begin
    let zero  = (UInt32.uint_to_t 0) in
    let one   = (UInt32.uint_to_t 1) in
    let two   = one @+ one in
    let three = one @+ two in
    let four  = two @+ two in
    blit w (i @- four) temp zero four;
    if UInt32.eq ((UInt32.div i four) @% nk) zero then (
      rotWord temp;
      subWord temp sbox;
      upd temp (UInt32.uint_to_t 0) (index temp zero ^^ rcon ((i @/ four) @/ nk) SInt.UInt8.one) 
    ) else if (UInt32.eq ((i @/ four) @% nk) four) then (
      subWord temp sbox
    );
    let w0 = index w (i @+ zero  @- (four*nk)) in
    let w1 = index w (i @+ one   @- (four*nk)) in
    let w2 = index w (i @+ two   @- (four*nk)) in
    let w3 = index w (i @+ three @- (four*nk)) in
    let t0 = index temp zero  in
    let t1 = index temp one   in
    let t2 = index temp two   in
    let t3 = index temp three in
    upd w (i @+ zero ) (t0 ^^ w0);
    upd w (i @+ one  ) (t1 ^^ w1);
    upd w (i @+ two  ) (t2 ^^ w2);
    upd w (i @+ three) (t3 ^^ w3);
    keyExpansion_aux key w temp sbox (i @+ UInt32.uint_to_t 4)
  end
    
(* val keyExpansion: key:suint8s{length key = 4 * nk} -> w:suint8s{length w = 4 * (nb * (nr+1))} -> sbox:suint8s -> St unit *)
val keyExpansion: key:suint8s -> w:suint8s -> sbox:suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let keyExpansion key w sbox =
  push_frame();
  let temp = create zero (UInt32.uint_to_t 4) in
  blit key (UInt32.uint_to_t 0) w (UInt32.uint_to_t 0) ((UInt32.uint_to_t 4)*nk);
  let i = (UInt32.uint_to_t 4) * nk in
  keyExpansion_aux key w temp sbox i;
  pop_frame()

val invShiftRows: state:suint8s{length state = 16} -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let invShiftRows state =
  let zero  = (UInt32.uint_to_t 0) in
  let one   = (UInt32.uint_to_t 1) in
  let two   = one @+ one in
  let three = one @+ two in
  let four  = two @+ two in
  let eight  = four @+ four in
  let twelve = four @+ eight in
  let i = three in
  let tmp = index state i in
  upd state i           (index state (i@+four)); 
  upd state (i@+four)   (index state (i@+eight)); 
  upd state (i@+eight)  (index state (i@+twelve)); 
  upd state (i@+twelve) tmp;
  let i = two in
  let tmp = index state i in
  upd state i           (index state (i@+eight)); 
  upd state (i@+eight)  tmp; 
  let tmp = index state (i@+four) in
  upd state (i@+four)   (index state (i@+twelve)); 
  upd state (i@+twelve) tmp;
  let i = one in
  let tmp = index state i in
  upd state i           (index state (i@+twelve)); 
  upd state (i@+twelve) (index state (i@+eight));
  upd state (i@+eight)  (index state (i@+four)); 
  upd state (i@+four)   tmp; 
  ()

val invSubBytes_aux_sbox: state:suint8s -> sbox:suint8s -> ctr:uint32 -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rec invSubBytes_aux_sbox state sbox ctr =
  if UInt32.eq ctr (UInt32.uint_to_t 16) then () 
  else begin 
    let si = index state ctr in
    let si' = access sbox si in
    upd state ctr si';
    invSubBytes_aux_sbox state sbox (ctr@+(UInt32.uint_to_t 1))
  end

val invSubBytes_sbox: state:suint8s -> suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let invSubBytes_sbox state sbox = 
  invSubBytes_aux_sbox state sbox (UInt32.uint_to_t 0)
       
val invMixColumns: suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let invMixColumns state = 
  let zero  = (UInt32.uint_to_t 0) in
  let one   = (UInt32.uint_to_t 1) in
  let two   = one @+ one in
  let three = one @+ two in
  let four  = two @+ two in
  let c = zero in
  let s0 = index state (zero  @+(four * c)) in
  let s1 = index state (one   @+(four * c)) in
  let s2 = index state (two   @+(four * c)) in
  let s3 = index state (three @+(four * c)) in
  upd state ((four*c) @+ zero) (multiply (of_int 0xe) s0 ^^ multiply (of_int 0xb) s1
  	       ^^ multiply (of_int 0xd) s2 ^^ multiply (of_int 0x9) s3);
  upd state ((four*c) @+ one) (multiply (of_int 0xe) s1 ^^ multiply (of_int 0xb) s2
  	       ^^ multiply (of_int 0xd) s3 ^^ multiply (of_int 0x9) s0);
  upd state ((four*c) @+ two) (multiply (of_int 0xe) s2 ^^ multiply (of_int 0xb) s3
  	       ^^ multiply (of_int 0xd) s0 ^^ multiply (of_int 0x9) s1);
  upd state ((four*c) @+ three) (multiply (of_int 0xe) s3 ^^ multiply (of_int 0xb) s0
  	       ^^ multiply (of_int 0xd) s1 ^^ multiply (of_int 0x9) s2); 
  let c = one in
  let s0 = index state (zero  @+ (four*c)) in
  let s1 = index state (one   @+ (four*c)) in
  let s2 = index state (two   @+ (four*c)) in
  let s3 = index state (three @+ (four*c)) in
  upd state ((four*c) @+ zero) (multiply (of_int 0xe) s0 ^^ multiply (of_int 0xb) s1
  	       ^^ multiply (of_int 0xd) s2 ^^ multiply (of_int 0x9) s3);
  upd state ((four*c) @+ one) (multiply (of_int 0xe) s1 ^^ multiply (of_int 0xb) s2
  	       ^^ multiply (of_int 0xd) s3 ^^ multiply (of_int 0x9) s0);
  upd state ((four*c) @+ two) (multiply (of_int 0xe) s2 ^^ multiply (of_int 0xb) s3
  	       ^^ multiply (of_int 0xd) s0 ^^ multiply (of_int 0x9) s1);
  upd state ((four*c) @+ three) (multiply (of_int 0xe) s3 ^^ multiply (of_int 0xb) s0
  	       ^^ multiply (of_int 0xd) s1 ^^ multiply (of_int 0x9) s2); 
  let c = two in
  let s0 = index state (zero  @+ (four*c)) in
  let s1 = index state (one   @+ (four*c)) in
  let s2 = index state (two   @+ (four*c)) in
  let s3 = index state (three @+ (four*c)) in
  upd state ((four*c) @+ zero) (multiply (of_int 0xe) s0 ^^ multiply (of_int 0xb) s1
  	       ^^ multiply (of_int 0xd) s2 ^^ multiply (of_int 0x9) s3);
  upd state ((four*c) @+ one) (multiply (of_int 0xe) s1 ^^ multiply (of_int 0xb) s2
  	       ^^ multiply (of_int 0xd) s3 ^^ multiply (of_int 0x9) s0);
  upd state ((four*c) @+ two) (multiply (of_int 0xe) s2 ^^ multiply (of_int 0xb) s3
  	       ^^ multiply (of_int 0xd) s0 ^^ multiply (of_int 0x9) s1);
  upd state ((four*c) @+ three) (multiply (of_int 0xe) s3 ^^ multiply (of_int 0xb) s0
  	       ^^ multiply (of_int 0xd) s1 ^^ multiply (of_int 0x9) s2); 
  let c = three in
  let s0 = index state (zero  @+ (four*c)) in
  let s1 = index state (one   @+ (four*c)) in
  let s2 = index state (two   @+ (four*c)) in
  let s3 = index state (three @+ (four*c)) in
  upd state ((four*c) @+ zero) (multiply (of_int 0xe) s0 ^^ multiply (of_int 0xb) s1
  	       ^^ multiply (of_int 0xd) s2 ^^ multiply (of_int 0x9) s3);
  upd state ((four*c) @+ one) (multiply (of_int 0xe) s1 ^^ multiply (of_int 0xb) s2
  	       ^^ multiply (of_int 0xd) s3 ^^ multiply (of_int 0x9) s0);
  upd state ((four*c) @+ two) (multiply (of_int 0xe) s2 ^^ multiply (of_int 0xb) s3
  	       ^^ multiply (of_int 0xd) s0 ^^ multiply (of_int 0x9) s1); 
  upd state ((four*c) @+ three) (multiply (of_int 0xe) s3 ^^ multiply (of_int 0xb) s0
  	       ^^ multiply (of_int 0xd) s1 ^^ multiply (of_int 0x9) s2);
  () (* JK: Without this "unit", the extraction gets into an infinite loop *)

val inv_cipher_loop: state:suint8s -> w:suint8s -> suint8s -> round:uint32 -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rec inv_cipher_loop state w sbox round = 
  if UInt32.eq round (UInt32.uint_to_t 0) then ()
  else begin
    invShiftRows state;
    invSubBytes_sbox state sbox;
    addRoundKey state w round;
    invMixColumns state;
    inv_cipher_loop state w sbox (round @- (UInt32.uint_to_t 1))
  end

(* val inv_cipher: out:suint8s{length out = 4 * nb} -> input:suint8s{length input = 4*nb} -> w:suint8s{length w = 4 * (nr+1)} -> sbox:suint8s{length sbox = 256} -> St unit *)
val inv_cipher: out:suint8s -> input:suint8s -> w:suint8s -> sbox:suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let inv_cipher out input w sbox =
  push_frame ();
  let state = create SInt.UInt8.zero (UInt32.uint_to_t 4 * nb) in
  blit input (UInt32.uint_to_t 0) state (UInt32.uint_to_t 0) (UInt32.uint_to_t 4 * nb);
  addRoundKey state w nr;
  inv_cipher_loop state w sbox (UInt32.uint_to_t 13);
  invShiftRows state;
  invSubBytes_sbox state sbox;
  addRoundKey state w (UInt32.uint_to_t 0);
  blit state (UInt32.uint_to_t 0) out (UInt32.uint_to_t 0) (UInt32.uint_to_t 4 * nb);
  pop_frame ()
  
