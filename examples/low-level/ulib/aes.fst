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
type uint32 = UInt.UInt32.uint32
type suint8s = buffer suint8

// Parameters for AES-256 
let nk = UInt.UInt32.of_int 8
let nb = UInt.UInt32.of_int 4
let nr = UInt.UInt32.of_int 14

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
  upd sbox (UInt.UInt32.of_int 0   ) (SInt.UInt8.of_int 0x63); upd sbox (UInt.UInt32.of_int 1   ) (SInt.UInt8.of_int 0x7c); upd sbox (UInt.UInt32.of_int 2   ) (SInt.UInt8.of_int 0x77); upd sbox (UInt.UInt32.of_int 3   ) (SInt.UInt8.of_int 0x7b); 
  upd sbox (UInt.UInt32.of_int 4   ) (SInt.UInt8.of_int 0xf2); upd sbox (UInt.UInt32.of_int 5   ) (SInt.UInt8.of_int 0x6b); upd sbox (UInt.UInt32.of_int 6   ) (SInt.UInt8.of_int 0x6f); upd sbox (UInt.UInt32.of_int 7   ) (SInt.UInt8.of_int 0xc5); 
  upd sbox (UInt.UInt32.of_int 8   ) (SInt.UInt8.of_int 0x30); upd sbox (UInt.UInt32.of_int 9   ) (SInt.UInt8.of_int 0x01); upd sbox (UInt.UInt32.of_int 10  ) (SInt.UInt8.of_int 0x67); upd sbox (UInt.UInt32.of_int 11  ) (SInt.UInt8.of_int 0x2b); 
  upd sbox (UInt.UInt32.of_int 12  ) (SInt.UInt8.of_int 0xfe); upd sbox (UInt.UInt32.of_int 13  ) (SInt.UInt8.of_int 0xd7); upd sbox (UInt.UInt32.of_int 14  ) (SInt.UInt8.of_int 0xab); upd sbox (UInt.UInt32.of_int 15  ) (SInt.UInt8.of_int 0x76); 
  upd sbox (UInt.UInt32.of_int 16  ) (SInt.UInt8.of_int 0xca); upd sbox (UInt.UInt32.of_int 17  ) (SInt.UInt8.of_int 0x82); upd sbox (UInt.UInt32.of_int 18  ) (SInt.UInt8.of_int 0xc9); upd sbox (UInt.UInt32.of_int 19  ) (SInt.UInt8.of_int 0x7d); 
  upd sbox (UInt.UInt32.of_int 20  ) (SInt.UInt8.of_int 0xfa); upd sbox (UInt.UInt32.of_int 21  ) (SInt.UInt8.of_int 0x59); upd sbox (UInt.UInt32.of_int 22  ) (SInt.UInt8.of_int 0x47); upd sbox (UInt.UInt32.of_int 23  ) (SInt.UInt8.of_int 0xf0); 
  upd sbox (UInt.UInt32.of_int 24  ) (SInt.UInt8.of_int 0xad); upd sbox (UInt.UInt32.of_int 25  ) (SInt.UInt8.of_int 0xd4); upd sbox (UInt.UInt32.of_int 26  ) (SInt.UInt8.of_int 0xa2); upd sbox (UInt.UInt32.of_int 27  ) (SInt.UInt8.of_int 0xaf); 
  upd sbox (UInt.UInt32.of_int 28  ) (SInt.UInt8.of_int 0x9c); upd sbox (UInt.UInt32.of_int 29  ) (SInt.UInt8.of_int 0xa4); upd sbox (UInt.UInt32.of_int 30  ) (SInt.UInt8.of_int 0x72); upd sbox (UInt.UInt32.of_int 31  ) (SInt.UInt8.of_int 0xc0); 
  upd sbox (UInt.UInt32.of_int 32  ) (SInt.UInt8.of_int 0xb7); upd sbox (UInt.UInt32.of_int 33  ) (SInt.UInt8.of_int 0xfd); upd sbox (UInt.UInt32.of_int 34  ) (SInt.UInt8.of_int 0x93); upd sbox (UInt.UInt32.of_int 35  ) (SInt.UInt8.of_int 0x26); 
  upd sbox (UInt.UInt32.of_int 36  ) (SInt.UInt8.of_int 0x36); upd sbox (UInt.UInt32.of_int 37  ) (SInt.UInt8.of_int 0x3f); upd sbox (UInt.UInt32.of_int 38  ) (SInt.UInt8.of_int 0xf7); upd sbox (UInt.UInt32.of_int 39  ) (SInt.UInt8.of_int 0xcc); 
  upd sbox (UInt.UInt32.of_int 40  ) (SInt.UInt8.of_int 0x34); upd sbox (UInt.UInt32.of_int 41  ) (SInt.UInt8.of_int 0xa5); upd sbox (UInt.UInt32.of_int 42  ) (SInt.UInt8.of_int 0xe5); upd sbox (UInt.UInt32.of_int 43  ) (SInt.UInt8.of_int 0xf1); 
  upd sbox (UInt.UInt32.of_int 44  ) (SInt.UInt8.of_int 0x71); upd sbox (UInt.UInt32.of_int 45  ) (SInt.UInt8.of_int 0xd8); upd sbox (UInt.UInt32.of_int 46  ) (SInt.UInt8.of_int 0x31); upd sbox (UInt.UInt32.of_int 47  ) (SInt.UInt8.of_int 0x15); 
  upd sbox (UInt.UInt32.of_int 48  ) (SInt.UInt8.of_int 0x04); upd sbox (UInt.UInt32.of_int 49  ) (SInt.UInt8.of_int 0xc7); upd sbox (UInt.UInt32.of_int 50  ) (SInt.UInt8.of_int 0x23); upd sbox (UInt.UInt32.of_int 51  ) (SInt.UInt8.of_int 0xc3); 
  upd sbox (UInt.UInt32.of_int 52  ) (SInt.UInt8.of_int 0x18); upd sbox (UInt.UInt32.of_int 53  ) (SInt.UInt8.of_int 0x96); upd sbox (UInt.UInt32.of_int 54  ) (SInt.UInt8.of_int 0x05); upd sbox (UInt.UInt32.of_int 55  ) (SInt.UInt8.of_int 0x9a); 
  upd sbox (UInt.UInt32.of_int 56  ) (SInt.UInt8.of_int 0x07); upd sbox (UInt.UInt32.of_int 57  ) (SInt.UInt8.of_int 0x12); upd sbox (UInt.UInt32.of_int 58  ) (SInt.UInt8.of_int 0x80); upd sbox (UInt.UInt32.of_int 59  ) (SInt.UInt8.of_int 0xe2); 
  upd sbox (UInt.UInt32.of_int 60  ) (SInt.UInt8.of_int 0xeb); upd sbox (UInt.UInt32.of_int 61  ) (SInt.UInt8.of_int 0x27); upd sbox (UInt.UInt32.of_int 62  ) (SInt.UInt8.of_int 0xb2); upd sbox (UInt.UInt32.of_int 63  ) (SInt.UInt8.of_int 0x75); 
  upd sbox (UInt.UInt32.of_int 64  ) (SInt.UInt8.of_int 0x09); upd sbox (UInt.UInt32.of_int 65  ) (SInt.UInt8.of_int 0x83); upd sbox (UInt.UInt32.of_int 66  ) (SInt.UInt8.of_int 0x2c); upd sbox (UInt.UInt32.of_int 67  ) (SInt.UInt8.of_int 0x1a); 
  upd sbox (UInt.UInt32.of_int 68  ) (SInt.UInt8.of_int 0x1b); upd sbox (UInt.UInt32.of_int 69  ) (SInt.UInt8.of_int 0x6e); upd sbox (UInt.UInt32.of_int 70  ) (SInt.UInt8.of_int 0x5a); upd sbox (UInt.UInt32.of_int 71  ) (SInt.UInt8.of_int 0xa0); 
  upd sbox (UInt.UInt32.of_int 72  ) (SInt.UInt8.of_int 0x52); upd sbox (UInt.UInt32.of_int 73  ) (SInt.UInt8.of_int 0x3b); upd sbox (UInt.UInt32.of_int 74  ) (SInt.UInt8.of_int 0xd6); upd sbox (UInt.UInt32.of_int 75  ) (SInt.UInt8.of_int 0xb3); 
  upd sbox (UInt.UInt32.of_int 76  ) (SInt.UInt8.of_int 0x29); upd sbox (UInt.UInt32.of_int 77  ) (SInt.UInt8.of_int 0xe3); upd sbox (UInt.UInt32.of_int 78  ) (SInt.UInt8.of_int 0x2f); upd sbox (UInt.UInt32.of_int 79  ) (SInt.UInt8.of_int 0x84); 
  upd sbox (UInt.UInt32.of_int 80  ) (SInt.UInt8.of_int 0x53); upd sbox (UInt.UInt32.of_int 81  ) (SInt.UInt8.of_int 0xd1); upd sbox (UInt.UInt32.of_int 82  ) (SInt.UInt8.of_int 0x00); upd sbox (UInt.UInt32.of_int 83  ) (SInt.UInt8.of_int 0xed); 
  upd sbox (UInt.UInt32.of_int 84  ) (SInt.UInt8.of_int 0x20); upd sbox (UInt.UInt32.of_int 85  ) (SInt.UInt8.of_int 0xfc); upd sbox (UInt.UInt32.of_int 86  ) (SInt.UInt8.of_int 0xb1); upd sbox (UInt.UInt32.of_int 87  ) (SInt.UInt8.of_int 0x5b); 
  upd sbox (UInt.UInt32.of_int 88  ) (SInt.UInt8.of_int 0x6a); upd sbox (UInt.UInt32.of_int 89  ) (SInt.UInt8.of_int 0xcb); upd sbox (UInt.UInt32.of_int 90  ) (SInt.UInt8.of_int 0xbe); upd sbox (UInt.UInt32.of_int 91  ) (SInt.UInt8.of_int 0x39); 
  upd sbox (UInt.UInt32.of_int 92  ) (SInt.UInt8.of_int 0x4a); upd sbox (UInt.UInt32.of_int 93  ) (SInt.UInt8.of_int 0x4c); upd sbox (UInt.UInt32.of_int 94  ) (SInt.UInt8.of_int 0x58); upd sbox (UInt.UInt32.of_int 95  ) (SInt.UInt8.of_int 0xcf); 
  upd sbox (UInt.UInt32.of_int 96  ) (SInt.UInt8.of_int 0xd0); upd sbox (UInt.UInt32.of_int 97  ) (SInt.UInt8.of_int 0xef); upd sbox (UInt.UInt32.of_int 98  ) (SInt.UInt8.of_int 0xaa); upd sbox (UInt.UInt32.of_int 99  ) (SInt.UInt8.of_int 0xfb); 
  upd sbox (UInt.UInt32.of_int 100 ) (SInt.UInt8.of_int 0x43); upd sbox (UInt.UInt32.of_int 101 ) (SInt.UInt8.of_int 0x4d); upd sbox (UInt.UInt32.of_int 102 ) (SInt.UInt8.of_int 0x33); upd sbox (UInt.UInt32.of_int 103 ) (SInt.UInt8.of_int 0x85); 
  upd sbox (UInt.UInt32.of_int 104 ) (SInt.UInt8.of_int 0x45); upd sbox (UInt.UInt32.of_int 105 ) (SInt.UInt8.of_int 0xf9); upd sbox (UInt.UInt32.of_int 106 ) (SInt.UInt8.of_int 0x02); upd sbox (UInt.UInt32.of_int 107 ) (SInt.UInt8.of_int 0x7f); 
  upd sbox (UInt.UInt32.of_int 108 ) (SInt.UInt8.of_int 0x50); upd sbox (UInt.UInt32.of_int 109 ) (SInt.UInt8.of_int 0x3c); upd sbox (UInt.UInt32.of_int 110 ) (SInt.UInt8.of_int 0x9f); upd sbox (UInt.UInt32.of_int 111 ) (SInt.UInt8.of_int 0xa8); 
  upd sbox (UInt.UInt32.of_int 112 ) (SInt.UInt8.of_int 0x51); upd sbox (UInt.UInt32.of_int 113 ) (SInt.UInt8.of_int 0xa3); upd sbox (UInt.UInt32.of_int 114 ) (SInt.UInt8.of_int 0x40); upd sbox (UInt.UInt32.of_int 115 ) (SInt.UInt8.of_int 0x8f); 
  upd sbox (UInt.UInt32.of_int 116 ) (SInt.UInt8.of_int 0x92); upd sbox (UInt.UInt32.of_int 117 ) (SInt.UInt8.of_int 0x9d); upd sbox (UInt.UInt32.of_int 118 ) (SInt.UInt8.of_int 0x38); upd sbox (UInt.UInt32.of_int 119 ) (SInt.UInt8.of_int 0xf5); 
  upd sbox (UInt.UInt32.of_int 120 ) (SInt.UInt8.of_int 0xbc); upd sbox (UInt.UInt32.of_int 121 ) (SInt.UInt8.of_int 0xb6); upd sbox (UInt.UInt32.of_int 122 ) (SInt.UInt8.of_int 0xda); upd sbox (UInt.UInt32.of_int 123 ) (SInt.UInt8.of_int 0x21); 
  upd sbox (UInt.UInt32.of_int 124 ) (SInt.UInt8.of_int 0x10); upd sbox (UInt.UInt32.of_int 125 ) (SInt.UInt8.of_int 0xff); upd sbox (UInt.UInt32.of_int 126 ) (SInt.UInt8.of_int 0xf3); upd sbox (UInt.UInt32.of_int 127 ) (SInt.UInt8.of_int 0xd2); 
  upd sbox (UInt.UInt32.of_int 128 ) (SInt.UInt8.of_int 0xcd); upd sbox (UInt.UInt32.of_int 129 ) (SInt.UInt8.of_int 0x0c); upd sbox (UInt.UInt32.of_int 130 ) (SInt.UInt8.of_int 0x13); upd sbox (UInt.UInt32.of_int 131 ) (SInt.UInt8.of_int 0xec); 
  upd sbox (UInt.UInt32.of_int 132 ) (SInt.UInt8.of_int 0x5f); upd sbox (UInt.UInt32.of_int 133 ) (SInt.UInt8.of_int 0x97); upd sbox (UInt.UInt32.of_int 134 ) (SInt.UInt8.of_int 0x44); upd sbox (UInt.UInt32.of_int 135 ) (SInt.UInt8.of_int 0x17); 
  upd sbox (UInt.UInt32.of_int 136 ) (SInt.UInt8.of_int 0xc4); upd sbox (UInt.UInt32.of_int 137 ) (SInt.UInt8.of_int 0xa7); upd sbox (UInt.UInt32.of_int 138 ) (SInt.UInt8.of_int 0x7e); upd sbox (UInt.UInt32.of_int 139 ) (SInt.UInt8.of_int 0x3d); 
  upd sbox (UInt.UInt32.of_int 140 ) (SInt.UInt8.of_int 0x64); upd sbox (UInt.UInt32.of_int 141 ) (SInt.UInt8.of_int 0x5d); upd sbox (UInt.UInt32.of_int 142 ) (SInt.UInt8.of_int 0x19); upd sbox (UInt.UInt32.of_int 143 ) (SInt.UInt8.of_int 0x73); 
  upd sbox (UInt.UInt32.of_int 144 ) (SInt.UInt8.of_int 0x60); upd sbox (UInt.UInt32.of_int 145 ) (SInt.UInt8.of_int 0x81); upd sbox (UInt.UInt32.of_int 146 ) (SInt.UInt8.of_int 0x4f); upd sbox (UInt.UInt32.of_int 147 ) (SInt.UInt8.of_int 0xdc); 
  upd sbox (UInt.UInt32.of_int 148 ) (SInt.UInt8.of_int 0x22); upd sbox (UInt.UInt32.of_int 149 ) (SInt.UInt8.of_int 0x2a); upd sbox (UInt.UInt32.of_int 150 ) (SInt.UInt8.of_int 0x90); upd sbox (UInt.UInt32.of_int 151 ) (SInt.UInt8.of_int 0x88); 
  upd sbox (UInt.UInt32.of_int 152 ) (SInt.UInt8.of_int 0x46); upd sbox (UInt.UInt32.of_int 153 ) (SInt.UInt8.of_int 0xee); upd sbox (UInt.UInt32.of_int 154 ) (SInt.UInt8.of_int 0xb8); upd sbox (UInt.UInt32.of_int 155 ) (SInt.UInt8.of_int 0x14); 
  upd sbox (UInt.UInt32.of_int 156 ) (SInt.UInt8.of_int 0xde); upd sbox (UInt.UInt32.of_int 157 ) (SInt.UInt8.of_int 0x5e); upd sbox (UInt.UInt32.of_int 158 ) (SInt.UInt8.of_int 0x0b); upd sbox (UInt.UInt32.of_int 159 ) (SInt.UInt8.of_int 0xdb); 
  upd sbox (UInt.UInt32.of_int 160 ) (SInt.UInt8.of_int 0xe0); upd sbox (UInt.UInt32.of_int 161 ) (SInt.UInt8.of_int 0x32); upd sbox (UInt.UInt32.of_int 162 ) (SInt.UInt8.of_int 0x3a); upd sbox (UInt.UInt32.of_int 163 ) (SInt.UInt8.of_int 0x0a); 
  upd sbox (UInt.UInt32.of_int 164 ) (SInt.UInt8.of_int 0x49); upd sbox (UInt.UInt32.of_int 165 ) (SInt.UInt8.of_int 0x06); upd sbox (UInt.UInt32.of_int 166 ) (SInt.UInt8.of_int 0x24); upd sbox (UInt.UInt32.of_int 167 ) (SInt.UInt8.of_int 0x5c); 
  upd sbox (UInt.UInt32.of_int 168 ) (SInt.UInt8.of_int 0xc2); upd sbox (UInt.UInt32.of_int 169 ) (SInt.UInt8.of_int 0xd3); upd sbox (UInt.UInt32.of_int 170 ) (SInt.UInt8.of_int 0xac); upd sbox (UInt.UInt32.of_int 171 ) (SInt.UInt8.of_int 0x62); 
  upd sbox (UInt.UInt32.of_int 172 ) (SInt.UInt8.of_int 0x91); upd sbox (UInt.UInt32.of_int 173 ) (SInt.UInt8.of_int 0x95); upd sbox (UInt.UInt32.of_int 174 ) (SInt.UInt8.of_int 0xe4); upd sbox (UInt.UInt32.of_int 175 ) (SInt.UInt8.of_int 0x79); 
  upd sbox (UInt.UInt32.of_int 176 ) (SInt.UInt8.of_int 0xe7); upd sbox (UInt.UInt32.of_int 177 ) (SInt.UInt8.of_int 0xc8); upd sbox (UInt.UInt32.of_int 178 ) (SInt.UInt8.of_int 0x37); upd sbox (UInt.UInt32.of_int 179 ) (SInt.UInt8.of_int 0x6d); 
  upd sbox (UInt.UInt32.of_int 180 ) (SInt.UInt8.of_int 0x8d); upd sbox (UInt.UInt32.of_int 181 ) (SInt.UInt8.of_int 0xd5); upd sbox (UInt.UInt32.of_int 182 ) (SInt.UInt8.of_int 0x4e); upd sbox (UInt.UInt32.of_int 183 ) (SInt.UInt8.of_int 0xa9); 
  upd sbox (UInt.UInt32.of_int 184 ) (SInt.UInt8.of_int 0x6c); upd sbox (UInt.UInt32.of_int 185 ) (SInt.UInt8.of_int 0x56); upd sbox (UInt.UInt32.of_int 186 ) (SInt.UInt8.of_int 0xf4); upd sbox (UInt.UInt32.of_int 187 ) (SInt.UInt8.of_int 0xea); 
  upd sbox (UInt.UInt32.of_int 188 ) (SInt.UInt8.of_int 0x65); upd sbox (UInt.UInt32.of_int 189 ) (SInt.UInt8.of_int 0x7a); upd sbox (UInt.UInt32.of_int 190 ) (SInt.UInt8.of_int 0xae); upd sbox (UInt.UInt32.of_int 191 ) (SInt.UInt8.of_int 0x08); 
  upd sbox (UInt.UInt32.of_int 192 ) (SInt.UInt8.of_int 0xba); upd sbox (UInt.UInt32.of_int 193 ) (SInt.UInt8.of_int 0x78); upd sbox (UInt.UInt32.of_int 194 ) (SInt.UInt8.of_int 0x25); upd sbox (UInt.UInt32.of_int 195 ) (SInt.UInt8.of_int 0x2e); 
  upd sbox (UInt.UInt32.of_int 196 ) (SInt.UInt8.of_int 0x1c); upd sbox (UInt.UInt32.of_int 197 ) (SInt.UInt8.of_int 0xa6); upd sbox (UInt.UInt32.of_int 198 ) (SInt.UInt8.of_int 0xb4); upd sbox (UInt.UInt32.of_int 199 ) (SInt.UInt8.of_int 0xc6); 
  upd sbox (UInt.UInt32.of_int 200 ) (SInt.UInt8.of_int 0xe8); upd sbox (UInt.UInt32.of_int 201 ) (SInt.UInt8.of_int 0xdd); upd sbox (UInt.UInt32.of_int 202 ) (SInt.UInt8.of_int 0x74); upd sbox (UInt.UInt32.of_int 203 ) (SInt.UInt8.of_int 0x1f); 
  upd sbox (UInt.UInt32.of_int 204 ) (SInt.UInt8.of_int 0x4b); upd sbox (UInt.UInt32.of_int 205 ) (SInt.UInt8.of_int 0xbd); upd sbox (UInt.UInt32.of_int 206 ) (SInt.UInt8.of_int 0x8b); upd sbox (UInt.UInt32.of_int 207 ) (SInt.UInt8.of_int 0x8a); 
  upd sbox (UInt.UInt32.of_int 208 ) (SInt.UInt8.of_int 0x70); upd sbox (UInt.UInt32.of_int 209 ) (SInt.UInt8.of_int 0x3e); upd sbox (UInt.UInt32.of_int 210 ) (SInt.UInt8.of_int 0xb5); upd sbox (UInt.UInt32.of_int 211 ) (SInt.UInt8.of_int 0x66); 
  upd sbox (UInt.UInt32.of_int 212 ) (SInt.UInt8.of_int 0x48); upd sbox (UInt.UInt32.of_int 213 ) (SInt.UInt8.of_int 0x03); upd sbox (UInt.UInt32.of_int 214 ) (SInt.UInt8.of_int 0xf6); upd sbox (UInt.UInt32.of_int 215 ) (SInt.UInt8.of_int 0x0e); 
  upd sbox (UInt.UInt32.of_int 216 ) (SInt.UInt8.of_int 0x61); upd sbox (UInt.UInt32.of_int 217 ) (SInt.UInt8.of_int 0x35); upd sbox (UInt.UInt32.of_int 218 ) (SInt.UInt8.of_int 0x57); upd sbox (UInt.UInt32.of_int 219 ) (SInt.UInt8.of_int 0xb9); 
  upd sbox (UInt.UInt32.of_int 220 ) (SInt.UInt8.of_int 0x86); upd sbox (UInt.UInt32.of_int 221 ) (SInt.UInt8.of_int 0xc1); upd sbox (UInt.UInt32.of_int 222 ) (SInt.UInt8.of_int 0x1d); upd sbox (UInt.UInt32.of_int 223 ) (SInt.UInt8.of_int 0x9e); 
  upd sbox (UInt.UInt32.of_int 224 ) (SInt.UInt8.of_int 0xe1); upd sbox (UInt.UInt32.of_int 225 ) (SInt.UInt8.of_int 0xf8); upd sbox (UInt.UInt32.of_int 226 ) (SInt.UInt8.of_int 0x98); upd sbox (UInt.UInt32.of_int 227 ) (SInt.UInt8.of_int 0x11); 
  upd sbox (UInt.UInt32.of_int 228 ) (SInt.UInt8.of_int 0x69); upd sbox (UInt.UInt32.of_int 229 ) (SInt.UInt8.of_int 0xd9); upd sbox (UInt.UInt32.of_int 230 ) (SInt.UInt8.of_int 0x8e); upd sbox (UInt.UInt32.of_int 231 ) (SInt.UInt8.of_int 0x94); 
  upd sbox (UInt.UInt32.of_int 232 ) (SInt.UInt8.of_int 0x9b); upd sbox (UInt.UInt32.of_int 233 ) (SInt.UInt8.of_int 0x1e); upd sbox (UInt.UInt32.of_int 234 ) (SInt.UInt8.of_int 0x87); upd sbox (UInt.UInt32.of_int 235 ) (SInt.UInt8.of_int 0xe9); 
  upd sbox (UInt.UInt32.of_int 236 ) (SInt.UInt8.of_int 0xce); upd sbox (UInt.UInt32.of_int 237 ) (SInt.UInt8.of_int 0x55); upd sbox (UInt.UInt32.of_int 238 ) (SInt.UInt8.of_int 0x28); upd sbox (UInt.UInt32.of_int 239 ) (SInt.UInt8.of_int 0xdf); 
  upd sbox (UInt.UInt32.of_int 240 ) (SInt.UInt8.of_int 0x8c); upd sbox (UInt.UInt32.of_int 241 ) (SInt.UInt8.of_int 0xa1); upd sbox (UInt.UInt32.of_int 242 ) (SInt.UInt8.of_int 0x89); upd sbox (UInt.UInt32.of_int 243 ) (SInt.UInt8.of_int 0x0d); 
  upd sbox (UInt.UInt32.of_int 244 ) (SInt.UInt8.of_int 0xbf); upd sbox (UInt.UInt32.of_int 245 ) (SInt.UInt8.of_int 0xe6); upd sbox (UInt.UInt32.of_int 246 ) (SInt.UInt8.of_int 0x42); upd sbox (UInt.UInt32.of_int 247 ) (SInt.UInt8.of_int 0x68); 
  upd sbox (UInt.UInt32.of_int 248 ) (SInt.UInt8.of_int 0x41); upd sbox (UInt.UInt32.of_int 249 ) (SInt.UInt8.of_int 0x99); upd sbox (UInt.UInt32.of_int 250 ) (SInt.UInt8.of_int 0x2d); upd sbox (UInt.UInt32.of_int 251 ) (SInt.UInt8.of_int 0x0f); 
  upd sbox (UInt.UInt32.of_int 252 ) (SInt.UInt8.of_int 0xb0); upd sbox (UInt.UInt32.of_int 253 ) (SInt.UInt8.of_int 0x54); upd sbox (UInt.UInt32.of_int 254 ) (SInt.UInt8.of_int 0xbb); upd sbox (UInt.UInt32.of_int 255 ) (SInt.UInt8.of_int 0x16)

val mk_inv_sbox: sbox:suint8s{length sbox = 64} -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let mk_inv_sbox sbox = 
  upd sbox (UInt.UInt32.of_int 0   ) (SInt.UInt8.of_int 0x52); upd sbox (UInt.UInt32.of_int 1   ) (SInt.UInt8.of_int 0x09); upd sbox (UInt.UInt32.of_int 2   ) (SInt.UInt8.of_int 0x6a); upd sbox (UInt.UInt32.of_int 3   ) (SInt.UInt8.of_int 0xd5); 
  upd sbox (UInt.UInt32.of_int 4   ) (SInt.UInt8.of_int 0x30); upd sbox (UInt.UInt32.of_int 5   ) (SInt.UInt8.of_int 0x36); upd sbox (UInt.UInt32.of_int 6   ) (SInt.UInt8.of_int 0xa5); upd sbox (UInt.UInt32.of_int 7   ) (SInt.UInt8.of_int 0x38); 
  upd sbox (UInt.UInt32.of_int 8   ) (SInt.UInt8.of_int 0xbf); upd sbox (UInt.UInt32.of_int 9   ) (SInt.UInt8.of_int 0x40); upd sbox (UInt.UInt32.of_int 10  ) (SInt.UInt8.of_int 0xa3); upd sbox (UInt.UInt32.of_int 11  ) (SInt.UInt8.of_int 0x9e); 
  upd sbox (UInt.UInt32.of_int 12  ) (SInt.UInt8.of_int 0x81); upd sbox (UInt.UInt32.of_int 13  ) (SInt.UInt8.of_int 0xf3); upd sbox (UInt.UInt32.of_int 14  ) (SInt.UInt8.of_int 0xd7); upd sbox (UInt.UInt32.of_int 15  ) (SInt.UInt8.of_int 0xfb); 
  upd sbox (UInt.UInt32.of_int 16  ) (SInt.UInt8.of_int 0x7c); upd sbox (UInt.UInt32.of_int 17  ) (SInt.UInt8.of_int 0xe3); upd sbox (UInt.UInt32.of_int 18  ) (SInt.UInt8.of_int 0x39); upd sbox (UInt.UInt32.of_int 19  ) (SInt.UInt8.of_int 0x82); 
  upd sbox (UInt.UInt32.of_int 20  ) (SInt.UInt8.of_int 0x9b); upd sbox (UInt.UInt32.of_int 21  ) (SInt.UInt8.of_int 0x2f); upd sbox (UInt.UInt32.of_int 22  ) (SInt.UInt8.of_int 0xff); upd sbox (UInt.UInt32.of_int 23  ) (SInt.UInt8.of_int 0x87); 
  upd sbox (UInt.UInt32.of_int 24  ) (SInt.UInt8.of_int 0x34); upd sbox (UInt.UInt32.of_int 25  ) (SInt.UInt8.of_int 0x8e); upd sbox (UInt.UInt32.of_int 26  ) (SInt.UInt8.of_int 0x43); upd sbox (UInt.UInt32.of_int 27  ) (SInt.UInt8.of_int 0x44); 
  upd sbox (UInt.UInt32.of_int 28  ) (SInt.UInt8.of_int 0xc4); upd sbox (UInt.UInt32.of_int 29  ) (SInt.UInt8.of_int 0xde); upd sbox (UInt.UInt32.of_int 30  ) (SInt.UInt8.of_int 0xe9); upd sbox (UInt.UInt32.of_int 31  ) (SInt.UInt8.of_int 0xcb); 
  upd sbox (UInt.UInt32.of_int 32  ) (SInt.UInt8.of_int 0x54); upd sbox (UInt.UInt32.of_int 33  ) (SInt.UInt8.of_int 0x7b); upd sbox (UInt.UInt32.of_int 34  ) (SInt.UInt8.of_int 0x94); upd sbox (UInt.UInt32.of_int 35  ) (SInt.UInt8.of_int 0x32); 
  upd sbox (UInt.UInt32.of_int 36  ) (SInt.UInt8.of_int 0xa6); upd sbox (UInt.UInt32.of_int 37  ) (SInt.UInt8.of_int 0xc2); upd sbox (UInt.UInt32.of_int 38  ) (SInt.UInt8.of_int 0x23); upd sbox (UInt.UInt32.of_int 39  ) (SInt.UInt8.of_int 0x3d); 
  upd sbox (UInt.UInt32.of_int 40  ) (SInt.UInt8.of_int 0xee); upd sbox (UInt.UInt32.of_int 41  ) (SInt.UInt8.of_int 0x4c); upd sbox (UInt.UInt32.of_int 42  ) (SInt.UInt8.of_int 0x95); upd sbox (UInt.UInt32.of_int 43  ) (SInt.UInt8.of_int 0x0b); 
  upd sbox (UInt.UInt32.of_int 44  ) (SInt.UInt8.of_int 0x42); upd sbox (UInt.UInt32.of_int 45  ) (SInt.UInt8.of_int 0xfa); upd sbox (UInt.UInt32.of_int 46  ) (SInt.UInt8.of_int 0xc3); upd sbox (UInt.UInt32.of_int 47  ) (SInt.UInt8.of_int 0x4e); 
  upd sbox (UInt.UInt32.of_int 48  ) (SInt.UInt8.of_int 0x08); upd sbox (UInt.UInt32.of_int 49  ) (SInt.UInt8.of_int 0x2e); upd sbox (UInt.UInt32.of_int 50  ) (SInt.UInt8.of_int 0xa1); upd sbox (UInt.UInt32.of_int 51  ) (SInt.UInt8.of_int 0x66); 
  upd sbox (UInt.UInt32.of_int 52  ) (SInt.UInt8.of_int 0x28); upd sbox (UInt.UInt32.of_int 53  ) (SInt.UInt8.of_int 0xd9); upd sbox (UInt.UInt32.of_int 54  ) (SInt.UInt8.of_int 0x24); upd sbox (UInt.UInt32.of_int 55  ) (SInt.UInt8.of_int 0xb2); 
  upd sbox (UInt.UInt32.of_int 56  ) (SInt.UInt8.of_int 0x76); upd sbox (UInt.UInt32.of_int 57  ) (SInt.UInt8.of_int 0x5b); upd sbox (UInt.UInt32.of_int 58  ) (SInt.UInt8.of_int 0xa2); upd sbox (UInt.UInt32.of_int 59  ) (SInt.UInt8.of_int 0x49); 
  upd sbox (UInt.UInt32.of_int 60  ) (SInt.UInt8.of_int 0x6d); upd sbox (UInt.UInt32.of_int 61  ) (SInt.UInt8.of_int 0x8b); upd sbox (UInt.UInt32.of_int 62  ) (SInt.UInt8.of_int 0xd1); upd sbox (UInt.UInt32.of_int 63  ) (SInt.UInt8.of_int 0x25); 
  upd sbox (UInt.UInt32.of_int 64  ) (SInt.UInt8.of_int 0x72); upd sbox (UInt.UInt32.of_int 65  ) (SInt.UInt8.of_int 0xf8); upd sbox (UInt.UInt32.of_int 66  ) (SInt.UInt8.of_int 0xf6); upd sbox (UInt.UInt32.of_int 67  ) (SInt.UInt8.of_int 0x64); 
  upd sbox (UInt.UInt32.of_int 68  ) (SInt.UInt8.of_int 0x86); upd sbox (UInt.UInt32.of_int 69  ) (SInt.UInt8.of_int 0x68); upd sbox (UInt.UInt32.of_int 70  ) (SInt.UInt8.of_int 0x98); upd sbox (UInt.UInt32.of_int 71  ) (SInt.UInt8.of_int 0x16); 
  upd sbox (UInt.UInt32.of_int 72  ) (SInt.UInt8.of_int 0xd4); upd sbox (UInt.UInt32.of_int 73  ) (SInt.UInt8.of_int 0xa4); upd sbox (UInt.UInt32.of_int 74  ) (SInt.UInt8.of_int 0x5c); upd sbox (UInt.UInt32.of_int 75  ) (SInt.UInt8.of_int 0xcc); 
  upd sbox (UInt.UInt32.of_int 76  ) (SInt.UInt8.of_int 0x5d); upd sbox (UInt.UInt32.of_int 77  ) (SInt.UInt8.of_int 0x65); upd sbox (UInt.UInt32.of_int 78  ) (SInt.UInt8.of_int 0xb6); upd sbox (UInt.UInt32.of_int 79  ) (SInt.UInt8.of_int 0x92); 
  upd sbox (UInt.UInt32.of_int 80  ) (SInt.UInt8.of_int 0x6c); upd sbox (UInt.UInt32.of_int 81  ) (SInt.UInt8.of_int 0x70); upd sbox (UInt.UInt32.of_int 82  ) (SInt.UInt8.of_int 0x48); upd sbox (UInt.UInt32.of_int 83  ) (SInt.UInt8.of_int 0x50); 
  upd sbox (UInt.UInt32.of_int 84  ) (SInt.UInt8.of_int 0xfd); upd sbox (UInt.UInt32.of_int 85  ) (SInt.UInt8.of_int 0xed); upd sbox (UInt.UInt32.of_int 86  ) (SInt.UInt8.of_int 0xb9); upd sbox (UInt.UInt32.of_int 87  ) (SInt.UInt8.of_int 0xda); 
  upd sbox (UInt.UInt32.of_int 88  ) (SInt.UInt8.of_int 0x5e); upd sbox (UInt.UInt32.of_int 89  ) (SInt.UInt8.of_int 0x15); upd sbox (UInt.UInt32.of_int 90  ) (SInt.UInt8.of_int 0x46); upd sbox (UInt.UInt32.of_int 91  ) (SInt.UInt8.of_int 0x57); 
  upd sbox (UInt.UInt32.of_int 92  ) (SInt.UInt8.of_int 0xa7); upd sbox (UInt.UInt32.of_int 93  ) (SInt.UInt8.of_int 0x8d); upd sbox (UInt.UInt32.of_int 94  ) (SInt.UInt8.of_int 0x9d); upd sbox (UInt.UInt32.of_int 95  ) (SInt.UInt8.of_int 0x84); 
  upd sbox (UInt.UInt32.of_int 96  ) (SInt.UInt8.of_int 0x90); upd sbox (UInt.UInt32.of_int 97  ) (SInt.UInt8.of_int 0xd8); upd sbox (UInt.UInt32.of_int 98  ) (SInt.UInt8.of_int 0xab); upd sbox (UInt.UInt32.of_int 99  ) (SInt.UInt8.of_int 0x00); 
  upd sbox (UInt.UInt32.of_int 100 ) (SInt.UInt8.of_int 0x8c); upd sbox (UInt.UInt32.of_int 101 ) (SInt.UInt8.of_int 0xbc); upd sbox (UInt.UInt32.of_int 102 ) (SInt.UInt8.of_int 0xd3); upd sbox (UInt.UInt32.of_int 103 ) (SInt.UInt8.of_int 0x0a); 
  upd sbox (UInt.UInt32.of_int 104 ) (SInt.UInt8.of_int 0xf7); upd sbox (UInt.UInt32.of_int 105 ) (SInt.UInt8.of_int 0xe4); upd sbox (UInt.UInt32.of_int 106 ) (SInt.UInt8.of_int 0x58); upd sbox (UInt.UInt32.of_int 107 ) (SInt.UInt8.of_int 0x05); 
  upd sbox (UInt.UInt32.of_int 108 ) (SInt.UInt8.of_int 0xb8); upd sbox (UInt.UInt32.of_int 109 ) (SInt.UInt8.of_int 0xb3); upd sbox (UInt.UInt32.of_int 110 ) (SInt.UInt8.of_int 0x45); upd sbox (UInt.UInt32.of_int 111 ) (SInt.UInt8.of_int 0x06); 
  upd sbox (UInt.UInt32.of_int 112 ) (SInt.UInt8.of_int 0xd0); upd sbox (UInt.UInt32.of_int 113 ) (SInt.UInt8.of_int 0x2c); upd sbox (UInt.UInt32.of_int 114 ) (SInt.UInt8.of_int 0x1e); upd sbox (UInt.UInt32.of_int 115 ) (SInt.UInt8.of_int 0x8f); 
  upd sbox (UInt.UInt32.of_int 116 ) (SInt.UInt8.of_int 0xca); upd sbox (UInt.UInt32.of_int 117 ) (SInt.UInt8.of_int 0x3f); upd sbox (UInt.UInt32.of_int 118 ) (SInt.UInt8.of_int 0x0f); upd sbox (UInt.UInt32.of_int 119 ) (SInt.UInt8.of_int 0x02); 
  upd sbox (UInt.UInt32.of_int 120 ) (SInt.UInt8.of_int 0xc1); upd sbox (UInt.UInt32.of_int 121 ) (SInt.UInt8.of_int 0xaf); upd sbox (UInt.UInt32.of_int 122 ) (SInt.UInt8.of_int 0xbd); upd sbox (UInt.UInt32.of_int 123 ) (SInt.UInt8.of_int 0x03); 
  upd sbox (UInt.UInt32.of_int 124 ) (SInt.UInt8.of_int 0x01); upd sbox (UInt.UInt32.of_int 125 ) (SInt.UInt8.of_int 0x13); upd sbox (UInt.UInt32.of_int 126 ) (SInt.UInt8.of_int 0x8a); upd sbox (UInt.UInt32.of_int 127 ) (SInt.UInt8.of_int 0x6b); 
  upd sbox (UInt.UInt32.of_int 128 ) (SInt.UInt8.of_int 0x3a); upd sbox (UInt.UInt32.of_int 129 ) (SInt.UInt8.of_int 0x91); upd sbox (UInt.UInt32.of_int 130 ) (SInt.UInt8.of_int 0x11); upd sbox (UInt.UInt32.of_int 131 ) (SInt.UInt8.of_int 0x41); 
  upd sbox (UInt.UInt32.of_int 132 ) (SInt.UInt8.of_int 0x4f); upd sbox (UInt.UInt32.of_int 133 ) (SInt.UInt8.of_int 0x67); upd sbox (UInt.UInt32.of_int 134 ) (SInt.UInt8.of_int 0xdc); upd sbox (UInt.UInt32.of_int 135 ) (SInt.UInt8.of_int 0xea); 
  upd sbox (UInt.UInt32.of_int 136 ) (SInt.UInt8.of_int 0x97); upd sbox (UInt.UInt32.of_int 137 ) (SInt.UInt8.of_int 0xf2); upd sbox (UInt.UInt32.of_int 138 ) (SInt.UInt8.of_int 0xcf); upd sbox (UInt.UInt32.of_int 139 ) (SInt.UInt8.of_int 0xce); 
  upd sbox (UInt.UInt32.of_int 140 ) (SInt.UInt8.of_int 0xf0); upd sbox (UInt.UInt32.of_int 141 ) (SInt.UInt8.of_int 0xb4); upd sbox (UInt.UInt32.of_int 142 ) (SInt.UInt8.of_int 0xe6); upd sbox (UInt.UInt32.of_int 143 ) (SInt.UInt8.of_int 0x73); 
  upd sbox (UInt.UInt32.of_int 144 ) (SInt.UInt8.of_int 0x96); upd sbox (UInt.UInt32.of_int 145 ) (SInt.UInt8.of_int 0xac); upd sbox (UInt.UInt32.of_int 146 ) (SInt.UInt8.of_int 0x74); upd sbox (UInt.UInt32.of_int 147 ) (SInt.UInt8.of_int 0x22); 
  upd sbox (UInt.UInt32.of_int 148 ) (SInt.UInt8.of_int 0xe7); upd sbox (UInt.UInt32.of_int 149 ) (SInt.UInt8.of_int 0xad); upd sbox (UInt.UInt32.of_int 150 ) (SInt.UInt8.of_int 0x35); upd sbox (UInt.UInt32.of_int 151 ) (SInt.UInt8.of_int 0x85); 
  upd sbox (UInt.UInt32.of_int 152 ) (SInt.UInt8.of_int 0xe2); upd sbox (UInt.UInt32.of_int 153 ) (SInt.UInt8.of_int 0xf9); upd sbox (UInt.UInt32.of_int 154 ) (SInt.UInt8.of_int 0x37); upd sbox (UInt.UInt32.of_int 155 ) (SInt.UInt8.of_int 0xe8); 
  upd sbox (UInt.UInt32.of_int 156 ) (SInt.UInt8.of_int 0x1c); upd sbox (UInt.UInt32.of_int 157 ) (SInt.UInt8.of_int 0x75); upd sbox (UInt.UInt32.of_int 158 ) (SInt.UInt8.of_int 0xdf); upd sbox (UInt.UInt32.of_int 159 ) (SInt.UInt8.of_int 0x6e); 
  upd sbox (UInt.UInt32.of_int 160 ) (SInt.UInt8.of_int 0x47); upd sbox (UInt.UInt32.of_int 161 ) (SInt.UInt8.of_int 0xf1); upd sbox (UInt.UInt32.of_int 162 ) (SInt.UInt8.of_int 0x1a); upd sbox (UInt.UInt32.of_int 163 ) (SInt.UInt8.of_int 0x71); 
  upd sbox (UInt.UInt32.of_int 164 ) (SInt.UInt8.of_int 0x1d); upd sbox (UInt.UInt32.of_int 165 ) (SInt.UInt8.of_int 0x29); upd sbox (UInt.UInt32.of_int 166 ) (SInt.UInt8.of_int 0xc5); upd sbox (UInt.UInt32.of_int 167 ) (SInt.UInt8.of_int 0x89); 
  upd sbox (UInt.UInt32.of_int 168 ) (SInt.UInt8.of_int 0x6f); upd sbox (UInt.UInt32.of_int 169 ) (SInt.UInt8.of_int 0xb7); upd sbox (UInt.UInt32.of_int 170 ) (SInt.UInt8.of_int 0x62); upd sbox (UInt.UInt32.of_int 171 ) (SInt.UInt8.of_int 0x0e); 
  upd sbox (UInt.UInt32.of_int 172 ) (SInt.UInt8.of_int 0xaa); upd sbox (UInt.UInt32.of_int 173 ) (SInt.UInt8.of_int 0x18); upd sbox (UInt.UInt32.of_int 174 ) (SInt.UInt8.of_int 0xbe); upd sbox (UInt.UInt32.of_int 175 ) (SInt.UInt8.of_int 0x1b); 
  upd sbox (UInt.UInt32.of_int 176 ) (SInt.UInt8.of_int 0xfc); upd sbox (UInt.UInt32.of_int 177 ) (SInt.UInt8.of_int 0x56); upd sbox (UInt.UInt32.of_int 178 ) (SInt.UInt8.of_int 0x3e); upd sbox (UInt.UInt32.of_int 179 ) (SInt.UInt8.of_int 0x4b); 
  upd sbox (UInt.UInt32.of_int 180 ) (SInt.UInt8.of_int 0xc6); upd sbox (UInt.UInt32.of_int 181 ) (SInt.UInt8.of_int 0xd2); upd sbox (UInt.UInt32.of_int 182 ) (SInt.UInt8.of_int 0x79); upd sbox (UInt.UInt32.of_int 183 ) (SInt.UInt8.of_int 0x20); 
  upd sbox (UInt.UInt32.of_int 184 ) (SInt.UInt8.of_int 0x9a); upd sbox (UInt.UInt32.of_int 185 ) (SInt.UInt8.of_int 0xdb); upd sbox (UInt.UInt32.of_int 186 ) (SInt.UInt8.of_int 0xc0); upd sbox (UInt.UInt32.of_int 187 ) (SInt.UInt8.of_int 0xfe); 
  upd sbox (UInt.UInt32.of_int 188 ) (SInt.UInt8.of_int 0x78); upd sbox (UInt.UInt32.of_int 189 ) (SInt.UInt8.of_int 0xcd); upd sbox (UInt.UInt32.of_int 190 ) (SInt.UInt8.of_int 0x5a); upd sbox (UInt.UInt32.of_int 191 ) (SInt.UInt8.of_int 0xf4); 
  upd sbox (UInt.UInt32.of_int 192 ) (SInt.UInt8.of_int 0x1f); upd sbox (UInt.UInt32.of_int 193 ) (SInt.UInt8.of_int 0xdd); upd sbox (UInt.UInt32.of_int 194 ) (SInt.UInt8.of_int 0xa8); upd sbox (UInt.UInt32.of_int 195 ) (SInt.UInt8.of_int 0x33); 
  upd sbox (UInt.UInt32.of_int 196 ) (SInt.UInt8.of_int 0x88); upd sbox (UInt.UInt32.of_int 197 ) (SInt.UInt8.of_int 0x07); upd sbox (UInt.UInt32.of_int 198 ) (SInt.UInt8.of_int 0xc7); upd sbox (UInt.UInt32.of_int 199 ) (SInt.UInt8.of_int 0x31); 
  upd sbox (UInt.UInt32.of_int 200 ) (SInt.UInt8.of_int 0xb1); upd sbox (UInt.UInt32.of_int 201 ) (SInt.UInt8.of_int 0x12); upd sbox (UInt.UInt32.of_int 202 ) (SInt.UInt8.of_int 0x10); upd sbox (UInt.UInt32.of_int 203 ) (SInt.UInt8.of_int 0x59); 
  upd sbox (UInt.UInt32.of_int 204 ) (SInt.UInt8.of_int 0x27); upd sbox (UInt.UInt32.of_int 205 ) (SInt.UInt8.of_int 0x80); upd sbox (UInt.UInt32.of_int 206 ) (SInt.UInt8.of_int 0xec); upd sbox (UInt.UInt32.of_int 207 ) (SInt.UInt8.of_int 0x5f); 
  upd sbox (UInt.UInt32.of_int 208 ) (SInt.UInt8.of_int 0x60); upd sbox (UInt.UInt32.of_int 209 ) (SInt.UInt8.of_int 0x51); upd sbox (UInt.UInt32.of_int 210 ) (SInt.UInt8.of_int 0x7f); upd sbox (UInt.UInt32.of_int 211 ) (SInt.UInt8.of_int 0xa9); 
  upd sbox (UInt.UInt32.of_int 212 ) (SInt.UInt8.of_int 0x19); upd sbox (UInt.UInt32.of_int 213 ) (SInt.UInt8.of_int 0xb5); upd sbox (UInt.UInt32.of_int 214 ) (SInt.UInt8.of_int 0x4a); upd sbox (UInt.UInt32.of_int 215 ) (SInt.UInt8.of_int 0x0d); 
  upd sbox (UInt.UInt32.of_int 216 ) (SInt.UInt8.of_int 0x2d); upd sbox (UInt.UInt32.of_int 217 ) (SInt.UInt8.of_int 0xe5); upd sbox (UInt.UInt32.of_int 218 ) (SInt.UInt8.of_int 0x7a); upd sbox (UInt.UInt32.of_int 219 ) (SInt.UInt8.of_int 0x9f); 
  upd sbox (UInt.UInt32.of_int 220 ) (SInt.UInt8.of_int 0x93); upd sbox (UInt.UInt32.of_int 221 ) (SInt.UInt8.of_int 0xc9); upd sbox (UInt.UInt32.of_int 222 ) (SInt.UInt8.of_int 0x9c); upd sbox (UInt.UInt32.of_int 223 ) (SInt.UInt8.of_int 0xef); 
  upd sbox (UInt.UInt32.of_int 224 ) (SInt.UInt8.of_int 0xa0); upd sbox (UInt.UInt32.of_int 225 ) (SInt.UInt8.of_int 0xe0); upd sbox (UInt.UInt32.of_int 226 ) (SInt.UInt8.of_int 0x3b); upd sbox (UInt.UInt32.of_int 227 ) (SInt.UInt8.of_int 0x4d); 
  upd sbox (UInt.UInt32.of_int 228 ) (SInt.UInt8.of_int 0xae); upd sbox (UInt.UInt32.of_int 229 ) (SInt.UInt8.of_int 0x2a); upd sbox (UInt.UInt32.of_int 230 ) (SInt.UInt8.of_int 0xf5); upd sbox (UInt.UInt32.of_int 231 ) (SInt.UInt8.of_int 0xb0); 
  upd sbox (UInt.UInt32.of_int 232 ) (SInt.UInt8.of_int 0xc8); upd sbox (UInt.UInt32.of_int 233 ) (SInt.UInt8.of_int 0xeb); upd sbox (UInt.UInt32.of_int 234 ) (SInt.UInt8.of_int 0xbb); upd sbox (UInt.UInt32.of_int 235 ) (SInt.UInt8.of_int 0x3c); 
  upd sbox (UInt.UInt32.of_int 236 ) (SInt.UInt8.of_int 0x83); upd sbox (UInt.UInt32.of_int 237 ) (SInt.UInt8.of_int 0x53); upd sbox (UInt.UInt32.of_int 238 ) (SInt.UInt8.of_int 0x99); upd sbox (UInt.UInt32.of_int 239 ) (SInt.UInt8.of_int 0x61); 
  upd sbox (UInt.UInt32.of_int 240 ) (SInt.UInt8.of_int 0x17); upd sbox (UInt.UInt32.of_int 241 ) (SInt.UInt8.of_int 0x2b); upd sbox (UInt.UInt32.of_int 242 ) (SInt.UInt8.of_int 0x04); upd sbox (UInt.UInt32.of_int 243 ) (SInt.UInt8.of_int 0x7e); 
  upd sbox (UInt.UInt32.of_int 244 ) (SInt.UInt8.of_int 0xba); upd sbox (UInt.UInt32.of_int 245 ) (SInt.UInt8.of_int 0x77); upd sbox (UInt.UInt32.of_int 246 ) (SInt.UInt8.of_int 0xd6); upd sbox (UInt.UInt32.of_int 247 ) (SInt.UInt8.of_int 0x26); 
  upd sbox (UInt.UInt32.of_int 248 ) (SInt.UInt8.of_int 0xe1); upd sbox (UInt.UInt32.of_int 249 ) (SInt.UInt8.of_int 0x69); upd sbox (UInt.UInt32.of_int 250 ) (SInt.UInt8.of_int 0x14); upd sbox (UInt.UInt32.of_int 251 ) (SInt.UInt8.of_int 0x63); 
  upd sbox (UInt.UInt32.of_int 252 ) (SInt.UInt8.of_int 0x55); upd sbox (UInt.UInt32.of_int 253 ) (SInt.UInt8.of_int 0x21); upd sbox (UInt.UInt32.of_int 254 ) (SInt.UInt8.of_int 0x0c); upd sbox (UInt.UInt32.of_int 255 ) (SInt.UInt8.of_int 0x7d)

val access: sbox:suint8s -> idx:suint8 -> STL suint8
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True)) 
let access sbox i =
  let rec access_aux: suint8s -> suint8 -> uint32 -> suint8 -> STL suint8
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
    = fun sbox i ctr tmp -> 
      if UInt.UInt32.eq ctr (UInt.UInt32.of_int 256) then tmp 
      else let mask = SInt.UInt8.eq i (of_uint32 ctr) in
	 let tmp = tmp ^| (mask ^& index sbox ctr) in
	 access_aux sbox i (UInt.UInt32.add ctr UInt.UInt32.one) tmp in
  access_aux sbox i UInt.UInt32.zero SInt.UInt8.zero

val subBytes_aux_sbox: state:suint8s -> suint8s -> ctr:uint32 -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rec subBytes_aux_sbox state sbox ctr =
  if UInt.UInt32.eq ctr (UInt.UInt32.of_int 16) then ()
  else 
  begin
    let si = index state ctr in
    let si' = access sbox si in
    upd state ctr si';
    subBytes_aux_sbox state sbox (UInt.UInt32.add ctr UInt.UInt32.one)
  end

val subBytes_sbox: state:suint8s -> suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let subBytes_sbox state sbox =
  subBytes_aux_sbox state sbox UInt.UInt32.zero

val shiftRows: state:suint8s{length state = 16} -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let shiftRows state =
  let i = UInt.UInt32.one in
  let tmp = index state i in
  upd state i      (index state (UInt.UInt32.add i (UInt.UInt32.of_int 4))); 
  upd state (UInt.UInt32.add i (UInt.UInt32.of_int 4))  (index state (UInt.UInt32.add i (UInt.UInt32.of_int 8))); 
  upd state (UInt.UInt32.add i (UInt.UInt32.of_int 8))  (index state (UInt.UInt32.add i (UInt.UInt32.of_int 12))); 
  upd state (UInt.UInt32.add i (UInt.UInt32.of_int 12)) tmp;
  let i = UInt.UInt32.of_int 2 in
  let tmp = index state i in
  upd state i (index state (UInt.UInt32.add i (UInt.UInt32.of_int 8))); 
  upd state (UInt.UInt32.add i (UInt.UInt32.of_int 8))  tmp; 
  let tmp = index state (UInt.UInt32.add i (UInt.UInt32.of_int 4)) in
  upd state (UInt.UInt32.add i (UInt.UInt32.of_int 4))  (index state (UInt.UInt32.add i (UInt.UInt32.of_int 12))); 
  upd state (UInt.UInt32.add i (UInt.UInt32.of_int 12)) tmp;
  let i = UInt.UInt32.of_int 3 in
  let tmp = index state i in
  upd state i      (index state (UInt.UInt32.add i (UInt.UInt32.of_int 12))); 
  upd state (UInt.UInt32.add i (UInt.UInt32.of_int 12)) (index state (UInt.UInt32.add i (UInt.UInt32.of_int 8)));
  upd state (UInt.UInt32.add i (UInt.UInt32.of_int 8))  (index state (UInt.UInt32.add i (UInt.UInt32.of_int 4))); 
  upd state (UInt.UInt32.add i (UInt.UInt32.of_int 4))  tmp; 
  ()

val multiply_2: suint8 -> suint8 -> Tot suint8 
let multiply_2 x y =
  (((y ^& one) ^*% x) 
  ^^ (((y ^>> 1) ^& one) ^*% xtime(x))
  ^^ (((y ^>> 2) ^& one) ^*% xtime(xtime(x)))
  ^^ (((y ^>> 3) ^& one) ^*% xtime(xtime(xtime(x)))))
       
let op_Star = UInt.UInt32.mul
let op_At_Plus = UInt.UInt32.add
let op_At_Subtraction = UInt.UInt32.sub

val mixColumns: suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let mixColumns state =
  let c = UInt.UInt32.zero in
  let zero = UInt.UInt32.zero in
  let one = UInt.UInt32.one in
  let two = UInt.UInt32.add one one in
  let three = UInt.UInt32.add two one in
  let four = UInt.UInt32.add two two in
  let s0 = index state (UInt.UInt32.add zero  (four*c)) in
  let s1 = index state (UInt.UInt32.add one   (four*c)) in
  let s2 = index state (UInt.UInt32.add two   (four*c)) in
  let s3 = index state (UInt.UInt32.add three (four*c)) in
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
  let zero  = UInt.UInt32.zero  in
  let one   = UInt.UInt32.one   in
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
  if UInt.UInt32.eq round (UInt.UInt32.of_int 14) then ()
  else begin
    subBytes_sbox state sbox;
    shiftRows state;
    mixColumns state;
    addRoundKey state w round; 
    cipher_loop state w sbox (round @+ UInt.UInt32.one)
  end

(* val cipher: out:suint8s{length out = Prims.op_Multiply 4 nb} -> input:suint8s{length input = 4*nb} -> w:suint8s{length w = 4 * (nr+1)} -> sbox:suint8s{length sbox = 256} -> STL unit *)
(*   (requires (fun h -> True)) *)
(*   (ensures (fun h0 _ h1 -> True)) *)
val cipher: out:suint8s -> input:suint8s -> w:suint8s -> sbox:suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let cipher out input w sbox =
  push_frame ();
  let state = create SInt.UInt8.zero ((UInt.UInt32.of_int 4)*nb) in
  blit input UInt.UInt32.zero state UInt.UInt32.zero ((UInt.UInt32.of_int 4)*nb);
  addRoundKey state w UInt.UInt32.zero;
  cipher_loop state w sbox UInt.UInt32.one;
  subBytes_sbox state sbox;
  shiftRows state;
  addRoundKey state w nr;
  blit state UInt.UInt32.zero out UInt.UInt32.zero ((UInt.UInt32.of_int 4)*nb);
  pop_frame ()

val rotWord: word:suint8s{length word = 4} -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rotWord word =
  let zero  = UInt.UInt32.zero in
  let one   = UInt.UInt32.one in
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
  let zero  = UInt.UInt32.zero in
  let one   = UInt.UInt32.one in
  let two   = one @+ one in
  let three = one @+ two in
  let w0 = index word zero in
  let w1 = index word one in
  let w2 = index word two in
  let w3 = index word three in
  upd word zero (access sbox w0);
  upd word one (access sbox w1);
  upd word two (access sbox w2);
  upd word three (access sbox w3)

(* TODO: use table ? *)
val rcon: uint32 -> suint8 -> Tot suint8
let rec rcon i tmp =
  if UInt.UInt32.eq i UInt.UInt32.one then tmp
  else begin
    let tmp = multiply (of_int 0x2) tmp in    
    rcon (i @- UInt.UInt32.one) tmp
  end

let op_At_Slash = UInt.UInt32.div
let op_At_Percent = UInt.UInt32.rem

val keyExpansion_aux: suint8s -> suint8s -> suint8s -> suint8s -> uint32 -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rec keyExpansion_aux key w temp sbox i =
  if UInt.UInt32.eq i (UInt.UInt32.of_int 240) then ()
  else begin
    let zero  = UInt.UInt32.zero in
    let one   = UInt.UInt32.one in
    let two   = one @+ one in
    let three = one @+ two in
    let four  = two @+ two in
    blit w (i @- four) temp zero four;
    if UInt.UInt32.eq ((UInt.UInt32.div i four) @% nk) zero then (
      rotWord temp;
      subWord temp sbox;
      upd temp UInt.UInt32.zero (index temp zero ^^ rcon ((i @/ four) @/ nk) SInt.UInt8.one) 
    ) else if (UInt.UInt32.eq ((i @/ four) @% nk) four) then (
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
    keyExpansion_aux key w temp sbox (i @+ UInt.UInt32.of_int 4)
  end
    
(* val keyExpansion: key:suint8s{length key = 4 * nk} -> w:suint8s{length w = 4 * (nb * (nr+1))} -> sbox:suint8s -> St unit *)
val keyExpansion: key:suint8s -> w:suint8s -> sbox:suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let keyExpansion key w sbox =
  push_frame();
  let temp = create zero (UInt.UInt32.of_int 4) in
  blit key UInt.UInt32.zero w UInt.UInt32.zero ((UInt.UInt32.of_int 4)*nk);
  let i = (UInt.UInt32.of_int 4) * nk in
  keyExpansion_aux key w temp sbox i;
  pop_frame()

val invShiftRows: state:suint8s{length state = 16} -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let invShiftRows state =
  let zero  = UInt.UInt32.zero in
  let one   = UInt.UInt32.one in
  let two   = one @+ one in
  let three = one @+ two in
  let four  = two @+ two in
  let eight  = four @+ four in
  let twelve  = four @+ eight in
  let i = three in
  let tmp = index state i in
  upd state i      (index state (i@+four)); 
  upd state (i@+four)  (index state (i@+eight)); 
  upd state (i@+eight)  (index state (i@+twelve)); 
  upd state (i@+twelve) tmp;
  let i = two in
  let tmp = index state i in
  upd state i      (index state (i@+eight)); 
  upd state (i@+eight)  tmp; 
  let tmp = index state (i@+four) in
  upd state (i@+four)  (index state (i@+twelve)); 
  upd state (i@+twelve) tmp;
  let i = one in
  let tmp = index state i in
  upd state i      (index state (i@+twelve)); 
  upd state (i@+twelve) (index state (i@+eight));
  upd state (i@+eight)  (index state (i@+four)); 
  upd state (i@+four)  tmp; 
  ()

val invSubBytes_aux_sbox: state:suint8s -> sbox:suint8s -> ctr:uint32 -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let rec invSubBytes_aux_sbox state sbox ctr =
  if UInt.UInt32.eq ctr (UInt.UInt32.of_int 16) then () 
  else begin 
    let si = index state ctr in
    let si' = access sbox si in
    upd state ctr si';
    invSubBytes_aux_sbox state sbox (ctr@+UInt.UInt32.one)
  end

val invSubBytes_sbox: state:suint8s -> suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let invSubBytes_sbox state sbox = 
  invSubBytes_aux_sbox state sbox UInt.UInt32.zero
       
val invMixColumns: suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let invMixColumns state = 
  let zero  = UInt.UInt32.zero in
  let one   = UInt.UInt32.one in
  let two   = one @+ one in
  let three = one @+ two in
  let four = two @+ two in
  let c = zero in
  let s0 = index state (zero  @+(four * c)) in
  let s1 = index state (one   @+(four * c)) in
  let s2 = index state (two   @+(four * c)) in
  let s3 = index state (three @+(four * c)) in
  upd state ((four*c) @+ one) (multiply (of_int 0xe) s0 ^^ multiply (of_int 0xb) s1
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
  if UInt.UInt32.eq round UInt.UInt32.zero then ()
  else begin
    invShiftRows state;
    invSubBytes_sbox state sbox;
    addRoundKey state w round;
    invMixColumns state;
    inv_cipher_loop state w sbox (round @- UInt.UInt32.one)
  end

(* val inv_cipher: out:suint8s{length out = 4 * nb} -> input:suint8s{length input = 4*nb} -> w:suint8s{length w = 4 * (nr+1)} -> sbox:suint8s{length sbox = 256} -> St unit *)
val inv_cipher: out:suint8s -> input:suint8s -> w:suint8s -> sbox:suint8s -> STL unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let inv_cipher out input w sbox =
  push_frame ();
  let state = create SInt.UInt8.zero (UInt.UInt32.of_int 4 * nb) in
  blit input UInt.UInt32.zero state UInt.UInt32.zero (UInt.UInt32.of_int 4 * nb);
  addRoundKey state w nr;
  inv_cipher_loop state w sbox (UInt.UInt32.of_int 13);
  invShiftRows state;
  invSubBytes_sbox state sbox;
  addRoundKey state w UInt.UInt32.zero;
  blit state UInt.UInt32.zero out UInt.UInt32.zero (UInt.UInt32.of_int 4 * nb);
  pop_frame ()
  
