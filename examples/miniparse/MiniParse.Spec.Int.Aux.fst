(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module MiniParse.Spec.Int.Aux

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module Cast = FStar.Int.Cast

inline_for_extraction
let decode_u16 (lohi: U8.t * U8.t) : Tot U16.t =
  let (lo, hi) = lohi in
  Cast.uint8_to_uint16 lo `U16.add` (256us `U16.mul` Cast.uint8_to_uint16 hi)

inline_for_extraction
let encode_u16 (x: U16.t) : Tot (U8.t * U8.t) =
  let lo = Cast.uint16_to_uint8 x in
  let hi = Cast.uint16_to_uint8 (x `U16.div` 256us) in
  (lo, hi)

let encode_u16_decode_u16 (lohi: U8.t * U8.t) : Lemma
  (encode_u16 (decode_u16 lohi) == lohi)
= ()

let decode_u16_encode_u16 (x: U16.t) : Lemma
  (decode_u16 (encode_u16 x) == x)
= ()
