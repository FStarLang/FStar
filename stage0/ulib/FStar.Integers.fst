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
module FStar.Integers

#set-options "--initial_ifuel 2 --max_ifuel 2 --initial_fuel 0 --max_fuel 0"

irreducible
let mark_for_norm = ()

unfold
let norm (#a:Type) (x:a) = norm [iota; delta_attr [`%mark_for_norm]] x

type width =
  | W8
  | W16
  | W32
  | W64
  | W128
  | Winfinite

[@@mark_for_norm]
let nat_of_width = function
  | W8   -> Some 8
  | W16  -> Some 16
  | W32  -> Some 32
  | W64  -> Some 64
  | W128 -> Some 128
  | Winfinite -> None

let fixed_width = w:width{w <> Winfinite}

[@@mark_for_norm]
let nat_of_fixed_width (w:fixed_width) =
  match nat_of_width w with
  | Some v -> v

type signed_width =
  | Signed of width
  | Unsigned of fixed_width //We don't support (Unsigned WInfinite); use nat instead

[@@mark_for_norm]
let width_of_sw = function
  | Signed w -> w
  | Unsigned w -> w

[@@mark_for_norm]
noextract
inline_for_extraction
let int_t sw : Tot Type0 =
  match sw with
  | Unsigned W8 -> FStar.UInt8.t
  | Unsigned W16 -> FStar.UInt16.t
  | Unsigned W32 -> FStar.UInt32.t
  | Unsigned W64 -> FStar.UInt64.t
  | Unsigned W128 -> FStar.UInt128.t
  | Signed Winfinite -> int
  | Signed W8 -> FStar.Int8.t
  | Signed W16 -> FStar.Int16.t
  | Signed W32 -> FStar.Int32.t
  | Signed W64 -> FStar.Int64.t
  | Signed W128 -> FStar.Int128.t

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let within_bounds' sw (x:int) =
  match sw, nat_of_width (width_of_sw sw) with
  | Signed _,   None   -> True
  | Signed _,   Some n -> FStar.Int.size x n
  | Unsigned _, Some n -> FStar.UInt.size x n

unfold
let within_bounds sw x = norm (within_bounds' sw x)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let v #sw (x:int_t sw)
  : Tot (y:int_t (Signed Winfinite){within_bounds sw y})
  = match sw with
    | Unsigned w ->
      (match w with
       | W8 -> FStar.UInt8.v x
       | W16 -> FStar.UInt16.v x
       | W32 -> FStar.UInt32.v x
       | W64 -> FStar.UInt64.v x
       | W128 -> FStar.UInt128.v x)
    | Signed w ->
      (match w with
       | Winfinite -> x
       | W8 -> FStar.Int8.v x
       | W16 -> FStar.Int16.v x
       | W32 -> FStar.Int32.v x
       | W64 -> FStar.Int64.v x
       | W128 -> FStar.Int128.v x)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let u    #sw
        (x:int_t (Signed Winfinite){within_bounds sw x})
  : Tot (y:int_t sw{norm (v x == v y)})
  = match sw with
    | Unsigned w ->
      (match w with
       | W8 -> FStar.UInt8.uint_to_t x
       | W16 -> FStar.UInt16.uint_to_t x
       | W32 -> FStar.UInt32.uint_to_t x
       | W64 -> FStar.UInt64.uint_to_t x
       | W128 -> FStar.UInt128.uint_to_t x)
    | Signed w ->
      (match w with
       | Winfinite -> x
       | W8 -> FStar.Int8.int_to_t x
       | W16 -> FStar.Int16.int_to_t x
       | W32 -> FStar.Int32.int_to_t x
       | W64 -> FStar.Int64.int_to_t x
       | W128 -> FStar.Int128.int_to_t x)

irreducible
noextract
let cast #sw #sw'
         (from:int_t sw{within_bounds sw' (v from)})
   : Tot (to:int_t sw'{norm (v from == v to)})
   = u (v from)

[@@mark_for_norm]
unfold
noextract
let cast_ok #from to (x:int_t from) = within_bounds to (v x)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( + ) #sw
          (x:int_t sw)
          (y:int_t sw{within_bounds sw (v x + v y)})
  : Tot   (int_t sw)
  = match sw with
    | Signed Winfinite -> x + y
    | Unsigned W8   -> FStar.UInt8.(x +^ y)
    | Unsigned W16  -> FStar.UInt16.(x +^ y)
    | Unsigned W32  -> FStar.UInt32.(x +^ y)
    | Unsigned W64  -> FStar.UInt64.(x +^ y)
    | Unsigned W128 -> FStar.UInt128.(x +^ y)
    | Signed W8   -> FStar.Int8.(x +^ y)
    | Signed W16  -> FStar.Int16.(x +^ y)
    | Signed W32  -> FStar.Int32.(x +^ y)
    | Signed W64  -> FStar.Int64.(x +^ y)
    | Signed W128 -> FStar.Int128.(x +^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( +? ) (#w:fixed_width)
           (x:int_t (Unsigned w))
           (y:int_t (Unsigned w))
  : Tot    (int_t (Unsigned w))
  = match w with
    | W8 -> FStar.UInt8.(x +?^ y)
    | W16 -> FStar.UInt16.(x +?^ y)
    | W32 -> FStar.UInt32.(x +?^ y)
    | W64 -> FStar.UInt64.(x +?^ y)
    | W128 -> FStar.UInt128.(x +?^ y)

[@@mark_for_norm; strict_on_arguments [0]]
noextract
let modulo sw (x:int) (y:pos{Signed? sw ==> y%2=0}) =
  match sw with
  | Unsigned _ ->  x % y
  | _ -> FStar.Int.(x @% y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( +% ) (#sw:_{Unsigned? sw})
           (x:int_t sw)
           (y:int_t sw)
  : Tot    (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x +%^ y)
    | W16 -> FStar.UInt16.(x +%^ y)
    | W32 -> FStar.UInt32.(x +%^ y)
    | W64 -> FStar.UInt64.(x +%^ y)
    | W128 -> FStar.UInt128.(x +%^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let op_Subtraction #sw
                   (x:int_t sw)
                   (y:int_t sw{within_bounds sw (v x - v y)})
    : Tot          (int_t sw)
  = match sw with
    | Signed Winfinite -> x - y
    | Unsigned W8 -> FStar.UInt8.(x -^ y)
    | Unsigned W16 -> FStar.UInt16.(x -^ y)
    | Unsigned W32 -> FStar.UInt32.(x -^ y)
    | Unsigned W64 -> FStar.UInt64.(x -^ y)
    | Unsigned W128 -> FStar.UInt128.(x -^ y)
    | Signed W8 -> FStar.Int8.(x -^ y)
    | Signed W16 -> FStar.Int16.(x -^ y)
    | Signed W32 -> FStar.Int32.(x -^ y)
    | Signed W64 -> FStar.Int64.(x -^ y)
    | Signed W128 -> FStar.Int128.(x -^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let op_Subtraction_Question
        (#sw:_{Unsigned? sw})
        (x:int_t sw)
        (y:int_t sw)
  : Tot (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x -?^ y)
    | W16 -> FStar.UInt16.(x -?^ y)
    | W32 -> FStar.UInt32.(x -?^ y)
    | W64 -> FStar.UInt64.(x -?^ y)
    | W128 -> FStar.UInt128.(x -?^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let op_Subtraction_Percent
         (#sw:_{Unsigned? sw})
         (x:int_t sw)
         (y:int_t sw)
  : Tot  (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x -%^ y)
    | W16 -> FStar.UInt16.(x -%^ y)
    | W32 -> FStar.UInt32.(x -%^ y)
    | W64 -> FStar.UInt64.(x -%^ y)
    | W128 -> FStar.UInt128.(x -%^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let op_Minus
         (#sw:_{Signed? sw})
         (x:int_t sw{within_bounds sw (0 - v x)})
  : Tot  (int_t sw)
  = let Signed w = sw in
    match w with
    | Winfinite -> 0 - x
    | W8 -> FStar.Int8.(0y -^ x)
    | W16 -> FStar.Int16.(0s -^ x)
    | W32 -> FStar.Int32.(0l -^ x)
    | W64 -> FStar.Int64.(0L -^ x)
    | W128 -> FStar.Int128.(int_to_t 0 -^ x)

open FStar.Mul
[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( * ) (#sw:signed_width{width_of_sw sw <> W128})
          (x:int_t sw)
          (y:int_t sw{within_bounds sw (v x * v y)})
  : Tot   (int_t sw)
  = match sw with
    | Signed Winfinite -> x * y
    | Unsigned W8 -> FStar.UInt8.(x *^ y)
    | Unsigned W16 -> FStar.UInt16.(x *^ y)
    | Unsigned W32 -> FStar.UInt32.(x *^ y)
    | Unsigned W64 -> FStar.UInt64.(x *^ y)
    | Signed W8 -> FStar.Int8.(x *^ y)
    | Signed W16 -> FStar.Int16.(x *^ y)
    | Signed W32 -> FStar.Int32.(x *^ y)
    | Signed W64 -> FStar.Int64.(x *^ y)
    | Signed W128 -> FStar.Int128.(x *^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( *? ) (#sw:_{Unsigned? sw /\ width_of_sw sw <> W128})
           (x:int_t sw)
           (y:int_t sw)
  : Tot    (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x *?^ y)
    | W16 -> FStar.UInt16.(x *?^ y)
    | W32 -> FStar.UInt32.(x *?^ y)
    | W64 -> FStar.UInt64.(x *?^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( *% ) (#sw:_{Unsigned? sw /\ width_of_sw sw <> W128})
           (x:int_t sw)
           (y:int_t sw)
  : Tot    (int_t sw)
  = let Unsigned w = sw in
    match w with
    | W8 -> FStar.UInt8.(x *%^ y)
    | W16 -> FStar.UInt16.(x *%^ y)
    | W32 -> FStar.UInt32.(x *%^ y)
    | W64 -> FStar.UInt64.(x *%^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( > ) #sw (x:int_t sw) (y:int_t sw) : bool =
    match sw with
    | Signed Winfinite -> x > y
    | Unsigned W8 -> FStar.UInt8.(x >^ y)
    | Unsigned W16 -> FStar.UInt16.(x >^ y)
    | Unsigned W32 -> FStar.UInt32.(x >^ y)
    | Unsigned W64 -> FStar.UInt64.(x >^ y)
    | Unsigned W128 -> FStar.UInt128.(x >^ y)
    | Signed W8 -> FStar.Int8.(x >^ y)
    | Signed W16 -> FStar.Int16.(x >^ y)
    | Signed W32 -> FStar.Int32.(x >^ y)
    | Signed W64 -> FStar.Int64.(x >^ y)
    | Signed W128 -> FStar.Int128.(x >^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( >= ) #sw (x:int_t sw) (y:int_t sw) : bool =
    match sw with
    | Signed Winfinite -> x >= y
    | Unsigned W8 -> FStar.UInt8.(x >=^ y)
    | Unsigned W16 -> FStar.UInt16.(x >=^ y)
    | Unsigned W32 -> FStar.UInt32.(x >=^ y)
    | Unsigned W64 -> FStar.UInt64.(x >=^ y)
    | Unsigned W128 -> FStar.UInt128.(x >=^ y)
    | Signed W8 -> FStar.Int8.(x >=^ y)
    | Signed W16 -> FStar.Int16.(x >=^ y)
    | Signed W32 -> FStar.Int32.(x >=^ y)
    | Signed W64 -> FStar.Int64.(x >=^ y)
    | Signed W128 -> FStar.Int128.(x >=^ y)


[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( < ) #sw (x:int_t sw) (y:int_t sw) : bool =
    match sw with
    | Signed Winfinite -> x < y
    | Unsigned W8 -> FStar.UInt8.(x <^ y)
    | Unsigned W16 -> FStar.UInt16.(x <^ y)
    | Unsigned W32 -> FStar.UInt32.(x <^ y)
    | Unsigned W64 -> FStar.UInt64.(x <^ y)
    | Unsigned W128 -> FStar.UInt128.(x <^ y)
    | Signed W8 -> FStar.Int8.(x <^ y)
    | Signed W16 -> FStar.Int16.(x <^ y)
    | Signed W32 -> FStar.Int32.(x <^ y)
    | Signed W64 -> FStar.Int64.(x <^ y)
    | Signed W128 -> FStar.Int128.(x <^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( <= ) #sw (x:int_t sw) (y:int_t sw) : bool =
    match sw with
    | Signed Winfinite -> x <= y
    | Unsigned W8 -> FStar.UInt8.(x <=^ y)
    | Unsigned W16 -> FStar.UInt16.(x <=^ y)
    | Unsigned W32 -> FStar.UInt32.(x <=^ y)
    | Unsigned W64 -> FStar.UInt64.(x <=^ y)
    | Unsigned W128 -> FStar.UInt128.(x <=^ y)
    | Signed W8 -> FStar.Int8.(x <=^ y)
    | Signed W16 -> FStar.Int16.(x <=^ y)
    | Signed W32 -> FStar.Int32.(x <=^ y)
    | Signed W64 -> FStar.Int64.(x <=^ y)
    | Signed W128 -> FStar.Int128.(x <=^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( / ) (#sw:signed_width{sw <> Unsigned W128})
          (x:int_t sw)
          (y:int_t sw{0 <> (v y <: Prims.int) /\
                      (match sw with
                       | Unsigned _ -> within_bounds sw (v x / v y)
                       | Signed _ -> within_bounds sw (v x `FStar.Int.op_Slash` v y))})
   : Tot (int_t sw)
   = match sw with
     | Signed Winfinite -> x / y
     | Unsigned W8 -> FStar.UInt8.(x /^ y)
     | Unsigned W16 -> FStar.UInt16.(x /^ y)
     | Unsigned W32 -> FStar.UInt32.(x /^ y)
     | Unsigned W64 -> FStar.UInt64.(x /^ y)
     | Signed W8 -> FStar.Int8.(x /^ y)
     | Signed W16 -> FStar.Int16.(x /^ y)
     | Signed W32 -> FStar.Int32.(x /^ y)
     | Signed W64 -> FStar.Int64.(x /^ y)
     | Signed W128 -> FStar.Int128.(x /^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( % ) (#sw:signed_width{sw <> Unsigned W128})
          (x:int_t sw)
          (y:int_t sw{0 <> (v y <: Prims.int) /\
                      (match sw with
                       | Unsigned _ -> within_bounds sw (FStar.UInt.mod #(nat_of_fixed_width (width_of_sw sw)) (v x) (v y))
                       | Signed Winfinite -> True
                       | Signed _ -> within_bounds sw (FStar.Int.mod #(nat_of_fixed_width (width_of_sw sw)) (v x) (v y))) /\
                       within_bounds sw (FStar.Int.op_Slash (v x) (v y))})
   : Tot (int_t sw)
   = match sw with
     | Signed Winfinite -> x % y
     | Unsigned W8 -> FStar.UInt8.(x %^ y)
     | Unsigned W16 -> FStar.UInt16.(x %^ y)
     | Unsigned W32 -> FStar.UInt32.(x %^ y)
     | Unsigned W64 -> FStar.UInt64.(x %^ y)
     | Signed W8 -> FStar.Int8.(x %^ y)
     | Signed W16 -> FStar.Int16.(x %^ y)
     | Signed W32 -> FStar.Int32.(x %^ y)
     | Signed W64 -> FStar.Int64.(x %^ y)
     | Signed W128 -> FStar.Int128.(x %^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( ^^ ) #sw (x:int_t sw) (y:int_t sw{width_of_sw sw <> Winfinite})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x ^^ y)
      | Unsigned W16 -> FStar.UInt16.(x ^^ y)
      | Unsigned W32 -> FStar.UInt32.(x ^^ y)
      | Unsigned W64 -> FStar.UInt64.(x ^^ y)
      | Unsigned W128 -> FStar.UInt128.(x ^^ y)
      | Signed W8 -> FStar.Int8.(x ^^ y)
      | Signed W16 -> FStar.Int16.(x ^^ y)
      | Signed W32 -> FStar.Int32.(x ^^ y)
      | Signed W64 -> FStar.Int64.(x ^^ y)
      | Signed W128 -> FStar.Int128.(x ^^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( &^ ) #sw (x:int_t sw) (y:int_t sw{width_of_sw sw <> Winfinite})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x &^ y)
      | Unsigned W16 -> FStar.UInt16.(x &^ y)
      | Unsigned W32 -> FStar.UInt32.(x &^ y)
      | Unsigned W64 -> FStar.UInt64.(x &^ y)
      | Unsigned W128 -> FStar.UInt128.(x &^ y)
      | Signed W8 -> FStar.Int8.(x &^ y)
      | Signed W16 -> FStar.Int16.(x &^ y)
      | Signed W32 -> FStar.Int32.(x &^ y)
      | Signed W64 -> FStar.Int64.(x &^ y)
      | Signed W128 -> FStar.Int128.(x &^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( |^ ) #sw (x:int_t sw) (y:int_t sw{width_of_sw sw <> Winfinite})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x |^ y)
      | Unsigned W16 -> FStar.UInt16.(x |^ y)
      | Unsigned W32 -> FStar.UInt32.(x |^ y)
      | Unsigned W64 -> FStar.UInt64.(x |^ y)
      | Unsigned W128 -> FStar.UInt128.(x |^ y)
      | Signed W8 -> FStar.Int8.(x |^ y)
      | Signed W16 -> FStar.Int16.(x |^ y)
      | Signed W32 -> FStar.Int32.(x |^ y)
      | Signed W64 -> FStar.Int64.(x |^ y)
      | Signed W128 -> FStar.Int128.(x |^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( <<^ ) #sw (x:int_t sw{0 <= v x})
                (y:int_t (Unsigned W32){width_of_sw sw <> Winfinite /\ v y < nat_of_fixed_width (width_of_sw sw) /\ (Signed? sw ==> within_bounds sw (v x * pow2 (v y)))})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x <<^ y)
      | Unsigned W16 -> FStar.UInt16.(x <<^ y)
      | Unsigned W32 -> FStar.UInt32.(x <<^ y)
      | Unsigned W64 -> FStar.UInt64.(x <<^ y)
      | Unsigned W128 -> FStar.UInt128.(x <<^ y)
      | Signed W8 -> FStar.Int8.(x <<^ y)
      | Signed W16 -> FStar.Int16.(x <<^ y)
      | Signed W32 -> FStar.Int32.(x <<^ y)
      | Signed W64 -> FStar.Int64.(x <<^ y)
      | Signed W128 -> FStar.Int128.(x <<^ y)

[@@mark_for_norm; strict_on_arguments [0]]
unfold
noextract
let ( >>^ ) #sw (x:int_t sw{0 <= v x})
                (y:int_t (Unsigned W32){width_of_sw sw <> Winfinite /\ v y < nat_of_fixed_width (width_of_sw sw)})
    : Tot (int_t sw)
    = match sw with
      | Unsigned W8 -> FStar.UInt8.(x >>^ y)
      | Unsigned W16 -> FStar.UInt16.(x >>^ y)
      | Unsigned W32 -> FStar.UInt32.(x >>^ y)
      | Unsigned W64 -> FStar.UInt64.(x >>^ y)
      | Unsigned W128 -> FStar.UInt128.(x >>^ y)
      | Signed W8 -> FStar.Int8.(x >>^ y)
      | Signed W16 -> FStar.Int16.(x >>^ y)
      | Signed W32 -> FStar.Int32.(x >>^ y)
      | Signed W64 -> FStar.Int64.(x >>^ y)
      | Signed W128 -> FStar.Int128.(x >>^ y)

[@@mark_for_norm]
unfold
let uint_8   = int_t (Unsigned W8)

[@@mark_for_norm]
unfold
let uint_16  = int_t (Unsigned W16)

[@@mark_for_norm]
unfold
let uint_32  = int_t (Unsigned W32)

[@@mark_for_norm]
unfold
let uint_64  = int_t (Unsigned W64)

[@@mark_for_norm]
unfold
let int       = int_t (Signed Winfinite)

[@@mark_for_norm]
unfold
let int_8   = int_t (Signed W8)

[@@mark_for_norm]
unfold
let int_16  = int_t (Signed W16)

[@@mark_for_norm]
unfold
let int_32  = int_t (Signed W32)

[@@mark_for_norm]
unfold
let int_64  = int_t (Signed W64)

[@@mark_for_norm]
unfold
let int_128 = int_t (Signed W128)

[@@mark_for_norm]
unfold
let ok #sw
       (op:(int_t (Signed Winfinite)
          -> int_t (Signed Winfinite)
          -> int_t (Signed Winfinite)))
       (x:int_t sw)
       (y:int_t sw)
   = within_bounds sw (op (v x) (v y))

[@@mark_for_norm]
unfold
let nat = i:int{ i >= 0 }

[@@mark_for_norm]
unfold
let pos = i:nat{ 0 < i }

////////////////////////////////////////////////////////////////////////////////
//Test
////////////////////////////////////////////////////////////////////////////////
let f_int (x:int) (y:int) = x + y
let f_nat (x:nat) (y:nat) = x + y
let f_nat_int_pos (x:nat) (y:int) (z:pos) = x + y + z
let f_uint_8 (x:uint_8) (y:uint_8{ok (+) x y}) = x + y
let f_int_16 (x:int_16) (y:int_16{ok (+) x y}) = x + y
let g (x:uint_32) (y:uint_32{ok ( * ) y y /\ ok (+) x (y * y)}) = x + y * y
let h (x:Prims.nat) (y:Prims.nat): nat  = u x + u y
let i (x:Prims.nat) (y:Prims.nat) = x + y
let j (x:Prims.int) (y:Prims.nat) = x - y
let k (x:Prims.int) (y:Prims.int) = x * y
