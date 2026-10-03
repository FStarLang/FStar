module MachineInts
open FStar.All
open FStar.IO

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32
module I8  = FStar.Int8
module U16 = FStar.UInt16
module SZ  = FStar.SizeT
module Cast = FStar.Int.Cast

(* Machine arithmetic must become machine instructions, not the modular
   arithmetic over Prims.int that FStar.UInt actually specifies (section 8.1,
   kind 1); the type must become a machine type, not the record wrapping a
   refined nat (kind 2). *)
let wrap (x y : U32.t) : U32.t = U32.add_mod x y

let bits (x y : U32.t) : U32.t =
  U32.logxor (U32.logand x y) (U32.shift_right (U32.lognot (U32.logor x y)) 28ul)

let cmp (x y : U64.t) : bool = U64.lt x y || U64.eq x y

let narrow (x : U8.t) : U8.t = U8.logand x 15uy

let signed (x : I32.t{I32.v x = 3}) : I32.t = I32.sub x 7l

(* A primitive is an operator in the IR but a function in F*, so passing one
   around has to eta-expand it. *)
let twice (f : U32.t -> U32.t -> U32.t) (x : U32.t) : U32.t = f (f x x) x

let show32 (x : U32.t) : ML unit = print_string (U32.to_string x); print_string " "

(* Width conversions.  Every machine width is a *distinct* OCaml type -- and a
   distinct C type -- so a coercion between two of them has to be a real
   conversion, and a narrowing one has to mask (section 8.1). *)
let widen (x : U8.t) : U64.t = Cast.uint8_to_uint64 x
let narrow32 (x : U32.t) : U8.t = Cast.uint32_to_uint8 x
let resign (x : I32.t) : I8.t = Cast.int32_to_int8 x

(* A *round trip* through a narrower width.  Every backend spells a conversion
   as a cast, and it is tempting to fuse two of them -- which is right for a
   representation coercion, where nothing computes, and a miscompilation here:
   the inner conversion is exactly the one that throws the top bits away.  The
   IR keeps the two apart ([ECast] against [ECoerce]) so that no pass has to
   guess which it is looking at. *)
let round_trip (x : U32.t) : U32.t =
  Cast.uint8_to_uint32 (Cast.uint32_to_uint8 x)

(* [FStar.SizeT]'s conversions are compiled as coercions rather than as calls,
   because C has no support library for them. *)
let to_sz (x : U16.t) : SZ.t = SZ.uint16_to_sizet x
let of_sz (x : SZ.t) : U64.t = SZ.sizet_to_uint64 x

let main () : ML unit =
  show32 (wrap 4294967295ul 3ul);
  show32 (bits 12ul 10ul);
  print_string (if cmp 3uL 4uL then "lt " else "ge ");
  print_string (U8.to_string (narrow 250uy));
  print_string " ";
  print_string (I32.to_string (signed 3l));
  print_string " ";
  show32 (twice U32.add_mod 5ul);
  print_string (U64.to_string (widen 200uy));
  print_string " ";
  print_string (U8.to_string (narrow32 0x1234ff00ul));
  print_string " ";
  print_string (I8.to_string (resign (-129l)));
  print_string " ";
  print_string (U64.to_string (of_sz (to_sz 60000us)));
  print_string " ";
  show32 (round_trip 0x1234ff12ul);
  print_string "\n"
