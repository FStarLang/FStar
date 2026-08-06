module MachineInts
open FStar.All
open FStar.IO

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32

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

let main () : ML unit =
  show32 (wrap 4294967295ul 3ul);
  show32 (bits 12ul 10ul);
  print_string (if cmp 3uL 4uL then "lt " else "ge ");
  print_string (U8.to_string (narrow 250uy));
  print_string " ";
  print_string (I32.to_string (signed 3l));
  print_string " ";
  show32 (twice U32.add_mod 5ul);
  print_string "\n"
