(* Section 125.  Neither C nor karamel has a rotate operator, so
   [rotate_left] and [rotate_right] expand to a shift pair, and the distance
   is the whole difficulty: the obvious [a >> (n - s)] is a shift by [n] when
   [s] is zero, which C leaves undefined.  Rotating by zero is therefore the
   case that matters most here, and it is checked at every width.

   The expected values are written out rather than printed and accepted: a
   golden taken from the run would agree with whatever the rule does, and
   what is being tested is that the rule agrees with arithmetic.  The test
   returns the number of the first check that failed, so a failure on any
   backend names itself -- and says so through the exit code rather than by
   printing, since direct-to-C has no krmllib and so no [print_string] to
   link against. *)
module Rotate
open FStar.All

module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8  = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

let rol8   (x : U8.t)  (s : U32.t{U32.v s < 8})  : U8.t  = U8.rotate_left  x s
let ror8   (x : U8.t)  (s : U32.t{U32.v s < 8})  : U8.t  = U8.rotate_right x s
let rol16  (x : U16.t) (s : U32.t{U32.v s < 16}) : U16.t = U16.rotate_left  x s
let ror16  (x : U16.t) (s : U32.t{U32.v s < 16}) : U16.t = U16.rotate_right x s
let rol32  (x : U32.t) (s : U32.t{U32.v s < 32}) : U32.t = U32.rotate_left  x s
let ror32  (x : U32.t) (s : U32.t{U32.v s < 32}) : U32.t = U32.rotate_right x s
let rol64  (x : U64.t) (s : U32.t{U32.v s < 64}) : U64.t = U64.rotate_left  x s
let ror64  (x : U64.t) (s : U32.t{U32.v s < 64}) : U64.t = U64.rotate_right x s

(* A rotate is about the bit pattern, so at a signed width the right shift
   has to be the logical one.  [>>] is not, which is why the rule rotates at
   the unsigned width of the same size and casts back.  A negative operand is
   the only thing that can tell the two apart. *)
let irol32 (x : I32.t) (s : U32.t{U32.v s < 32}) : I32.t = I32.rotate_left  x s
let iror32 (x : I32.t) (s : U32.t{U32.v s < 32}) : I32.t = I32.rotate_right x s

(* [shift_arithmetic_right] keeps the sign bit, where a logical shift of the
   same bits does not. *)
let sar8  (x : I8.t)  (s : U32.t{U32.v s < 8})  : I8.t  = I8.shift_arithmetic_right x s
let sar16 (x : I16.t) (s : U32.t{U32.v s < 16}) : I16.t = I16.shift_arithmetic_right x s
let sar32 (x : I32.t) (s : U32.t{U32.v s < 32}) : I32.t = I32.shift_arithmetic_right x s
let sar64 (x : I64.t) (s : U32.t{U32.v s < 64}) : I64.t = I64.shift_arithmetic_right x s

(* [n] is the number of the check, and the first one that fails is the exit
   status.  Zero is success, so the checks are numbered from one. *)
let chk (acc : Int32.t) (n : Int32.t) (b : bool) : Int32.t =
  if b then acc else if Int32.eq acc 0l then n else acc

let main () : ML Int32.t =
  let r = 0l in
  (* Rotating by zero: the distance the mask has to turn into zero. *)
  let r = chk r 1l  (U8.eq  (rol8 0xa5uy 0ul) 165uy) in
  let r = chk r 2l  (U8.eq  (ror8 0xa5uy 0ul) 165uy) in
  let r = chk r 3l  (U16.eq (rol16 0xa5a5us 0ul) 42405us) in
  let r = chk r 4l  (U16.eq (ror16 0xa5a5us 0ul) 42405us) in
  let r = chk r 5l  (U32.eq (rol32 0x12345678ul 0ul) 305419896ul) in
  let r = chk r 6l  (U32.eq (ror32 0x12345678ul 0ul) 305419896ul) in
  let r = chk r 7l  (U64.eq (rol64 0x123456789abcdefuL 0ul) 81985529216486895uL) in
  let r = chk r 8l  (U64.eq (ror64 0x123456789abcdefuL 0ul) 81985529216486895uL) in
  (* And the two ends of the range the mask must leave alone. *)
  let r = chk r 9l  (U8.eq  (rol8 0xa5uy 1ul) 75uy) in
  let r = chk r 10l (U8.eq  (ror8 0xa5uy 1ul) 210uy) in
  let r = chk r 11l (U8.eq  (rol8 0xa5uy 7ul) 210uy) in
  let r = chk r 12l (U8.eq  (ror8 0xa5uy 7ul) 75uy) in
  let r = chk r 13l (U16.eq (rol16 0xa5a5us 1ul) 19275us) in
  let r = chk r 14l (U16.eq (ror16 0xa5a5us 15ul) 19275us) in
  let r = chk r 15l (U32.eq (rol32 0x12345678ul 4ul) 591751041ul) in
  let r = chk r 16l (U32.eq (ror32 0x12345678ul 31ul) 610839792ul) in
  let r = chk r 17l (U64.eq (rol64 0x123456789abcdefuL 8ul) 2541551405711093505uL) in
  let r = chk r 18l (U64.eq (ror64 0x123456789abcdefuL 63ul) 163971058432973790uL) in
  (* Signed rotate, on a negative value: an arithmetic right shift here would
     smear the sign bit over the result. *)
  let r = chk r 19l (I32.eq (irol32 (-1091581332l) 0ul) (-1091581332l)) in
  let r = chk r 20l (I32.eq (iror32 (-1091581332l) 0ul) (-1091581332l)) in
  let r = chk r 21l (I32.eq (irol32 (-1091581332l) 4ul) (-285432117l)) in
  let r = chk r 22l (I32.eq (iror32 (-1091581332l) 4ul) (-873530202l)) in
  (* Arithmetic shift, on a negative value at each width.  A shift by the
     width less one leaves -1 exactly when the sign bit was replicated. *)
  let r = chk r 23l (I8.eq  (sar8 (-100y) 0ul) (-100y)) in
  let r = chk r 24l (I8.eq  (sar8 (-100y) 3ul) (-13y)) in
  let r = chk r 25l (I8.eq  (sar8 (-100y) 7ul) (-1y)) in
  let r = chk r 26l (I16.eq (sar16 (-30000s) 4ul) (-1875s)) in
  let r = chk r 27l (I16.eq (sar16 (-30000s) 15ul) (-1s)) in
  let r = chk r 28l (I32.eq (sar32 (-2000000000l) 8ul) (-7812500l)) in
  let r = chk r 29l (I32.eq (sar32 (-2000000000l) 31ul) (-1l)) in
  let r = chk r 30l (I64.eq (sar64 (-9000000000000000000L) 16ul) (-137329101562500L)) in
  chk r 31l (I64.eq (sar64 (-9000000000000000000L) 63ul) (-1L))
