module ExtPrimsIntMul

/// `*` on `Prims.int`. **Known C bug, XFAIL_C.**
///
/// F* extraction emits `Prims.op_Star` for `*`, and the C backend turns that
/// into a call to `Prims_op_Star`. But krmllib only ever defines
/// `Prims_op_Multiply` (karamel/krmllib/dist/generic/prims.c), so the
/// generated C fails to compile ("implicit declaration of function
/// `Prims_op_Star`") and would fail to link even without -Werror. Severity 4.

module I32 = FStar.Int32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let a : int = 17
let b : int = 5
let c : int = -17
let d : int = -5
let z : int = 0
let one : int = 1
let two : int = 2

let main () : I32.t =
     chk 1l (a * b = 85)
 &&& chk 2l (c * b = -85)
 &&& chk 3l (c * d = 85)
 &&& chk 4l (a * z = 0)
 &&& chk 5l (a * one = a)
 &&& chk 6l (two * a = 34)
 &&& chk 7l ((a / b) * b + a % b = a)
 &&& chk 8l ((c / b) * b + c % b = c)
