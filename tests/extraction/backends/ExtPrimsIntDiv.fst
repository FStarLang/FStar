module ExtPrimsIntDiv

/// `Prims.int` division and remainder. **Known C bug, XFAIL_C.**
///
/// F*'s `/` and `%` on `Prims.int` are *Euclidean*: the remainder is always
/// non-negative, whatever the signs of the operands.
///
///     (-17) /   5  = -4      (-17) %   5  = 3
///       17  / (-5) = -3        17  % (-5) = 2
///     (-17) / (-5) =  4      (-17) % (-5) = 3
///
/// C's `/` and `%` (and OCaml's `/` and `mod`) truncate towards zero instead,
/// giving -3 and -2 for the first line. karamel/krmllib/dist/generic/prims.c
/// implements
///
///     int32_t Prims_op_Division(int32_t x, int32_t y) { RETURN_OR((int64_t)x / (int64_t)y); }
///     int32_t Prims_op_Modulus (int32_t x, int32_t y) { RETURN_OR((int64_t)x % (int64_t)y); }
///
/// i.e. it hands the operation straight to C, so every negative dividend is
/// silently wrong (severity 2). Since F* proves `x % 5 >= 0`, the bad value
/// can be laundered into an out-of-bounds index, which is why this is worse
/// than it looks. OCaml is fine because extraction routes these through
/// `Prims.op_Slash`/`op_Percent`, which are Zarith `ediv`/`erem`.

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

let positive_operands () : I32.t =
     chk 1l (a / b = 3)
 &&& chk 2l (a % b = 2)
 &&& chk 3l (a / one = a)
 &&& chk 4l (z / b = 0)
 &&& chk 5l (z % b = 0)

let negative_dividend () : I32.t =
     chk 10l (c / b = -4)
 &&& chk 11l (c % b = 3)

let negative_divisor () : I32.t =
     chk 20l (a / d = -3)
 &&& chk 21l (a % d = 2)

let both_negative () : I32.t =
     chk 30l (c / d = 4)
 &&& chk 31l (c % d = 3)

/// The remainder is non-negative in every quadrant -- this is the property
/// F* lets you rely on, and the one a truncating backend breaks.
let remainder_is_nonnegative () : I32.t =
     chk 40l (a % b >= 0)
 &&& chk 41l (c % b >= 0)
 &&& chk 42l (a % d >= 0)
 &&& chk 43l (c % d >= 0)

let main () : I32.t =
     positive_operands ()
 &&& negative_dividend ()
 &&& negative_divisor ()
 &&& both_negative ()
 &&& remainder_is_nonnegative ()
