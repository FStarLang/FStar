module ExtPrimsInt

/// `Prims.int`, the part every backend is expected to get right: addition,
/// subtraction, negation and comparison of small values.
///
/// OCaml realizes `Prims.int` with Zarith, i.e. real bignums. C does *not*:
/// karamel/include/krml/internal/compat.h defines
/// `typedef int32_t Prims_pos, Prims_nat, Prims_nonzero, Prims_int` and
/// krmllib's prims.c wraps every operation in `RETURN_OR`, which aborts with
/// exit code 252 on 32-bit overflow. That is a documented porting aid rather
/// than a faithful realization, so bignums live in ExtPrimsIntBignum,
/// division in ExtPrimsIntDiv and multiplication in ExtPrimsIntMul, each of
/// which is XFAILed on the backends that cannot do it.
///
/// F* extraction constant-folds literal `Prims.int` arithmetic, so every
/// operand must be a top-level `let` -- opaque to extraction, but still
/// delta-reducible for the SMT solver -- or the test is vacuous.

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
     chk 1l (a + b = 22)
 &&& chk 2l (a - b = 12)
 &&& chk 3l (-a = -17)
 &&& chk 4l (a + c = 0)
 &&& chk 5l (b - a = -12)
 &&& chk 6l (c - d = -12)
 &&& chk 7l (- (-a) = 17)
 &&& chk 8l (a > b)
 &&& chk 9l (c < d)
 &&& chk 10l (a >= a + z)
 &&& chk 11l (b <= a)
 &&& chk 12l (a = a + z)
 &&& chk 13l (a <> b)
 &&& chk 14l (not (a < b))
 &&& chk 15l (c < z)
 &&& chk 16l (z > c)
