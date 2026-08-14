module ExtPrimsIntBignum

/// `Prims.int` beyond 32 bits. **Known C limitation, XFAIL_C.**
///
/// `Prims_int` is `int32_t` in C (karamel/include/krml/internal/compat.h), so
/// nothing here fits. Operations go through `RETURN_OR`, which detects the
/// overflow and calls `KRML_HOST_EXIT(252)` -- noisy, and arguably the right
/// thing for a porting aid. *Literals*, however, bypass that check entirely:
/// they are printed verbatim into the C source and the compiler truncates
/// them, so `big2` below silently becomes -775520534 (gcc only tells you
/// because of -Werror=overflow). That is a silent wrong value, severity 2.
///
/// OCaml is exact (Zarith).

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

/// Larger than 2^63, so a backend using any machine word gets this wrong.
let big  : int = 123456789012345678901234567890
let big2 : int = 987654321098765432109876543210

let main () : I32.t =
     chk 1l (big + big2 = 1111111110111111111011111111100)
 &&& chk 2l (big2 - big = 864197532086419753208641975320)
 &&& chk 3l (big < big2 - big)
 &&& chk 4l (-big < 0)
 &&& chk 5l (big + z = big)
 &&& chk 6l (big <> big2)
 &&& chk 7l (big2 > big)
