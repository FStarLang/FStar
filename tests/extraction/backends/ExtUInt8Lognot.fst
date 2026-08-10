module ExtUInt8Lognot

/// `FStar.UInt8.lognot` in the OCaml backend. **Known bug, XFAIL_OCAML.**
///
/// `FStar.UInt8` is the only machine-integer module whose OCaml realization is
/// written by hand (ulib/ml/app/FStar_UInt8.ml); UInt16/32/64 and Int8/../64
/// are generated from ulib/ml/app/ints/FStar_Ints.ml.body on top of Stdint.
/// The hand-written file represents a `uint8` as a plain OCaml `int` and masks
/// the result of every operation that can leave the range... except `lognot`:
///
///     let lognot (a:uint8) : uint8 = lnot a          (* missing `land 255` *)
///
/// So `FStar.UInt8.lognot 0uy` evaluates to `-1` at runtime while F* proves it
/// is `255uy`. This is a *silent wrong value*: nothing crashes, the value is
/// simply not the one that was verified, and it is not even a representable
/// `uint8`, so every subsequent comparison, cast and `to_string` is wrong too.
/// Since F* will happily prove `UInt8.v (UInt8.lognot 0uy) = 255`, the bad
/// value can be laundered into an out-of-bounds index.
///
/// The fix is a one-liner in ulib/ml/app/FStar_UInt8.ml. The same file is also
/// missing `ne`, `shift_arithmetic_right`, `of_int`, `to_native_int`,
/// `of_native_int`, `len` and `zeroes` compared to its generated siblings.
///
/// The C and Rust backends get this right (`~x` on a `uint8_t` is truncated
/// back on assignment), so they are *not* excluded.

module U8  = FStar.UInt8
module I32 = FStar.Int32

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let zero8 : U8.t = 0uy
let max8  : U8.t = 255uy
let lo8   : U8.t = 0x0fuy

let main () : I32.t =
     chk 1l (U8.eq (U8.lognot zero8) 255uy)
 &&& chk 2l (U8.eq (U8.lognot max8) 0uy)
 &&& chk 3l (U8.eq (U8.lognot lo8) 0xf0uy)
     (* the bad value is not even in range, so ordering breaks too *)
 &&& chk 4l (U8.gt (U8.lognot zero8) 0uy)
 &&& chk 5l (U8.lte (U8.lognot zero8) 255uy)
