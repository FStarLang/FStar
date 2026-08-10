module ExtIntNe

/// `FStar.IntN.ne` / `FStar.UIntN.ne` (also spelled `<>^`).
///
/// `mk_op` in src/extraction/FStarC.Extraction.Krml.fst maps `eq` to the `Eq`
/// opcode but has no case for `ne`, even though the Krml AST has a `Neq`
/// opcode. So `x <>^ y` survives extraction as a call to `FStar_UInt32_ne`,
/// which is *declared* in krmllib's headers but defined nowhere:
///
///   - C: the emitted code fails to compile/link
///     (`implicit declaration of function 'FStar_Int32_ne'`, and no symbol in
///     libkrmllib.a).
///   - Rust: `krml -backend rust` reports
///     `unexpected: [type] no casts in Low* -> Rust` and then writes a .rs
///     file with the enclosing function silently *missing*.
///
/// Both backends are therefore excluded in the Makefile. The OCaml column does
/// exercise this file, and once `mk_op` learns about `ne` the two entries can
/// be dropped from NO_C / NO_RUST.

module I8  = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let a32 : I32.t = 3l
let b32 : I32.t = 4l
let a32' : I32.t = 3l

let main () : I32.t =
     chk 1l (I32.ne a32 b32)
 &&& chk 2l (not (I32.ne a32 a32'))
 &&& chk 3l (I8.ne  3y 4y)
 &&& chk 4l (I16.ne 3s 4s)
 &&& chk 5l (I64.ne 3L 4L)
 &&& chk 6l (U8.ne  3uy 4uy)
 &&& chk 7l (U16.ne 3us 4us)
 &&& chk 8l (U32.ne 3ul 4ul)
 &&& chk 9l (U64.ne 3uL 4uL)
     (* the infix spelling unfolds to the same function *)
 &&& chk 10l (I32.(a32 <>^ b32))
 &&& chk 11l (U32.(3ul <>^ 4ul))
