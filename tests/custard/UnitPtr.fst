module UnitPtr
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

/// Section 53.1.  A function passed as a value, at a type C has to spell.
///
/// The C signature of a definition and the C spelling of its type were
/// computed by different code, and they disagreed in two ways.  A [unit]
/// result is [void] in a definition and was [custard_unit] in a type; a
/// [unit] parameter is dropped from a definition and was kept in a type.
/// Neither shows up while every function is only ever *called*, because a
/// call site consults the definition's own tables.  Pass one as a value and
/// the pointer type and the function disagree, in one translation unit, with
/// no Custard diagnostic and a C error about generated names.
///
/// Both shapes are here.  [k] returns unit; [j] returns unit *and* takes one.
/// The suite compiles with -Werror, which is what pins it.

let k (a : U32.t) : ML unit = ()

let j (u : unit) (a : U32.t) : ML unit = ()

let apply (f : U32.t -> ML unit) (n : U32.t) : ML unit = f n

let apply2 (f : unit -> U32.t -> ML unit) (n : U32.t) : ML unit = f () n

let main () : ML I32.t =
  apply k 1ul;
  apply2 j 2ul;
  0l
