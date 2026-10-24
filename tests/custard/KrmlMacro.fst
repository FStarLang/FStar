module KrmlMacro

module I32 = FStar.Int32
module U32 = FStar.UInt32

/// Section 45.2.  A C decoration on an [assume val], through the karamel
/// backend.
///
/// The [DExternal] was built with no flags at all, so [@@CMacro] -- and every
/// other C decoration an [assume val] can carry -- was dropped on the way out.
/// karamel therefore took the symbol for an ordinary function and spelled the
/// call with the function's name, not the macro's, so nothing the target
/// supplies matched it.
///
/// The test is that the result links and runs.

[@@CMacro]
assume val double (x : U32.t) : U32.t

let main () : I32.t = if U32.eq (double 5ul) 10ul then 0l else 1l
