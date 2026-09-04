module RustTup
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

/// Section 54.1.  Tuples on the Rust leg.
///
/// [PrintKrml.is_tuple_type_name] and [is_tuple_ctor_name] send a tuple to
/// karamel's *native* tuple node on KrmlRust and to the monomorphized struct
/// name on KrmlC.  That is right on both, and it had a test on neither side
/// of the split until now -- the KrmlC spelling was pinned, the Rust one was
/// not, because nothing in this directory produced Rust.
///
/// Run with [-fkeep-tuples], which is what makes karamel leave the native
/// tuple alone rather than monomorphizing it back into a struct; without it
/// this test would pass while checking nothing about the Rust spelling.
///
/// Deliberately no *global* of tuple type: with [-fkeep-tuples] karamel's
/// Rust backend fails to translate one ("Unexpected EAny"), omits it from the
/// crate, and exits 0 while emitting code that still refers to it (section
/// 54.2).  That is a karamel defect, not a Custard one -- the stock
/// [--codegen krml] pipeline does the same -- and the point of the leg is
/// that it is now caught rather than shipped.

let swap (p : U32.t & U32.t) : U32.t & U32.t = (snd p, fst p)

let sum (p : U32.t & U32.t) : U32.t = U32.add_mod (fst p) (snd p)

let main () : ML I32.t =
  let p = (1ul, 2ul) in
  let q = swap p in
  if U32.eq (fst q) 2ul && U32.eq (snd q) 1ul && U32.eq (sum p) 3ul
  then 0l else 1l
