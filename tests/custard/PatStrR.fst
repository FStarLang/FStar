module PatStrR
module U32 = FStar.UInt32

/// Section 50.2.  The same string match as [PatStrKrml.classify], for
/// karamel's *Rust* backend.
///
/// The if-chain section 48.3 desugars to compares with krmllib's
/// [__eq__Prims_string], which is C and has no Rust counterpart.  Ungated,
/// the desugaring handed karamel something its Rust backend cannot translate
/// and it crashed with no output file; before section 48.3 the same module
/// got a clean refusal.  The desugaring is now C-only and this is refused
/// again.
///
/// The branches are out of source order for the reason [ChrLit] is: the
/// desugaring is order-sensitive and a test whose branches are sorted cannot
/// see the difference.

let classify (s : string) : U32.t =
  match s with
  | "b" -> 2ul
  | "a" -> 1ul
  | _ -> 3ul

let main () : FStar.Int32.t =
  if U32.eq (classify "a") 1ul then 0l else 1l
