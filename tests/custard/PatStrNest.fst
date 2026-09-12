module PatStrNest

/// Section 48.3.  The negative control for the string-match desugaring.
///
/// [string_match] fires only on a match whose scrutinee is a string and whose
/// every pattern is a bare string constant, a variable or a wildcard.  A
/// string constant *inside* another pattern is not that shape, so it still
/// reaches [krml_pat], which has no karamel pattern to build and refuses.
///
/// Without this, "the krml backend handles string patterns" would be read as
/// a claim about all of them.

module U32 = FStar.UInt32
module I32 = FStar.Int32

let look (o: option string) : U32.t =
  match o with
  | Some "a" -> 1ul
  | Some _ -> 2ul
  | None -> 3ul

let main () : I32.t =
  if look (Some "a") = 1ul then 0l else 1l
