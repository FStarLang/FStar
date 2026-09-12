module KrmlPrims
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

/// Section 65.1.  The declarations Custard compiles whose lident karamel
/// already has a definition for.
///
/// karamel prepends its own [Prims] to every program, and that [Prims]
/// defines [list] and [dtuple2].  Custard is whole-program and compiles both
/// from their F* sources, so two definitions arrive under one lident and they
/// do not agree: karamel's [dtuple2] has fields [fst] and [snd] where F*'s
/// has [_1] and [_2], and its [list] has constructors [Nil] and [Cons] where
/// Custard's are mangled.  EverParse hit the first; the second came out of
/// fixing it.
///
/// Both are here because the collision is not per-type: it is that a
/// whole-program compiler and a per-module one disagree about who owns
/// [Prims].  The program checks its own answers, because the failure this
/// guards against is karamel silently resolving a reference to the *other*
/// definition, which is a wrong field and not a missing one.

let pair (x:U32.t) : (y:U32.t & U32.t) = (| x, U32.add_mod x x |)

let rec tally (l : list U32.t) : U32.t =
  match l with
  | [] -> 0ul
  | h :: rest -> U32.add_mod h (tally rest)

let main () : ML I32.t =
  let p = pair 3ul in
  (* [dfst] and [dsnd] are different projections, so a definition whose fields
     have been swapped or conflated shows up here and would not show up in a
     grep for either name. *)
  let ok1 = U32.eq (dfst p) 3ul in
  let ok2 = U32.eq (dsnd p) 6ul in
  let ok3 = U32.eq (tally [1ul; 2ul; 3ul]) 6ul in
  let ok4 = U32.eq (tally []) 0ul in
  if ok1 && ok2 && ok3 && ok4 then 0l else 1l
