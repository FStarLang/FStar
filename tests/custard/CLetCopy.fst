module CLetCopy
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* Section 129: a tuple that is built and then immediately taken apart should
   leave neither behind.  The fold that does that asks two questions of a
   binding -- is the definition a constructor whose fields are all cheap to
   re-evaluate, and is the name read only by matches on it -- and a copy
   sitting between the two answers the second one wrongly.

   F* inserts exactly such a copy.  A [let (a, (b, ())) = p] whose scrutinee
   is already a variable elaborates to [let _letpattern = p in match
   _letpattern with ...], so inlining [use_pair] here puts the copy between
   the constructor and the match that consumes it.  Read top-down, [p] is no
   longer destructed-only -- the copy's right-hand side is a bare use of it --
   and [_letpattern] is not a constructor, so neither binding folds and the
   tuple is materialized in full.

   Nested tuples ending in [unit] are what a type-level fold over a list of
   descriptors produces, so this is the shape a DSL that indexes a resource
   by such a list hands to every one of its entry points. *)

inline_for_extraction noextract
let use_pair (p : U32.t & (U32.t & unit)) : U32.t =
  let (a, (b, ())) = p in
  U32.add_mod (U32.mul_mod a 2ul) b

(* [p] is named rather than written at the call site: the copy is what F*
   inserts in front of a match whose scrutinee is *already a variable*, so
   passing the constructor directly would substitute it and never make one.
   [x] is a parameter so that nothing here is constant-folded away and the
   constructor really does meet the match inside a function body. *)
let combine (x : U32.t) : U32.t =
  let p = (U32.mul_mod x x, (U32.add_mod x 1ul, ())) in
  use_pair p

let main () : ML I32.t =
  if U32.eq (combine 3ul) 22ul then 0l else 1l
