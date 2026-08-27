module A

(* Mirrors FStar.Pervasives.false_elim: only declared here, defined in A.fst by
   a recursive equation that unfolds to itself forever. *)
val absurd (#a: Type) (_: squash False) : Tot a

(* Any single inline_for_extraction definition in an *interface* puts the module
   in Dep.interfaces_with_inlining, so cross-module inlining loads A.fst when
   extracting a client and A's definitions become delta-unfoldable there.
   FStar.Pervasives.fsti is in exactly this situation because of coerce_eq. *)
inline_for_extraction noextract
let coerce (#a #b: Type) (_: squash (a == b)) (x: a) : b = x
