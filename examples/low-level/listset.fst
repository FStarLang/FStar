(*--build-config
    options:--admit_fsi FStar.List --admit_fsi FStar.Set;
    other-files:set.fsi ext.fst heap.fst st.fst all.fst list.fsi
  --*)

(** Some extra helper functions for lists. *)

module ListSet

open FStar.List

(** [lsubset la lb] is true if and only if all the elements from [la]
    are also in [lb]. *)
val lsubset: #a:Type -> list a -> list a -> Tot bool
let rec lsubset la lb =
match la with
| [] -> true
| h :: tl ->  ((mem h lb) && (lsubset tl lb))

val notIn : #a:Type -> a -> list a -> Tot bool
let notIn id l = not (mem id l)

val noRepeats : #a:Type -> list a -> Tot bool
let rec noRepeats la =
match la with
| [] -> true
| h :: tl ->  ((notIn h tl) && (noRepeats tl))
