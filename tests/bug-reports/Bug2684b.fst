module Bug2684b

open FStar.Tactics

assume val nat_dep: nat -> Type0

assume val complex_type: ty:Type0 -> (#[exact (`())] _ : unit) -> l:nat -> nat_dep l -> Type0

assume val a_function: #ty:Type0 -> (#[exact (`())] _ : unit) -> #x:nat -> #y:nat_dep x -> z:complex_type ty x y -> x':nat & y':nat_dep x' & complex_type ty x' y'

val a_lemma: #ty:Type0 -> (#[exact (`())] _ : unit) -> #x:nat -> #y:nat_dep x -> z:complex_type ty x y -> unit
let rec a_lemma #ty #tc #x #y z =
  let (|_, _, _|) = a_function z in
  ()
