module StrictArgsUnfoldTest1

noeq
type ordered (a:eqtype) =
{
  leq : a -> a -> bool;
}

[@@strict_on_arguments_unfold [1]]
let leq #a (d : ordered a) : a -> a -> bool = d.leq

let transitivity #a (d : ordered a) (x y z: a):
  Lemma (requires leq d x y /\ leq d y z)
  (ensures leq d x z)
= admit() // p.properties

let rec lower_bounded #a (d : ordered a) (l: list a) m: GTot bool =
  match l with
  | [] -> true
  | t::q -> leq d m t && lower_bounded d q m

(* Used to fail with:
      Failure("Impossible: locally nameless; got t#6")
*)
let rec lower_bounded_trans #a (d : ordered a) (l: list a) m1 m2:
  Lemma (requires lower_bounded d l m1 /\ leq d m2 m1)
        (ensures lower_bounded d l m2)
= match l with
  | [] -> ()
  | t::q -> (transitivity d m2 m1 t; lower_bounded_trans d q m1 m2)
