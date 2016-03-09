module Sample
open Bijection
open FStar.Relational
open FStar.Heap
open FStar.Comp

(* sample two random values such that they are related by a bijection f *)
assume val sample : #a:Type -> #b:Type
                    -> f:(a -> Tot b){good_sample_fun f}
                    -> ST2 (rel a  b)
                           (requires (fun h      -> True))
                           (ensures  (fun h r h' -> R.r r = f (R.l r)
                                                 /\ and_irel (rel_map2T equal h h')))
