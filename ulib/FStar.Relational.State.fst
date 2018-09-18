module FStar.Relational.State
open FStar.Relational.Relational
open FStar.Relational.Comp
open FStar.Heap
open FStar.Ref

(* Some convenient stateful functions *)
let read_rel1 r = compose2_self read (twice r)
let read_rel2 = compose2_self read
let assign_rel1 r v = compose2_self #_ #_ #_ (fun (a, b) -> write a b) (pair_rel (twice r) v)
let assign_rel2 r v = compose2_self #_ #_ #_ (fun (a, b) -> write a b) (pair_rel r v)

