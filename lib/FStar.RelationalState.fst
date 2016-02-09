module FStar.RelationalState
open FStar.Comp
open FStar.Relational
open FStar.Heap

(* Some convenient stateful functions *)
let read_rel1 r = compose2_self read (twice r)
let read_rel2 = compose2_self read
let assign_rel1 r v = compose2_self (fun (a,b) -> write a b) (pair_rel (twice r) v)
let assign_rel2 r v = compose2_self (fun (a,b) -> write a b) (pair_rel r v)
