(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15;
    other-files:set.fsi heap.fst st.fst all.fst st2.fst distinct.fst ifc_ts.fst
  --*)

module Interpreter

open IFC
open FStar.Comp
open FStar.Relational
open FStar.Heap

type binop =
| Plus
(*
| Minus
| Times
*)

type id = ref int

type aexp =
| AInt : int -> aexp
| AVar : id -> aexp 
| AOp  : binop -> aexp -> aexp -> aexp 

(*
type bexp =
| BTrue  : bexp
| BFalse : bexp
| BEq    : aexp -> aexp -> bexp
| BLe    : aexp -> aexp -> bexp
| BNot   : bexp -> bexp
| BAnd   : bexp -> bexp -> bexp
*)

(* Commands (aka. statements) *)
type com =
| Skip   : com
| Assign : var:id -> term:aexp -> com
| Seq    : first:com -> second:com -> com
(*
| If     : cond:bexp -> then_branch:com -> else_branch:com -> com
| While  : cond:bexp -> body:com -> com
*)
| If     : cond:aexp -> then_branch:com -> else_branch:com -> com
| While  : cond:aexp -> body:com -> com


(* Typechecking expressions: we infer the label *)
val tc_aexp : e:aexp -> Tot (l:label & ni_exp l)
let rec tc_aexp e = 
  match e with 
  | AInt i -> (| bot,(const_exp i) |)
  | AVar r -> (| label_fun r, (deref_exp r) |) 
  | AOp o e1 e2 -> 
    (* This style triggers a lot of weird bugs... *)
    (* let r1, r2 = tc_aexp e1, tc_aexp e2 in  *)
    let r1 = tc_aexp e1 in
    let r2 = tc_aexp e2 in 
    let (| l1, p1 |) = r1 in 
    let (| l2, p2 |) = r2 in 
    let l = if l1 <= l2 then l2 else l1 in
    let s1 = sub_exp l1 l p1 in 
    let s2 = sub_exp l2 l p2 in 
    (| l, convert l (bin_op_exp l s1 s2) |)
