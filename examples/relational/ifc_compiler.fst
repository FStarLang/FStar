(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15;
    other-files:set.fsi heap.fst st.fst all.fst st2.fst distinct.fst ifc_ts.fst
  --*)

module Compiler

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

type workaround_bug_404 (u:unit)

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
    let l = max l1 l2 in
    let s1 = sub_exp l1 l p1 in 
    let s2 = sub_exp l2 l p2 in 
    (| l, convert_exp l (bin_op_exp l s1 s2) |)


(* Typechecking commands: we typecheck in a given context *)
val tc_com : l:label -> c:com -> Tot (option (ni_com l)) (decreases c)
let rec tc_com l c = 
  match c with 

  | Skip -> Some (sub_com top l skip_com)

  | Assign x e -> 
    let lx = label_fun x in 
    if l <= lx then
      let (| l', ni_e |) = tc_aexp e in 
      if l' <= lx then 
        let ni_e' = sub_exp l' lx ni_e in 
        let ni_as = convert_com lx (assign_com x ni_e') in 
        Some (sub_com lx l ni_as)
      else
        None
    else
      None

  | Seq c1 c2 ->
    let r1 = tc_com l c1 in   
    let r2 = tc_com l c2 in 
    if is_None r1 || is_None r2 then
      None
    else
      Some (convert_com l (seq_com l (Some.v r1) (Some.v r2)))

  | If e ct cf -> 
    let (| l1', r1' |) = tc_aexp e in
    let l1 = max l1' l in 
    let r1 = sub_exp l1' l1 r1' in
    let r2 = tc_com l1 ct in 
    let r3 = tc_com l1 cf in 
    if is_None r2 || is_None r3 then
      None
    else
      let s = cond_com l1 r1 (Some.v r2) (Some.v r3) in 
      Some (sub_com l1 l s)

  | While e cb -> 
    let (| l1', r1' |) = tc_aexp e in
    let l1 = max l1' l in 
    let r1 = sub_exp l1' l1 r1' in
    let r2 = tc_com l1 cb in 
    if is_None r2 then 
      None
    else
      let s = loop_com l1 r1 (Some.v r2) in 
      Some (sub_com l1 l s)

val tc : com -> option ni
let tc = tc_com bot
