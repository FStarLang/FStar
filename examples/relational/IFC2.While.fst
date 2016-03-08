module IFC2.While

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
//| While  : cond:aexp -> body:com -> com


val interpret_exp : h:heap -> e:aexp -> Tot int
let rec interpret_exp h e = 
  match e with
  | AInt i -> i
  | AVar x -> sel h x
  | AOp o e1 e2 -> 
    let r1 = interpret_exp h e1 in 
    let r2 = interpret_exp h e2 in 
    match o with 
    | Plus -> r1 + r2

val interpret_com : h:heap -> c:com -> Tot heap (decreases c)
let rec interpret_com h c = 
  match c with
  | Skip -> h
  | Assign x e -> upd h x (interpret_exp h  e)
  | Seq c1 c2 -> 
    let h' = interpret_com h c1 in 
    interpret_com h' c2
  | If e ct cf -> 
    if (interpret_exp h e) <> 0 then
      interpret_com h ct
    else
      interpret_com h cf

val interpret_exp_st : e:aexp -> ST int (requires (fun _ -> True))
                                        (ensures  (fun h r h' -> equal h h' 
                                                              /\ r =  interpret_exp h e))
let rec interpret_exp_st e =
  match e with
  | AInt i -> i
  | AVar x -> !x
  | AOp o e1 e2 -> 
    let r1 = interpret_exp_st e1 in 
    let r2 = interpret_exp_st e2 in 
    match o with 
    | Plus -> r1 + r2

val interpret_com_st : c:com -> ST unit (requires (fun _ -> True))
                                        (ensures  (fun h _ h' -> equal h' (interpret_com h c)))
let rec interpret_com_st c = 
  match c with
  | Skip -> ()
  | Assign x e -> x := (interpret_exp_st e)
  | Seq c1 c2 -> 
    interpret_com_st c1;
    interpret_com_st c2
  | If e ct cf -> 
    if (interpret_exp_st e) <> 0 then
      interpret_com_st ct
    else
      interpret_com_st cf

