(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Relational.fst
  --*)

module While

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

module IFC

(* We model a simple IFC Type system *)
open FStar.Comp
open FStar.Heap
open While
open FStar.Relational

(****************************** Preliminaries ******************************)

(* We model labels with different levels as integers *)


(* A top label that is higher than all other labels *)
let top = 1000

(* A bottom label that is lower than all other labels *)
let bot = - top

type label = l:int{bot <= l /\ l <= top}

(* Label of the attacker *)
assume val alpha : label

(* A global labeling function (assigns a label to every reference) *)
assume val label_fun : ref int -> Tot label

(* A reference can be observed by the attacker if its label is not higher than
   alpha *)
let attacker_observable x = label_fun x <= alpha

(* We have alpha equivalence when two heaps are equal for all references that
  have a label <= alpha and thus are observable by the attacker *)
type a_equiv (h1:double heap) = 
  (forall (x:ref int). attacker_observable x 
                       ==> sel (R.l h1) x = sel (R.r h1) x)

(* Function to create new labeled references *)
assume val new_labeled_int : l:label -> x:ref int{label_fun x = l}

let tu = twice ()

let max l1 l2 = if l1 <= l2 then l2 else l1
let min l1 l2 = if l1 <= l2 then l1 else l2


(**************************** Typing Judgements ****************************)

(* typing judgement  e : l
   - Expressions do not modify the heap
   - If we have alpha equivalence on the input heaps, then the results must be
     equal if the expression label is lower than or equal to alpha *)
type ni_exp (ae:aexp) (l:label) =
              double unit ->
              ST2 (double int)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 r h2 -> equal (R.l h1) (R.l h2)
                                         /\ equal (R.r h1) (R.r h2)
                                         /\ R.l r = interpret_exp (R.l h1) ae
                                         /\ R.r r = interpret_exp (R.r h1) ae
                                         /\ (a_equiv h1
                                            ==> (if l <= alpha then
                                                  R.l r = R.r r
                                                else
                                                  true))))

(* typing judgement  l |- c
   - references with a label below l are not modified
   - alpha equivalence on input heaps implies alpha equivalence on output
     heaps *)
type ni_com (c:com) (l:label) =
              double unit ->
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int).
                                              label_fun y < l
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ R.l h2 = interpret_com (R.l h1) c
                                         /\ R.r h2 = interpret_com (R.r h1) c
                                         /\ (a_equiv h1 ==> a_equiv h2)))

(* We define noninterference for a program as noninterference for commands with
   the label bottom *)
type ni (c:com) = ni_com c bot

(*********************** Typing Rules for Expressions **********************)

(* Subtyping rule for expression labels

         e : l1   l1 <= l2
         -----------------
             e : l2
*)
val sub_exp : ae:aexp -> l1:label -> l2:label{l1 <= l2} -> =e1:(ni_exp ae l1) -> Tot (ni_exp ae l2)
let sub_exp _ _ _ e1 tu = e1 tu

(* Typing rule for dereferencing

         label_fun(r) = l
         ----------------
             !r : l
*)
val deref_exp : r:ref int -> Tot (ni_exp (AVar r) (label_fun r)) 
let deref_exp r tu = compose2_self read (twice r) 
(* Typing rule for Int constants

         i : int
         -------
         i : bot
*)
val const_exp : i:int -> Tot (ni_exp (AInt i) bot)
let const_exp i tu = twice i

(* Typing rule for binary operators (we write the rule only for "+", but other
   binarry operators work analogously

          e1 : l   e2 : l
          ---------------
           e1 + e2  : l
*)
val bin_op_exp : ae1:aexp -> ae2:aexp -> l:label -> =e1:(ni_exp ae1 l) -> =e2:(ni_exp ae2 l)
                 -> Tot (ni_exp (AOp Plus ae1 ae2) l) 
let bin_op_exp _ _ _ e1 e2 tu = (fun tu -> compose2_self (fun (a, b) -> a + b) (pair_rel (e1 tu) (e2 tu))) tu


(************************ Typing Rules for Commands ************************)

(* Subtyping rule for commands

         l1 |- c   l2 <= l1
         ------------------
              l2 |- c
*)
val sub_com : c:com ->  l1:label -> l2:label{l2 <= l1} -> =c1:(ni_com c l1) -> Tot (ni_com c l2)
let sub_com _ _ _ c1 tu = c1 tu

(* Typing rule for assignment

         e : l'      label_fun(r) = l'      l' >= l
         ------------------------------------------
                       l |- r := e
*)
val assign_com : ae:aexp -> r:ref int -> =e:ni_exp ae (label_fun r) -> Tot (ni_com (Assign r ae) (label_fun r)) 
let assign_com _ r e tu = compose2_self (write r) (e tu)

(* Sequencing rule for commands

         l |- c1    l |- c2
         ------------------
            l |- c1; c2
*)
val seq_com : com1:com -> com2:com -> l:label -> =c1:(ni_com com1 l) -> =c2:(ni_com com2 l) -> Tot(ni_com (Seq com1 com2) l) 
let seq_com _ _ _ c1 c2 tu = let _ = c1 tu in c2 tu

(* Conditional rule for commands

         e : l     l |- ct      l |- cf
         ------------------------------
         l |- if e <> 0 then ct else cf
*)
val cond_com : ae:aexp -> comt:com -> comf:com -> l:label -> =e:(ni_exp ae l) -> =ct:(ni_com comt l) -> =cf:(ni_com comf l) -> Tot (ni_com (If ae comt comf) l)
let cond_com _ _ _ _ e ct cf tu  = match e tu with
                             | R 0 0 -> cf tu
                             | R 0 _ -> cross cf ct
                             | R _ 0 -> cross ct cf
                             | R _ _ -> ct tu


(* Typing rule for Skip

         -----------
         top |- skip
*)

val skip_com : ni_com Skip top
let skip_com tu = tu

(*
(* Loop case of a while loop *)
val loop_loop : l:label -> =e:(ni_exp l) -> =c:(ni_com l)
(*        -> Tot (ni_com l) *)
(* This fails because of bug #379 *)
           -> double unit ->
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int).
                                              label_fun y < l
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))

(* While rule for commands

         e : l               l |- c
         --------------------------
         l |- while (e <> 0) do {c}
*)
val loop_com : l:label -> =e:(ni_exp l) -> =c:(ni_com l)
(*            -> Tot (ni_com l) *)
(* This fails because of bug #379 *)
           -> double unit ->
              ST2 (double unit)
                  (requires (fun h2 -> True))
                  (ensures  (fun h1 _ h2 -> (forall (y:ref int).
                                              label_fun y < l
                                              ==> sel (R.l h1) y = sel (R.l h2) y
                                               /\ sel (R.r h1) y = sel (R.r h2) y)
                                         /\ (a_equiv h1 ==> a_equiv h2)))
let rec loop_com l e c tu =
                  match e tu with
                 | R 0 0 -> skip_com tu
                 | R 0 _ -> cross skip_com (loop_loop l e c)
                 | R _ 0 -> cross (loop_loop l e c) skip_com
                 | R _ _ -> loop_loop l e c tu
and loop_loop l e c tu = let _ = c tu in loop_com l e c tu
*)

type workaround_bug_404 (u:unit)

(* Typechecking expressions: we infer the label *)
val tc_aexp : e:aexp -> Tot (l:label & ni_exp e l)
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
    let s1 = sub_exp e1 l1 l p1 in 
    let s2 = sub_exp e2 l2 l p2 in 
    (| l, bin_op_exp e1 e2 l s1 s2 |)

(* Typechecking commands: we typecheck in a given context *)
val tc_com : l:label -> c:com -> Tot (option (ni_com c l)) (decreases c)
let rec tc_com l c = 
  match c with 

  | Skip -> Some (sub_com c top l skip_com)

  | Assign x e -> 
    let lx = label_fun x in 
    if l <= lx then
      let (| l', ni_e |) = tc_aexp e in 
      if l' <= lx then 
        let ni_e' = sub_exp e l' lx ni_e in 
        let ni_as = assign_com e x ni_e' in 
        Some (sub_com c lx l ni_as)
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
      Some (seq_com c1 c2 l (Some.v r1) (Some.v r2))

  | If e ct cf -> 
    let (| l1', r1' |) = tc_aexp e in
    let l1 = max l1' l in 
    let r1 = sub_exp e l1' l1 r1' in
    let r2 = tc_com l1 ct in 
    let r3 = tc_com l1 cf in 
    if is_None r2 || is_None r3 then
      None
    else
      let s = cond_com e ct cf  l1 r1 (Some.v r2) (Some.v r3) in 
      Some (sub_com c l1 l s)

(*
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
*)

val tc : c:com -> option (ni c)
let tc = tc_com bot
