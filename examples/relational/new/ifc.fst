module Ifc

open Rel
open WhileLanguage
open FStar.Heap

(****************************** Preliminaries ******************************)

type label =
| Low
| High

val op_Less : label -> label -> Tot bool
let op_Less l1 l2 =
  match l1, l2 with
  | Low,High -> true
  | _, _ -> false

val op_Less_Equals : label -> label -> Tot bool
let op_Less_Equals l1 l2 =
  match l1, l2 with
  | High,Low -> false
  | _, _ -> true

type label_fun = ref int -> Tot label

type low_equiv (env:label_fun) (h1:rel heap) = 
  forall (x:ref int). env x = Low ==> sel (R.l h1) x = sel (R.r h1) x


(**************************** Typing Judgements ****************************)

(* env |- e : l
   - Expressions do not modify the heap
   - Correctness
   - Low equivalent input heaps + Low label ==> same result 
*)

type ni_exp (env:label_fun) (e:exp) (l:label) = 
  forall (h: (rel heap)).
   (low_equiv env h /\ is_Low l) ==> 
     (interpret_exp (R.r h) e = interpret_exp (R.l h) e)

(* env,pc:l |- c
   - References with a label below l are not modified
   - Total correctness
   - Low equivalent input heaps ==> Low equivalet output heaps 
*)
type ni_com' (env:label_fun) (c:com) (l:label) (h0:(rel heap)) = 
    (fun o_l -> 
    (fun o_r -> 
      (forall r. (env r < l) 
      ==> ((is_Some o_l 
        ==> b2t (sel (R.l h0) r = sel (Some.v o_l) r))
       /\ (is_Some o_r
        ==> b2t (sel (R.r h0) r = sel (Some.v o_r) r))))
     /\ ((is_Some o_l /\ is_Some o_r) 
      ==> (low_equiv env h0 
        ==> low_equiv env (R (Some.v o_l) (Some.v o_r)))))
      (interpret_com (R.r h0) c))
      (interpret_com (R.l h0) c)

type ni_com (env:label_fun) (c:com) (l:label) = 
    forall (h0:(rel heap)). ni_com' env c l h0


(*********************** Typing Rules for Expressions **********************)

(* Subtyping rule for expression labels

         E |- e : l1   l1 <= l2
         ----------------------
              E |- e : l2
*)

val sub_exp : env:label_fun -> e:exp -> l1:label -> l2:label{l1 <= l2} ->
  Lemma (requires (ni_exp env e l1))
        (ensures  (ni_exp env e l2))
let sub_exp _ _ _ _ = ()



(* Typing rule for dereferencing

         label_fun(r) = l
         ----------------
             r : l
*)

val avar_exp : env:label_fun -> r:id -> 
  Lemma (requires True)
        (ensures  (ni_exp env (AVar r) (env r))) 
let avar_exp _ _ = ()


(* Typing rule for Int constants

         i : int
         -------
         i : Low
*)
val aint_exp : env:label_fun -> i:int -> 
  Lemma (requires True)
        (ensures (ni_exp env (AInt i) Low))
let aint_exp _ _ = ()


(* Typing rule for binary operators

          e1 : l   e2 : l
          ----------------
          e1 `op` e2  : l
*)

val binop_exp : env:label_fun -> op:binop -> e1:exp -> e2:exp -> l:label ->
  Lemma (requires (ni_exp env e1 l) /\ (ni_exp env e2 l))
        (ensures  (ni_exp env (AOp op e1 e2) l))
let binop_exp _ _ _ _ _ = ()


(************************ Typing Rules for Commands ************************)

(* Subtyping rule for commands

         env,pc:l1 |- c   l2 <= l1
        ---------------------------
               env,pc:l2 |- c
*)

val sub_com : env:label_fun -> c:com -> l1:label -> l2:label{l2 <= l1} -> 
  Lemma (requires (ni_com env c l1 ))
        (ensures  (ni_com env c l2 ))
let sub_com _ _ _ _ = ()


(* Typing rule for assignment

         env |- e : env(r)    l <= env(r)
         --------------------------------
                  l |- r := e
*)
val assign_com : env:label_fun -> e:exp -> r:id -> 
  Lemma (requires (ni_exp env e (env r)))
        (ensures  (ni_com env (Assign r e) (env r)))
let assign_com _ _ _ = ()

(* Sequencing rule for commands

         env,pc:l |- c1  env,pc:l |- c2
         ------------------------------
               env,pc:l |- c1; c2
*)

val seq_com' : env:label_fun -> c1:com -> c2:com -> l:label -> h0:(rel heap) -> h1:(rel heap) -> 
  Lemma (requires (ni_com' env c1 l h0 /\ ni_com' env c2 l h1 /\
          (fun o_l -> (is_Some o_l) ==> equal (Some.v o_l) (R.l h1))
            (interpret_com (R.l h0) c1)
      /\  (fun o_r -> (is_Some o_r) ==> equal (Some.v o_r) (R.r h1))
            (interpret_com (R.r h0) c1)))
        (ensures  (ni_com' env (Seq c1 c2) l h0)) 
let seq_com' _ _ _ _ _ _ = ()

(*
val seq_com : env:label_fun -> c1:com -> c2:com -> l:label -> 
  Lemma (requires (ni_com env c1 l /\ ni_com env c2 l))
        (ensures  (ni_com env (Seq c1 c2) l)) 
let seq_com env c1 c2 l = 
*)

(* Conditional rule for commands

         env |- e : l   env,pc:l |- ct   env,pc:l |- cf
         ----------------------------------------------
             env,pc:l |- if e <> 0 then ct else cf
*)

val cond_com : env:label_fun -> e:exp -> ct:com -> cf:com -> l:label ->
  Lemma (requires ((ni_exp env e l) /\ (ni_com env ct l) /\ (ni_com env cf l)))
         (ensures  (ni_com env (If e ct cf) l))
let cond_com _ _ _ _ _ = ()

(* Typing rule for Skip

         -------------------
         env,pc:High |- skip
*)

val skip_com : env:label_fun ->
  Lemma (ni_com env Skip High)
let skip_com _ = ()

(* While rule for commands

         env |- e : l          env,pc:l |- c
         -----------------------------------
          env,pc:l |- while (e <> 0) do c
*)

(* This needs a high timeout *)
val loop_com : env:label_fun -> e:exp -> c:com -> v:variant -> l:label -> h:(rel heap) -> 
  Lemma (requires (ni_exp env e l /\ ni_com env c l))
        (ensures  (ni_com' env (While e c v) l h)) 
        (decreases ((interpret_exp (R.l h) v) + interpret_exp (R.r h) v))
let rec loop_com env e c v l h = 
  // Interpret the body
  let o_l = interpret_com (R.l h) c in 
  let o_r = interpret_com (R.r h) c in 

  // Case analysis on termination of bodies
  match is_Some o_l, is_Some o_r with
  | true , true  -> 
    begin
      let hl = Some.v o_l in 
      let hr = Some.v o_r in 
      // case analysis on decreasing of variant
      match (interpret_exp (R.r h) v > interpret_exp hr v), 
        (interpret_exp (R.l h) v > interpret_exp hl v) with
      | true , true  -> loop_com env e c v l (R hl hr)
      | true , false -> loop_com env e c v l (R (R.l h) hr)
      | false , true -> loop_com env e c v l (R hl (R.r h) )
      | false, false -> ()
    end
  | true , false -> 
    let hl = Some.v o_l in 
    if (interpret_exp (R.l h) v > interpret_exp hl v) then
      loop_com env e c v l (R hl (R.r h))
  | false, true  -> 
    let hr = Some.v o_r in 
    if (interpret_exp (R.r h) v > interpret_exp hr v) then
      loop_com env e c v l (R (R.l h) hr)
  | false, false -> ()
