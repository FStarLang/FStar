(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module IfcRules

open Rel
open While
open FStar.Heap
open FStar.Classical
open FStar.ST

(****************************** Preliminaries ******************************)

(* CH: Everything specialized to 2-point lattice *)
type label =
| Low
| High

val op_Less : label -> label -> Tot bool
let op_Less l1 l2 =
  match l1, l2 with
  | Low, High -> true
  | _, _      -> false

val op_Less_Equals : label -> label -> Tot bool
let op_Less_Equals l1 l2 =
  match l1, l2 with
  | High, Low -> false
  | _, _      -> true

val join : label -> label -> Tot label
let join l1 l2 =
  match l1, l2 with
  | Low, Low -> Low
  | _, _     -> High

(*
 * function from the addr_of refs to label
 *)
type label_fun = nat -> GTot label

let label_of (env:label_fun) (r:id) :GTot label = env (addr_of r)

type low_equiv (env:label_fun) (h1:rel heap) = 
  forall (x:ref int). label_of env x = Low ==> sel (R?.l h1) x = sel (R?.r h1) x


(**************************** Typing Judgements ****************************)

(* env |- e : l
   - Expressions do not modify the heap
   - Correctness
   - Low equivalent input heaps + Low label ==> same result
*)

type ni_exp (env:label_fun) (e:exp) (l:label) =
  forall (h: rel heap).
   (low_equiv env h /\ Low? l) ==>
     (interpret_exp (R?.r h) e = interpret_exp (R?.l h) e)

(* env,pc:l |- c
   - References with a label below l are not modified
   - Total correctness
   - Low equivalent input heaps ==> Low equivalet output heaps
*)
type ni_com' (env:label_fun) (c:com) (l:label) (h0: rel (option heap)) =
    (Some? (R?.l h0) /\ Some? (R?.r h0) ==>
     (let h0 = R (Some?.v (R?.l h0)) (Some?.v (R?.r h0)) in
      let o_l = interpret_com (R?.l h0) c in
      let o_r = interpret_com (R?.r h0) c in
       ((Some? o_l /\ Some? o_r /\ low_equiv env h0)
          ==> low_equiv env (R (Some?.v o_l) (Some?.v o_r)))))
    /\
    (Some? (R?.l h0) ==>
     (let hl = Some?.v (R?.l h0) in
      let o_l = interpret_com hl c in
        (forall r. (label_of env r < l /\ Some? o_l)
          ==> sel hl r = sel (Some?.v o_l) r)))
    /\
    (Some? (R?.r h0) ==>
     (let hr = Some?.v (R?.r h0) in
      let o_r = interpret_com hr c in
        (forall r. (label_of env r < l /\ Some? o_r)
          ==> sel hr r = sel (Some?.v o_r) r)))

type ni_com (env:label_fun) (c:com) (l:label) =
    forall (h0: rel (option heap)). ni_com' env c l h0


(*********************** Typing Rules for Expressions **********************)

(* CH: The way we derive these rules looks more like a
       semantically-justified program logic than a syntactic type
       system. Any connection to Dave Naumann and Anindya Banerjee's
       "relational logic"? (e.g. https://arxiv.org/abs/1611.08992) *)

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

         ----------------
          E | - r : E(r)
*)

val avar_exp : env:label_fun -> r:id ->
  Lemma (requires True)
        (ensures  (ni_exp env (AVar r) (label_of env r))) 
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

         env |- e : env(r)
         ------------------------
         env, pc:env(r) |- r := e

    - label of expression and context label have to be below label of r
      (first one to prevent explicit, second to prevent implicit flows)
*)
val assign_com : env:label_fun -> e:exp -> r:id -> 
  Lemma (requires (ni_exp env e (label_of env r)))
        (ensures  (ni_com env (Assign r e) (label_of env r)))
let assign_com _ _ _ = ()

(* Sequencing rule for commands

         env,pc:l |- c1  env,pc:l |- c2
         ------------------------------
               env,pc:l |- c1; c2
*)

val seq_com' : env:label_fun -> c1:com -> c2:com -> l:label -> h0: rel (option heap) ->
  Lemma (requires (ni_com env c1 l /\ ni_com env c2 l))
        (ensures  (ni_com' env (Seq c1 c2) l h0))
let seq_com' env c1 c2 l h0 =
  match h0 with
  | R None None -> ()
  | R (Some hl) None -> cut (ni_com' env c2 l (R (interpret_com hl c1) None))
  | R None (Some hr) -> cut (ni_com' env c2 l (R None (interpret_com hr c1)))
  | R (Some hl) (Some hr) -> cut (ni_com' env c2 l (R (interpret_com hl c1) (interpret_com hr c1)))

val seq_com : env:label_fun -> c1:com -> c2:com -> l:label ->
  Lemma (requires (ni_com env c1 l /\ ni_com env c2 l))
        (ensures  (ni_com env (Seq c1 c2) l))
let seq_com env c1 c2 l = forall_intro
     (fun (h0:rel (option heap)) ->
       seq_com' env c1 c2 l h0 <: Lemma (ni_com' env (Seq c1 c2) l h0))

(* Typing rule for conditional commands

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

(* slight variant taking option heap *)
val decr_while : h:(option heap) -> v:variant -> GTot nat
let decr_while h v = match h with
  | None -> 0
  | Some h0 ->
    let tmp = interpret_exp h0 v in
    if 0 > tmp then 0 else tmp

#reset-options "--z3rlimit 30"

val while_com' : env:label_fun -> e:exp -> c:com -> v:variant -> l:label -> h:rel (option heap) ->
  Lemma (requires (ni_exp env e l /\ ni_com env c l))
        (ensures  (ni_com' env (While e c v) l h))
        (decreases (decr_while (R?.l h) v + decr_while (R?.r h) v))
let rec while_com' env e c v l h =
  // Interpret the body
  match h with
  | R None None -> ()
  | R (Some h_l) None ->
  begin
    let o_l = interpret_com h_l c in
    match o_l with
    | Some hl ->
      if (interpret_exp h_l v > interpret_exp hl v) && interpret_exp hl v >= 0 then
        while_com' env e c v l (R o_l None)
      else
        ()
    | None  -> ()
  end
  | R None (Some h_r) ->
  begin
    let o_r = interpret_com h_r c in
    match o_r with
    | Some hr ->
      if (interpret_exp h_r v > interpret_exp hr v) && interpret_exp hr v >= 0 then
        while_com' env e c v l (R None o_r)
      else
        ()
    | None  -> ()
  end
  | R (Some h_l) (Some h_r) ->
  begin
    let o_l = interpret_com h_l c in
    let o_r = interpret_com h_r c in

    (* Case analysis on termination of bodies *)
    match o_l, o_r with
    | Some hl , Some hr  ->
      begin
        // case analysis on decreasing of variant
        match (interpret_exp h_l v > interpret_exp hl v) && interpret_exp hl v >= 0 ,
          (interpret_exp h_r v > interpret_exp hr v) && interpret_exp hr v >= 0 with
        | true , true  -> while_com' env e c v l (R o_l o_r)
        | true , false -> while_com' env e c v l (R o_l (Some h_r))
        | false , true -> while_com' env e c v l (R (Some h_l) o_r )
        | false, false -> ()
      end
    | Some hl , None ->
      if (interpret_exp h_l v > interpret_exp hl v) && interpret_exp hl v >= 0 then
        while_com' env e c v l (R o_l (Some h_r))
    | None , Some hr  ->
      if (interpret_exp h_r v > interpret_exp hr v) && interpret_exp hr v >= 0 then
        while_com' env e c v l (R (Some h_l) o_r)
    | None, None -> ()
  end

#reset-options

val while_com : env:label_fun -> e:exp -> c:com -> v:variant -> l:label ->
  Lemma (requires (ni_exp env e l /\ ni_com env c l))
        (ensures  (ni_com env (While e c v) l))
let while_com env e c v l = forall_intro
  (fun (h:rel (option heap)) -> while_com' env e c v l h
    <: Lemma (ensures  (ni_com' env (While e c v) l h)))
