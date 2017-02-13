module IfcReify

open Rel
open WhileReify
open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreExcFixed
open FStar.Classical

(****************************** Preliminaries ******************************)

(* CH: Everything specialized to 2-point lattice *)
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

val join : label -> label -> Tot label
let join l1 l2 =
  match l1, l2 with
  | Low,Low -> Low
  | _, _ -> High

type label_fun = id -> Tot label

type low_equiv (env:label_fun) (h1:rel heap) =
  (forall (x:id). (* {:pattern (env x)} *) env x = Low ==> index (R?.l h1) x = index (R?.r h1) x)

(**************************** Typing Judgements ****************************)

(* env |- e : l
   - Expressions do not modify the heap
   - Correctness
   - Low equivalent input heaps + Low label ==> same result
*)
let ni_exp (env:label_fun) (e:exp) (l:label) : Tot Type0 =
  forall (h: rel heap). (* {:pattern (low_equiv env h)} *)
   (low_equiv env h /\ Low? l) ==>
     (* interpret_exp (R?.r h) e = interpret_exp (R?.l h) e *)
     begin
       let Some vr, hr = reify (interpret_exp_st e) (R?.r h)in
       let Some vl, hl = reify (interpret_exp_st e) (R?.l h) in
       R?.r h = hr /\ R?.l h = hl /\ vr = vl
     end



(* env,pc:l |- c
   - References with a label below l are not modified
   - Total correctness
   - Low equivalent input heaps ==> Low equivalent output heaps
*)
let inv_com' (env:label_fun) (c:com) (l:label) (h0:heap) : Tot Type0
=
  match interpret_com h0 c with
  | None -> True
  | Some h1 ->
    forall (i:id). (* {:pattern (env i < l)} *) env i < l ==> index h0 i = index h1 i

let ni_com' (env:label_fun) (c:com) (l:label) (h0:rel heap) : Tot Type0 =
  let R h0l h0r = h0 in
  (* KM : That's the code that we would like to write but subtyping and matching on pairs interplay badly *)
  (* it generates a VC which boils down to [forall (h1l:heap). length h1l = length h0l] which is obviously false *)
  (* begin match interpret_com h0l c, interpret_com h0r c with *)
  (* | Some h1l, Some h1r -> low_equiv env (R h0l h0r) ==> low_equiv env (R h1l h1r) *)
  (* | _ -> True *)
  (* end *)
  begin match interpret_com h0l c with
    | Some h1l -> begin match  interpret_com h0r c with
      | Some h1r -> low_equiv env h0 ==> low_equiv env (R h1l h1r)
      | _ -> True
    end
    | _ -> True
  end

let ni_com (env:label_fun) (c:com) (l:label) : Tot Type0 =
  (forall (h0: rel heap). (* {:pattern (low_equiv env h0)} *) ni_com' env c l h0) /\
  (forall (h0:heap). (* {:pattern (Some? (interpret_com h0 c))} *) inv_com' env c l h0)

(* KM : Trying to figure out wht are the design tradeoffs on option heap *)
(* let preserves_env_upto_label (env:label_fun) (l:label) (c:com) (h0:heap) : Tot Type0 *)
(* = let (res, h1) = interpret_com h0 c in *)
(*   Some? res ==> (forall (i:id{i `in_` h0}). env i < l ==> index h0 i = index h1 i) *)

(* type ni_com' (env:label_fun) (c:com) (l:label) (h0:rel heap) = *)
(*   begin *)
(*     let res, h1 = split (lift (fun h -> interpret_com h c) h0) in *)
(*     low_equiv env h0 /\ Some? `diagb` res ==> low_equiv env h1 *)
(*     end /\ *)
(*     (preserves_env_upto_label env l c) `diag` h0 *)

(* type ni_com (env:label_fun) (c:com) (l:label) = *)
(*     forall (h0: rel heap). ni_com' env c l h0 *)

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
  Lemma (ensures  (ni_exp env (AVar r) (env r)))
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
let binop_exp env op e1 e2 l =
  ()

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

let assign_inv_com0 (env:label_fun) (e:exp) (r:id) (ne:squash(ni_exp env e (env r))) (h0:rel heap)
  : Lemma (ni_com' env (Assign r e) (env r) h0)
=
  FStar.Squash.give_proof ne ;
  let Some vr, h0r' = reify (interpret_exp_st e) (R?.r h0) in
  let Some vl, h0l' = reify (interpret_exp_st e) (R?.l h0) in
  match reify (interpret_com_st (Assign r e) (R?.l h0)) (R?.l h0) with
  | Some (), h1l ->
    begin match reify (interpret_com_st (Assign r e) (R?.r h0)) (R?.r h0) with
    | Some (), h1r -> assert (h1l = upd (R?.l h0) r vl /\ h1r = upd (R?.r h0) r vr)
    | None, _ -> ()
    end
  | None, _ -> ()

let assign_inv_com' (env:label_fun) (e:exp) (r:id) (h0:heap)
 : Lemma (inv_com' env (Assign r e) (env r) h0)
=
  let Some v, h0' = reify (interpret_exp_st e) h0 in
  match reify (interpret_com_st (Assign r e) h0) h0 with
  | None, h1 -> ()
  | Some (), h1 ->
    assert (h1 == upd h0 r v)

val assign_com : env:label_fun -> e:exp -> r:id ->
  Lemma (requires (ni_exp env e (env r)))
        (ensures  (ni_com env (Assign r e) (env r)))
let assign_com env e r =
  FStar.Classical.forall_intro (assign_inv_com0 env e r (FStar.Squash.get_proof (ni_exp env e (env r)))) ;
  FStar.Classical.forall_intro (assign_inv_com' env e r)

(* Sequencing rule for commands

         env,pc:l |- c1  env,pc:l |- c2
         ------------------------------
               env,pc:l |- c1; c2
*)

(* val seq_inv_com' : env:label_fun -> c1:com -> c2:com -> l:label -> h0:option heap -> *)
(*   Lemma (requires (ni_com env c1 l /\ ni_com env c2 l)) *)
(*     (ensures (inv_com' env (Seq c1 c2) l h0)) *)
(* let seq_inv_com' env c1 c2 l = function *)
(*   | None -> () *)
(*   | Some h0 -> cut (inv_com' env c2 l (interpret_com h0 c1)) *)

(* val seq_com' : env:label_fun -> c1:com -> c2:com -> l:label -> h0: rel (option heap) -> *)
(*   Lemma (requires (ni_com env c1 l /\ ni_com env c2 l)) *)
(*         (ensures  (ni_com' env (Seq c1 c2) l h0)) *)
(* let seq_com' env c1 c2 l h0 = *)
(*   match h0 with *)
(*   | R (Some hl) (Some hr) -> cut (ni_com' env c2 l (R (interpret_com hl c1) (interpret_com hr c1))) *)
(*   | _ -> () *)

(* val seq_com : env:label_fun -> c1:com -> c2:com -> l:label -> *)
(*   Lemma (requires (ni_com env c1 l /\ ni_com env c2 l)) *)
(*         (ensures  (ni_com env (Seq c1 c2) l)) *)
(* let seq_com env c1 c2 l = *)
(*   forall_intro *)
(*     (fun (h0:rel (option heap)) -> *)
(*       seq_com' env c1 c2 l h0 <: Lemma (ni_com' env (Seq c1 c2) l h0)) ; *)
(*   forall_intro *)
(*     (fun (h0:option heap) -> *)
(*       seq_inv_com' env c1 c2 l h0 <: Lemma (inv_com' env (Seq c1 c2) l h0)) *)

(* Typing rule for conditional commands

         env |- e : l   env,pc:l |- ct   env,pc:l |- cf
         ----------------------------------------------
             env,pc:l |- if e <> 0 then ct else cf
*)

(* #set-options "--z3rlimit 100" *)

(* val cond_com : env:label_fun -> e:exp -> ct:com -> cf:com -> l:label -> *)
(*   Lemma (requires ((ni_exp env e l) /\ (ni_com env ct l) /\ (ni_com env cf l))) *)
(*          (ensures  (ni_com env (If e ct cf) l)) *)
(* let cond_com _ _ _ _ _ = () *)

(* #set-options "--z3rlimit 5" *)

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

(* let interpret_exp (h:heap) (v:metric) : Tot nat = *)
(*   match fst (interpret_exp h v) with *)
(*   | Some n -> if 0 > n then 0 else n *)
(*   | None -> 0 *)

(* (\* slight metric taking option heap *\) *)
(* val decr_while : h:(option heap) -> v:metric -> GTot nat *)
(* let decr_while h v = match h with *)
(*   | None -> 0 *)
(*   | Some h0 -> interpret_exp h0 v *)

(* (\* #reset-options "--z3rlimit 30" *\) *)


(* val while_inv_com' *)
(*   : env:label_fun -> *)
(*     e:exp -> *)
(*     c:com -> *)
(*     v:metric -> *)
(*     l:label -> *)
(*     h:option heap -> *)
(*     Lemma *)
(*       (requires (ni_exp env e l /\ ni_com env c l)) *)
(*       (ensures  (inv_com' env (While e c v) l h)) *)
(*       (decreases (decr_while h v)) *)
(* let rec while_inv_com' env e c v l = function *)
(*   | None -> () *)
(*   | Some h0 -> *)
(*     let h1_opt = interpret_com h0 c in *)
(*     match h1_opt with *)
(*     | None -> () *)
(*     | Some h1 -> *)
(*       let v0 = interpret_exp h0 v in *)
(*       let v1 = interpret_exp h1 v in *)
(*       if v0 > v1 && v1 >= 0 *)
(*       then while_inv_com' env e c v l h1_opt *)
(*       else () *)

(* val while_com' : env:label_fun -> e:exp -> c:com -> v:metric -> l:label -> h:rel (option heap) -> *)
(*   Lemma (requires (ni_exp env e l /\ ni_com env c l)) *)
(*         (ensures  (ni_com' env (While e c v) l h)) *)
(*         (decreases (decr_while (R?.l h) v + decr_while (R?.r h) v)) *)
(* let rec while_com' env e c v l h = *)
(*   // Interpret the body *)
(*   match h with *)
(*   | R (Some h_l) (Some h_r) -> begin *)
(*     let o_l = interpret_com h_l c in *)
(*     let o_r = interpret_com h_r c in *)

(*     // Case analysis on termination of bodies *)
(*     match o_l, o_r with *)
(*     | Some hl , Some hr  -> *)
(*       begin *)
(*         // case analysis on decreasing of metric *)
(*         match (interpret_exp h_l v > interpret_exp hl v) && interpret_exp hl v >= 0 , *)
(*           (interpret_exp h_r v > interpret_exp hr v) && interpret_exp hr v >= 0 with *)
(*         | true , true  -> while_com' env e c v l (R o_l o_r) *)
(*         | true , false -> while_com' env e c v l (R o_l (Some h_r)) *)
(*         | false , true -> while_com' env e c v l (R (Some h_l) o_r ) *)
(*         | false, false -> () *)
(*       end *)
(*     | Some hl , None -> *)
(*       if (interpret_exp h_l v > interpret_exp hl v) && interpret_exp hl v >= 0 then *)
(*         while_com' env e c v l (R o_l (Some h_r)) *)
(*     | None , Some hr  -> *)
(*       if (interpret_exp h_r v > interpret_exp hr v) && interpret_exp hr v >= 0 then *)
(*         while_com' env e c v l (R (Some h_l) o_r) *)
(*     | None, None -> () *)
(*     end *)
(*   | _ -> () *)

(* #reset-options *)

(* val while_com : env:label_fun -> e:exp -> c:com -> v:metric -> l:label -> *)
(*   Lemma (requires (ni_exp env e l /\ ni_com env c l)) *)
(*         (ensures  (ni_com env (While e c v) l)) *)
(* let while_com env e c v l = *)
  (* forall_intro *)
  (*   (fun (h:rel (option heap)) -> *)
  (*     while_com' env e c v l h <: Lemma (ensures (ni_com' env (While e c v) l h)))  *)
  (*     ; *)
  (* forall_intro *)
  (*   (fun (h0:option heap) -> *)
  (*     while_inv_com' env e c v l h0 <: Lemma (ensures (inv_com' env (While e c v) l h0))) *)

