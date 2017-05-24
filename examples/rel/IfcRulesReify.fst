module IfcRulesReify

open Rel
open WhileReify
open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreExcFixed
open FStar.Squash
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

val meet : label -> label -> Tot label
let meet l1 l2 =
  match l1, l2 with
  | High, High -> High
  | _, _ -> Low

let universal_property_meet l l1 l2
  : Lemma (requires (l <= l1 /\ l <= l2)) (ensures (l <= meet l1 l2))
= ()

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
       let vr = reify (interpret_exp_st e) (R?.r h)in
       let vl = reify (interpret_exp_st e) (R?.l h) in
       vr = vl
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
val sub_exp : env:label_fun -> e:exp -> l1:label -> l2:label ->
  Lemma (requires (l1 <= l2 /\ ni_exp env e l1))
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

val sub_com : env:label_fun -> c:com -> l1:label -> l2:label ->
  Lemma (requires (l2 <= l1 /\ ni_com env c l1 ))
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
  let vr = reify (interpret_exp_st e) (R?.r h0) in
  let vl = reify (interpret_exp_st e) (R?.l h0) in
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
  let v = reify (interpret_exp_st e) h0 in
  match reify (interpret_com_st (Assign r e) h0) h0 with
  | None, h1 -> ()
  | Some (), h1 ->
    assert (h1 == upd h0 r v)

val assign_com : env:label_fun -> e:exp -> r:id ->
  Lemma (requires (ni_exp env e (env r)))
        (ensures  (ni_com env (Assign r e) (env r)))
let assign_com env e r =
  forall_intro (assign_inv_com0 env e r (FStar.Squash.get_proof (ni_exp env e (env r)))) ;
  forall_intro (assign_inv_com' env e r)


let seq_nil1 (c1:com) (c2:com) (h:heap)
   : Lemma
  (requires (fst (reify (interpret_com_st c1 h) h) = None))
  (ensures  (fst (reify (interpret_com_st (Seq c1 c2) h) h) = None))
   = ()

let seq_nil2 (c1:com) (c2:com) (h0:heap) (h1:heap)
   : Lemma
  (requires (h1 == snd (reify (interpret_com_st c1 h0) h0) /\
             fst (reify (interpret_com_st c2 h1) h1) = None))
  (ensures  (fst (reify (interpret_com_st (Seq c1 c2) h0) h0) = None))
   = ()

(* Sequencing rule for commands

         env,pc:l |- c1  env,pc:l |- c2
         ------------------------------
               env,pc:l |- c1; c2
*)

val seq_inv_com' : env:label_fun -> c1:com -> c2:com -> l:label -> h0:heap ->
  Lemma (requires (ni_com env c1 l /\ ni_com env c2 l))
    (ensures (inv_com' env (Seq c1 c2) l h0))
let seq_inv_com' env c1 c2 l h0 =
  match reify (interpret_com_st c1 h0) h0 with
  | None, _ -> seq_nil1 c1 c2 h0
  | Some (), h1 ->
    match reify (interpret_com_st c2 h1) h1 with
    | None, _ -> seq_nil2 c1 c2 h0 h1
    | Some (), h2 -> ()

#set-options "--z3rlimit 50"
let use_ni_com (env:label_fun) (c:com) (l:label) (h:rel heap{low_equiv env h})
  : Lemma
    (requires ni_com env c l)
    (ensures
          (let R hl hr = h in
           match reify (interpret_com_st c hl) hl,
                 reify (interpret_com_st c hr) hr with
           | (Some _, hl'),
             (Some _, hr') -> low_equiv env (R hl' hr')
           | _ -> True))
   = ()

val seq_com' : env:label_fun -> c1:com -> c2:com -> l:label -> h0: rel heap ->
  Lemma (requires (ni_com env c1 l /\ ni_com env c2 l))
        (ensures  (ni_com' env (Seq c1 c2) l h0))
let seq_com' env c1 c2 l h0 =
  if not (FStar.StrongExcludedMiddle.strong_excluded_middle (low_equiv env h0))
  then ()
  else begin
    assert (low_equiv env h0);
    let R h0l h0r = h0 in
    match reify (interpret_com_st c1 h0l) h0l with
    | None, _ -> seq_nil1 c1 c2 h0l
    | Some (), h1l ->
      match reify (interpret_com_st c1 h0r) h0r with
      | None, _ -> seq_nil1 c1 c2 h0r
      | Some (), h1r ->
        match reify (interpret_com_st c2 h1l) h1l with
        | None, _ -> seq_nil2 c1 c2 h0l h1l
        | Some (), h2l ->
          match reify (interpret_com_st c2 h1r) h1r with
          | None, _ -> seq_nil2 c1 c2 h0r h1r
          | Some (), h2r ->
              let h1 = R h1l h1r in
              use_ni_com env c1 l h0;
              assert (low_equiv env h1) ;
              let h2 = R h2l h2r in
              use_ni_com env c2 l h1;
              assert (low_equiv env h2)
   end

val seq_com : env:label_fun -> c1:com -> c2:com -> l:label ->
  Lemma (requires (ni_com env c1 l /\ ni_com env c2 l))
        (ensures  (ni_com env (Seq c1 c2) l))
let seq_com env c1 c2 l =
  forall_intro
    (fun (h0:rel heap) ->
      seq_com' env c1 c2 l h0 <: Lemma (ni_com' env (Seq c1 c2) l h0)) ;
  forall_intro
    (fun (h0:heap) ->
      seq_inv_com' env c1 c2 l h0 <: Lemma (inv_com' env (Seq c1 c2) l h0))

(* Typing rule for conditional commands

         env |- e : l   env,pc:l |- ct   env,pc:l |- cf
         ----------------------------------------------
             env,pc:l |- if e <> 0 then ct else cf
*)

val cond_inv_com' : env:label_fun -> e:exp -> ct:com -> cf:com -> l:label -> h0:heap ->
  Lemma (requires ((ni_exp env e l) /\ (ni_com env ct l) /\ (ni_com env cf l)))
          (ensures  (inv_com' env (If e ct cf) l h0))
let cond_inv_com' env e ct cf l h0 =
  let v = reify (interpret_exp_st e) h0 in
  if v = 0
  then match reify (interpret_com_st cf h0) h0 with
    | None, _ -> ()
    | Some (), h1 -> ()
  else match reify (interpret_com_st cf h0) h0 with
    | None, _ -> ()
    | Some (), h1 -> ()

  (* Works too but takes 20s more *)
  (* let c = if v = 0 then cf else ct in *)
  (* match reify (interpret_com_st c h0) h0 with *)
  (* | None, _ -> () *)
  (* | Some (), h1 -> () *)
#reset-options "--max_fuel 1"
let interpret_cond (e:exp) (ct:com) (cf:com) (h:heap)
  : Lemma (let v = reify (interpret_exp_st e) h in
           let c = if v = 0 then cf else ct in
           (reify (interpret_com_st (If e ct cf) h) h ==
            reify (interpret_com_st c h) h))
  = ()
    

val cond_ni_com' : env:label_fun -> e:exp -> ct:com -> cf:com -> l:label -> h0:rel heap ->
  Lemma (requires ((ni_exp env e l) /\ (ni_com env ct l) /\ (ni_com env cf l)))
          (ensures  (ni_com' env (If e ct cf) l h0))
let cond_ni_com' env e ct cf l h0 =
  if not (FStar.StrongExcludedMiddle.strong_excluded_middle (low_equiv env h0))
  then ()
  else
    let R h0l h0r = h0 in
    let vl = reify (interpret_exp_st e) h0l in
    let vr = reify (interpret_exp_st e) h0r in
    if Low? l
    then begin
      assert (vl == vr) ;
      let c = if vl = 0 then cf else ct in
      assert (ni_com env c l) ;
      let cif = If e ct cf in
      //NS:05/15 ... this 2 should be trivial to prove.
      //             Why do they require a lemma?
      interpret_cond e ct cf h0l;
      interpret_cond e ct cf h0r;
      use_ni_com env c l (R h0l h0r)
      end
    else  (* h0 and h1 are low_equiv since cl and cr cannot write at low cells *)
      match reify (interpret_com_st (If e ct cf) h0l) h0l with
      | None, _ -> ()
      | Some (), h1l ->
        match reify (interpret_com_st (If e ct cf) h0r) h0r with
        | None, _ -> ()
        | Some (), h1r ->
          cond_inv_com' env e ct cf l h0l ;
          cond_inv_com' env e ct cf l h0r ;
          assert (low_equiv env h0 ==> low_equiv env (R h1l h1r))

#set-options "--z3rlimit 5"

val cond_com : env:label_fun -> e:exp -> ct:com -> cf:com -> l:label ->
  Lemma (requires ((ni_exp env e l) /\ (ni_com env ct l) /\ (ni_com env cf l)))
         (ensures  (ni_com env (If e ct cf) l))
let cond_com env e ct cf l =
  forall_intro
    (fun (h0:rel heap) ->
      cond_ni_com' env e ct cf l h0 <: Lemma (ni_com' env (If e ct cf) l h0)) ;
  forall_intro
    (fun (h0:heap) ->
      cond_inv_com' env e ct cf l h0 <: Lemma (inv_com' env (If e ct cf) l h0))


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


val while_inv_com'
  : env:label_fun ->
    e:exp ->
    c:com ->
    v:metric ->
    l:label ->
    h0:heap ->
    Lemma
      (requires (ni_exp env e l /\ ni_com env c l))
      (ensures  (inv_com' env (While e c v) l h0))
      (decreases (decr_while h0 (While e c v)))

#reset-options "--z3rlimit 40"

let interpret_while_nil e c v h
  : Lemma (requires (reify (interpret_exp_st e) h <> 0 /\
                     fst (reify (interpret_com_st c h) h) == None))
          (ensures (interpret_com h (While e c v) == None))
  = ()

let interpret_while_loops (e:exp) (c:com) (v:metric) (h:heap)
  : Lemma (requires (reify (interpret_exp_st e) h <> 0 /\
                     (match reify (interpret_com_st c h) h with
                       | None, _ -> True
                       | Some _, h' ->
                         interpret_exp' h' v >= interpret_exp' h v)))
          (ensures (interpret_com h (While e c v) == None))
  = ()

let rec while_inv_com' env e c v l h0 =
  let v0 = reify (interpret_exp_st e) h0 in
  if v0 = 0 then assert (interpret_com h0 (While e c v) == Some h0)
  else
    let m0 = interpret_exp' h0 v in
    match reify (interpret_com_st c h0) h0 with
    | None, _ -> interpret_while_nil e c v h0
    | Some (), h2 ->
      let m1 = interpret_exp' h2 v in
      if m0 > m1
      then begin
          assert (decr_while h2 (While e c v) << decr_while h0 (While e c v)) ;
          while_inv_com' env e c v l h2
        end
      else interpret_while_loops e c v h0


val while_ni_com' : env:label_fun -> e:exp -> c:com -> v:metric -> l:label -> h0:rel heap ->
  Lemma (requires (ni_exp env e l /\ ni_com env c l))
        (ensures  (ni_com' env (While e c v) l h0))
        (decreases (decr_while (R?.l h0) (While e c v) + decr_while (R?.r h0) (While e c v)))
#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 50"
let rec while_ni_com' env e c v l h0 =
  if not (FStar.StrongExcludedMiddle.strong_excluded_middle (low_equiv env h0))
  then ()
  else
    let R h0l h0r = h0 in
    let v0l = reify (interpret_exp_st e) h0l in
    let v0r = reify (interpret_exp_st e) h0r in
    if Low? l
    then begin
      assert (v0l == v0r) ;
      if v0l = 0 then begin
        assert (interpret_com h0l (While e c v) == Some h0l);
        assert (interpret_com h0r (While e c v) == Some h0r)
      end
      else
        let m0l = interpret_exp' h0l v in
        let m0r = interpret_exp' h0r v in
        match reify (interpret_com_st c h0l) h0l with
        | None, _ -> interpret_while_nil e c v h0l
        | Some (), h2l ->
          match reify (interpret_com_st c h0r) h0r with
          | None, _ -> interpret_while_nil e c v h0r
          | Some (), h2r ->
            let m1l = interpret_exp' h2l v in
            let m1r = interpret_exp' h2r v in
            if m0l > m1l
            then if m0r > m1r
              then begin
                  assert (decr_while h2l (While e c v) << decr_while h0l (While e c v)) ;
                  while_ni_com' env e c v l (R h2l h2r)
                end
              else interpret_while_loops e c v h0r
            else interpret_while_loops e c v h0l
      end
    else
      (* h0 and h1 are low_equiv since cl and cr cannot write at low cells *)
      match reify (interpret_com_st (While e c v) h0l) h0l with
      | None, _ -> ()
      | Some (), h1l ->
        match reify (interpret_com_st (While e c v) h0r) h0r with
        | None, _ -> ()
        | Some (), h1r ->
          while_inv_com' env e c v l h0l ;
          while_inv_com' env e c v l h0r ;
          assert (low_equiv env h0 ==> low_equiv env (R h1l h1r))

#set-options "--z3rlimit 5"

val while_com : env:label_fun -> e:exp -> c:com -> v:metric -> l:label ->
  Lemma (requires (ni_exp env e l /\ ni_com env c l))
        (ensures  (ni_com env (While e c v) l))
let while_com env e c v l =
  forall_intro
    (fun (h:rel heap) ->
      while_ni_com' env e c v l h <: Lemma (ensures (ni_com' env (While e c v) l h))) ;
  forall_intro
    (fun (h0:heap) ->
      while_inv_com' env e c v l h0 <: Lemma (ensures (inv_com' env (While e c v) l h0)))
