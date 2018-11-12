module Sequences

open FStar.Tactics
open FStar.Reflection
open FStar.Seq

let is_seq_t t : Tac bool =
    let hd, args = collect_app t in
    let tseq = `seq in
    print ("This is the quoted term: " ^ (term_to_string tseq));
    print ("This is hd: " ^ (term_to_string hd));
    term_eq tseq hd

let clear_hypothesis (b:binder) : Tac unit = ()

let retain_only (nss:list string) : Tac unit =
  prune ""; //removes every top-level assertion which "" as a prefix; so prune everything
  addns "Prims" ; //keep prims always
  let _ig = map addns nss in //add back only things in nss
  ()

let unrefine_eq_lem (#a:Type) (#p : (a -> Type)) (x y : (z:a{p z})) (s : squash (eq2 #a x y)) : Lemma (eq2 #(z:a{p z}) x y) =
    ()

let prune_for_seq () : Tac unit =
  let e = cur_env () in
  let bs = binders_of_env e in
  //prune the local environment
  let _ = map (fun b ->
    match term_as_formula (type_of_binder b) with
    | Comp (Eq (Some t)) _ _ ->
      if is_seq_t t then //this is a sequence equality; keep it
        ()
      else clear_hypothesis b
    | _ -> ()) bs
  in
  retain_only ["FStar.Seq"]

let try_unref_eq () : Tac unit =
  let g = cur_goal () in //this is just the goal type
  let f = term_as_formula g in
  match f with
  | Comp (Eq (Some t)) l r ->
    begin match inspect t with
    | Tv_Refine _ _ ->
        apply_lemma (`unrefine_eq_lem);
        norm []
    | _ ->
        fail "done"
    end
  | _ -> fail "done"


let sequence_pruning () : Tac unit =
  norm [] ; //normalize the current goal
  // GM: if `seq a` is refined, applying lemma_eq_elim misbehaves and spins off a different goal, work around it by removing refinements here
  let _ = repeat try_unref_eq in
  let g = cur_goal () in
  let f = term_as_formula g in
  print ("This is the formula: " ^ (formula_to_string f));
  match f with
  | Comp (Eq (Some t)) l r ->
    //could use inspect t, but in this case ...
    if is_seq_t t
    then (prune_for_seq ();
          dump "After pruning" ;
          apply_lemma (`lemma_eq_elim)) //ok, we have a sequence equality; we're going to try to process it
    else fail "Not a sequence" //don't know about this goal, leave it untouched
  | _ -> fail "Not a sequence"

(* tseqthe quoted term    print ("This is the quoted term: " ^ (term_to_string tseq));     *)

(* This is a way to match more explicitly on an fvar
    match inspect hd with
    | Tv_FVar fv ->
      if inspect_fv fv = ["FStar"; "Seq"; "Base"; "seq"] //may be nicer to write it as "FStar.Seq.seq"; both as a string and also to
      then apply_lemma (quote lemma_eq_elim) //ok, we have a sequence equality; we're going to try to process it
      else fail "Not a sequence" //don't know about this goal, leave it untouched
    | _ -> fail "Not a sequence"
    end
*)

[@plugin]
let tau = fun () -> or_else sequence_pruning idtac


////////////////////////////////////////////////////////////////////////////////
let test (#a:Type0) (s:seq a) (x:a) (from:nat) (to:nat{from<=to /\ to<=length s}) (l:seq a) (y:nat) =
  assume (y == 17); //I would like to prune this out
  assume (l == snoc s x); //I would like to retain this fact from the local environment
  assert_by_tactic (slice s from to == slice l from to) //would prefer to write this, and have the tactic switch to extensional equality
                   (tau)


(* ////////////////// *)
(* 1. We generate this WP for test: *)

(*  forall a s x from to l y. y==17 ==> y == snoc s x ==> (with_tactic idtac (slice s from to == slice l from to) /\ *)
(*                                                   (with_tactic idtac (slice s from to == slice l from to) ==> (p /\ p ==> ...))) *)

(* 2. Then we process this WP *)

(*  a. remove marker in negative position *)
(*  forall a s x from to l y. y==17 ==> y == snoc s x ==> (with_tactic idtac (slice s from to == slice l from to) /\ *)
(*                                                   (slice s from to == slice l from to ==> (p /\ p ==> ...)) *)
(*  b. in positive position *)

(*  remove the marked term from the main VC *)
(*  forall a s x from to l y. y==17 ==> y == snoc s x ==> (true /\ *)
(*                                                   (slice s from to == slice l from to ==> (p /\ p ==> ...)) *)


(*  separate subgoal *)

(*   run idtac [ (G, (slice s from to == slice l from to)] where G =  a s x from to l y. y==17 ==> y == snoc s x *)

(*   -->* [ (G, (slice s from to == slice l from to)] *)


(*  c. present all remaining goals to Z3 *)

(* (\*   assert (slice s from to `Seq.equal` slice (snoc s x) from to) *\) *)
