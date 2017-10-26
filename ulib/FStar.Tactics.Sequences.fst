module FStar.Tactics.Sequences

open FStar.Tactics
open FStar.Reflection
open FStar.Seq

let is_seq_t t : tactic bool = 
    let hd, args = collect_app t in
    tseq <-- quote seq; //Somehow, tseq ends up as (seq u#0), when we expect it to be (seq u#?), i.e., a unification variable
    print ("This is the quoted term: " ^ (term_to_string tseq));;
    print ("This is hd: " ^ (term_to_string hd));;
    return (term_eq tseq hd)

let clear_hypothesis (b:binder) : tactic unit = idtac

let retain_only (nss:list string) : tactic unit = 
  prune "";; //removes every top-level assertion which "" as a prefix; so prune everything
  addns "Prims" ;; //keep prims always
  _ig <-- mapM addns nss ;  //add back only things in nss
  return ()

let unrefine_eq_lem (#a:Type) (#p : (a -> Type)) (x y : (z:a{p z})) (s : squash (eq2 #a x y)) : Lemma (eq2 #(z:a{p z}) x y) =
    ()
  
let prune_for_seq : tactic unit =
  g <-- cur_env;
  let bs = binders_of_env g in
  //prune the local environment
  _ig <-- mapM (fun b ->
    match term_as_formula (type_of_binder b) with
    | Comp Eq t _ _ ->
      s <-- is_seq_t t;
      if s then //this is a sequence equality; keep it
        idtac
      else clear_hypothesis b
    | _ -> idtac) bs ; 
  retain_only ["FStar.Seq"]
  
let try_unref_eq : tactic unit =
  g <-- cur_goal; //this is just the goal type
  let f = term_as_formula g in
  match f with
  | Comp Eq t l r ->
    begin match inspect t with
    | Tv_Refine _ _ ->
        apply_lemma (quote unrefine_eq_lem);;
        norm []
    | _ ->
        fail "done"
    end
  | _ -> fail "done"

val sequence_pruning : tactic unit
let sequence_pruning =
  norm [] ;; //normalize the current goal
  // GM: if `seq a` is refined, applying lemma_eq_elim misbehaves and spins off a different goal, work around it by removing refinements here
  repeat try_unref_eq;;
  g <-- cur_goal; //this is just the goal type
  dump "A";;
  let f = term_as_formula g in
  print ("This is the formula: " ^ (formula_to_string f));;
  match f with 
  | Comp Eq t l r ->
    dump "B";;
    //could use inspect t, but in this case ...
    b <-- is_seq_t t ; //use double everywhere in monadic notation (TODO)
    if b
    then (prune_for_seq ;; 
          dump "After pruning" ;;
          apply_lemma (quote lemma_eq_elim)) //ok, we have a sequence equality; we're going to try to process it
    else fail "Not a sequence" //don't know about this goal, leave it untouched
  | _ -> fail "Not a sequence"

(* tseqthe quoted term    print ("This is the quoted term: " ^ (term_to_string tseq));;     *)

(* This is a way to match more explicitly on an fvar
    match inspect hd with 
    | Tv_FVar fv -> 
      if inspect_fv fv = ["FStar"; "Seq"; "Base"; "seq"] //may be nicer to write it as "FStar.Seq.seq"; both as a string and also to 
      then apply_lemma (quote lemma_eq_elim) //ok, we have a sequence equality; we're going to try to process it
      else fail "Not a sequence" //don't know about this goal, leave it untouched
    | _ -> fail "Not a sequence"
    end
*)
    


////////////////////////////////////////////////////////////////////////////////
let test (#a:Type0) (s:seq a) (x:a) (from:nat) (to:nat{from<=to /\ to<=length s}) (l:seq a) (y:nat) =
  assume (y == 17); //I would like to prune this out
  assume (l == snoc s x); //I would like to retain this fact from the local environment
  assert_by_tactic (slice s from to == slice l from to) //would prefer to write this, and have the tactic switch to extensional equality
                   (or_else sequence_pruning idtac)


(* ////////////////// *)
(* 1. We generate this WP for test: *)

(*  forall a s x from to l y. y==17 ==> y == snoc s x ==> (by_tactic idtac (slice s from to == slice l from to) /\ *)
(*                                                   (by_tactic idtac (slice s from to == slice l from to) ==> (p /\ p ==> ...))) *)

(* 2. Then we process this WP *)

(*  a. remove marker in negative position *)
(*  forall a s x from to l y. y==17 ==> y == snoc s x ==> (by_tactic idtac (slice s from to == slice l from to) /\ *)
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
