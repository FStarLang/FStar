(* This doesn't work in interactive mode because it seems the symbol
   table queried by Emacs has stale unification variables in it.

   TODO: fix that table up in the compression pass
*)
module FStar.Tactics.Sequences

open FStar.Tactics
open FStar.Seq

let is_seq_t t : tactic bool = 
    let hd, args = collect_app t in
    tseq <-- quote seq; //Somehow, tseq ends up as (seq u#0), when we expect it to be (seq u#?), i.e., a unification variable
    return (term_eq tseq hd)

    (* print ("This is the quoted term: " ^ (term_to_string tseq));; *)
    (* print ("This is hd: " ^ (term_to_string hd));;     *)

let clear_hypothesis (b:binder) : tactic unit = idtac

let retain_only (nss:list string) : tactic unit = 
  prune "";; //removes every top-level assertion which "" as a prefix; so prune everything
  addns "Prims" ;; //keep prims always
  _ig <-- mapM addns nss ;  //add back only things in nss
  return ()
  
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
  
val sequence_pruning : tactic unit
let sequence_pruning =
  norm [];; //normalize the current goal
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
  assert_by_tactic (or_else sequence_pruning idtac) (slice s from to == slice l from to) //would prefer to write this, and have the tactic switch to extensional equality

(*   assert (slice s from to `Seq.equal` slice (snoc s x) from to) *)
