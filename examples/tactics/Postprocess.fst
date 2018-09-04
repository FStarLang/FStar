module Postprocess

open FStar.Tactics

let lem () : Lemma (1 == 2) = admit ()
let tau () = apply_lemma (`lem)

[@(postprocess_with tau)]
let x : int = 1

[@(postprocess_for_extraction_with tau)]
let y : int = 1

let _ = assert (x == 2)
let _ = assert (y == 1) // but `2` in extracted code

(* More hardcore transformations *)

noeq
type t1 =
    | A1 : t1
    | B1 : int -> t1
    | C1 : (int -> t1) -> t1

noeq
type t2 =
    | A2 : t2
    | B2 : int -> t2
    | C2 : (int -> t2) -> t2

let rec lift : t1 -> t2 =
    function
    | A1 -> A2
    | B1 i -> B2 i
    | C1 f -> C2 (fun x -> lift (FStar.WellFounded.axiom1 f x; f x))

let lemA () : Lemma (lift A1 == A2) = ()
let lemB x : Lemma (lift (B1 x) == (B2 x)) = ()
let lemC ($f: int -> t1) : Lemma (lift (C1 f) == C2 (fun x -> lift (f x))) by (compute ()) = ()

(* These could really be polymorphic *)
let congB #i #j (_ : squash (i == j)) : Lemma (B2 i == B2 j) = ()
let congC #f #g (_ : squash (f == g)) : Lemma (C2 f == C2 g) = ()

let xx = C1 (function
             | 0 -> A1
             | 5 -> B1 42
             | x -> B1 24)

open FStar.FunctionalExtensionality


let apply_feq_lem #a #b ($f $g : a -> b) : Lemma (requires (forall x. f x == g x))
                                              (ensures (f == g)) =
    assert (feq f g);
    ()
    
let fext () = apply_lemma (`apply_feq_lem); dismiss (); ignore (forall_intros ())

let _onL a b c (_ : squash (a == b)) (_ : squash (b == c)) : Lemma (a == c) = ()
let onL () = apply_lemma (`_onL)

// invariant: takes goals of shape squash (E == ?u) and solves them
let rec push_lifts' (u:unit) : Tac unit =
  match term_as_formula (cur_goal ()) with
  | Comp (Eq _) lhs rhs ->
    begin
    match inspect lhs with
    | Tv_App h t ->
      begin match inspect h with
      | Tv_FVar fv ->
        if fv_to_string fv = `%lift
        then case_analyze (fst t)
        else fail "not a lift (1)"
      | _ -> fail "not a lift (2)"
      end

    | Tv_Abs _ _ ->
      fext ();
      push_lifts' ()
      
    | _ -> fail "not a lift (3)"
    end
  | _ ->
    fail "not an equality"
and case_analyze (lhs:term) : Tac unit =
    let ap l =
      onL (); apply_lemma l
    in
    (* dump ("lhs= " ^ term_to_string lhs); *)
    match inspect lhs with
    | Tv_App _ _ ->
      let head, args = collect_app lhs in
      begin match inspect head with
      | Tv_FVar fv ->
             if fv_to_string fv = `%A1 then (ap (`lemA))
        else if fv_to_string fv = `%B1 then (ap (`lemB); apply_lemma (`congB); push_lifts' ())
        else if fv_to_string fv = `%C1 then (ap (`lemC); apply_lemma (`congC); push_lifts' ())
        else (tlabel "unknown fv"; trefl ())
      | _ -> 
        tlabel "head unk";
        trefl ()
      end
             
    | _ ->
      tlabel "ignoring";
      trefl ()

let push_lifts () : Tac unit =
  unfold_def (`xx);
  (* dump "before"; *)
  push_lifts' ();
  (* dump "after"; *)
  ()


[@(postprocess_with push_lifts)]
let yy = lift xx

[@(postprocess_with push_lifts)]
let zz = lift (C1 (fun y -> (C1 (fun x -> A1))))
