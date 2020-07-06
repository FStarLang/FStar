module Steel.FramingEffect.Common

open Steel.Memory
module Sem = Steel.Semantics.Hoare.MST
open Steel.Semantics.Instantiate


irreducible let framing_implicit : unit = ()

let delay (p:Type0) : Type0 = p
let annot_sub_post (p:Type0) : Type0 = p

type pre_t = slprop u#1
type post_t (a:Type) = a -> slprop u#1

let join_preserves_interp (hp:slprop) (m0:hmem hp) (m1:mem{disjoint m0 m1})
: Lemma
  (interp hp (join m0 m1))
  [SMTPat (interp hp (join m0 m1))]
= intro_emp m1;
  intro_star hp emp m0 m1;
  affine_star hp emp (join m0 m1)

let ens_depends_only_on (#a:Type) (pre:slprop) (post:a -> slprop)
  (q:(hmem pre -> x:a -> hmem (post x) -> prop))

= //can join any disjoint mem to the pre-mem and q is still valid
  (forall x (m_pre:hmem pre) m_post (m:mem{disjoint m_pre m}).
     q m_pre x m_post <==> q (join m_pre m) x m_post) /\  //at this point we need to know interp pre (join m_pre m) -- use join_preserves_interp for that

  //can join any disjoint mem to the post-mem and q is still valid
  (forall x m_pre (m_post:hmem (post x)) (m:mem{disjoint m_post m}).
     q m_pre x m_post <==> q m_pre x (join m_post m))

type req_t (pre:pre_t) = q:(hmem pre -> prop){  //inlining depends only on
  forall (m0:hmem pre) (m1:mem{disjoint m0 m1}). q m0 <==> q (join m0 m1)
}
type ens_t (pre:pre_t) (a:Type u#a) (post:post_t u#a a) : Type u#(max 2 a) =
  q:(hmem pre -> x:a -> hmem (post x) -> prop){
    ens_depends_only_on pre post q
  }

assume val sl_implies (p q:slprop u#1) : Type0

assume val sl_implies_reflexive (p:slprop u#1)
: Lemma (p `sl_implies` p)
  [SMTPat (p `sl_implies` p)]

assume val sl_implies_interp (p q:slprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures forall (m:mem) (f:slprop). interp (p `star` f) m ==>  interp (q `star` f) m)
  [SMTPat (p `sl_implies` q)]

assume val sl_implies_interp_emp (p q:slprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures forall (m:mem). interp p m ==>  interp q m)
  [SMTPat (p `sl_implies` q)]

assume val sl_implies_preserves_frame (p q:slprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures
    forall (m1 m2:mem) (r:slprop).
      Sem.preserves_frame #state q r m1 m2 ==>
      Sem.preserves_frame #state p r m1 m2)
  [SMTPat (p `sl_implies` q)]

assume val sl_implies_preserves_frame_right (p q:slprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures
    forall (m1 m2:mem) (r:slprop).
      Sem.preserves_frame #state r p m1 m2 ==>
      Sem.preserves_frame #state r q m1 m2)
  [SMTPat (p `sl_implies` q)]

let can_be_split (t1 t2:pre_t) = t1 `sl_implies` t2

let can_be_split_forall (#a:Type) (t1 t2:post_t a) =
  forall (x:a). t1 x `sl_implies` t2 x



/// Tactic for inferring frame automatically


let equiv_sl_implies (p1 p2:slprop) : Lemma
  (requires p1 `equiv` p2)
  (ensures p1 `sl_implies` p2)
  = admit()

let lemma_sl_implies_refl (p:slprop) : Lemma
  (ensures p `sl_implies` p)
  = equiv_sl_implies p p

let emp_unit_variant (#a:Type) (p:a -> slprop) : Lemma
   (ensures can_be_split_forall (fun x -> p x `star` emp) p)
  = let aux (x:a) : Lemma
      ((fun x -> p x `star` emp) x `sl_implies` p x)
      = Classical.forall_intro emp_unit;
        equiv_sl_implies ((fun x -> p x `star` emp) x) (p x)
    in Classical.forall_intro aux

open FStar.Tactics

let canon' (_:unit) : Tac unit =
  or_else (fun _ -> Steel.Memory.Tactics.canon())
          (fun _ -> fail "Could not prove slprop equivalence")

let rec slterm_nbr_uvars (t:term) : Tac int =
  match inspect t with
  | Tv_Uvar _ _ -> 1
  | Tv_App _ _ ->
    let hd, args = collect_app t in
    slterm_nbr_uvars hd + fold_left (fun n (x, _) -> n + slterm_nbr_uvars x) 0 args
  | Tv_Abs _ t -> slterm_nbr_uvars t
  // TODO: Probably need to check that...
  | _ -> 0

let solve_can_be_split (args:list argv) : Tac bool =
  match args with
  | [(t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> norm [delta_only [`%can_be_split]];
                     // If we have exactly the same term on both side,
                     // equiv_sl_implies would solve the goal immediately
                     or_else (fun _ -> apply_lemma (`lemma_sl_implies_refl))
                      (fun _ -> apply_lemma (`equiv_sl_implies);
                       norm [delta_only [
                              `%__proj__CM__item__unit;
                              `%__proj__CM__item__mult;
                              `%Steel.Memory.Tactics.rm;
                              `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                              `%fst; `%snd];
                            primops; iota; zeta];
                       canon' ()));
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen

let solve_can_be_split_forall (args:list argv) : Tac bool =
  match args with
  | [_; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> ignore (forall_intro());
                     norm [delta_only [`%can_be_split_forall]];
                     or_else (fun _ -> apply_lemma (`lemma_sl_implies_refl))
                       (fun _ ->
                       apply_lemma (`equiv_sl_implies);
                       or_else (fun _ ->  flip()) (fun _ -> ());
                       norm [delta_only [
                              `%__proj__CM__item__unit;
                              `%__proj__CM__item__mult;
                              `%Steel.Memory.Tactics.rm;
                              `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                              `%fst; `%snd];
                            primops; iota; zeta];
                       canon' ()));
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen

let rec solve_subcomp_post (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | App _ t ->
        let hd, args = collect_app t in
        if term_eq hd (quote annot_sub_post) then (focus (fun _ ->
          norm [delta_only [`%annot_sub_post]];
          // Assuming for now that the body will always be Steel
          // instead of SteelF, as we'll lift pure to Steel by
          // a polymonadic bind with Steel alloc/read/...
          // That means the postcondition of return will be ?u_ret * ?u_emp
          or_else (fun _ -> apply_lemma (`emp_unit_variant))
                  (fun _ ->
                     norm [delta_only [`%can_be_split_forall]];
                     ignore (forall_intro());
                     or_else
                       (fun _ -> apply_lemma (`lemma_sl_implies_refl))
                       (fun _ ->
                       let open FStar.Algebra.CommMonoid.Equiv in
                       apply_lemma (`equiv_sl_implies);
                       or_else (fun _ ->  flip()) (fun _ -> ());
                       norm [delta_only [
                              `%__proj__CM__item__unit;
                              `%__proj__CM__item__mult;
                              `%Steel.Memory.Tactics.rm;
                              `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                              `%fst; `%snd];
                            primops; iota; zeta];
                       canon' ()))
          ))
        else (later());
        solve_subcomp_post tl
    | _ -> later(); solve_subcomp_post tl

let is_uvar (t:term) : Tac bool = match t with
  | Tv_Uvar _ _ -> true
  | _ -> false

let is_return_eq (l r:term) : Tac bool =
  let nl, al = collect_app l in
  let nr, ar = collect_app r in
  match al, ar with
  | [(t1, _)], [(t2, _)] ->
    let b1 = is_uvar nl in
    let b2 = is_uvar nr in
    let b3 = not (is_uvar t1) in
    let b4 = not (is_uvar t2) in
    b1 && b2 && b3 && b4
  | _ -> false

let rec solve_indirection_eqs (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        if is_return_eq l r then later() else trefl();
        solve_indirection_eqs tl
    | _ -> later(); solve_indirection_eqs tl

let rec solve_triv_eqs (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
      let lnbr = slterm_nbr_uvars l in
      let rnbr = slterm_nbr_uvars r in
      // Only solve equality if there is only one uvar
      // trefl();
     if lnbr = 0 || rnbr = 0 then trefl () else later();
      solve_triv_eqs tl
    | _ -> later(); solve_triv_eqs tl

// Returns true if the goal has been solved, false if it should be delayed
let solve_or_delay (g:goal) : Tac bool =
  let f = term_as_formula' (goal_type g) in
  match f with
  | App _ t ->
      let hd, args = collect_app t in
      if term_eq hd (quote delay) then false
      else if term_eq hd (quote can_be_split) then solve_can_be_split args
      else if term_eq hd (quote can_be_split_forall) then solve_can_be_split_forall args
      else false
  | Comp (Eq _) l r ->
    let lnbr = slterm_nbr_uvars l in
    let rnbr = slterm_nbr_uvars r in
    // Only solve equality if one of the terms is completely determined
    if lnbr = 0 || rnbr = 0 then (trefl (); true) else false
  | _ -> false


// Returns true if it successfully solved a goal
// If it returns false, it means it didn't find any solvable goal,
// which should mean only delayed goals are left
let rec pick_next (l:list goal) : Tac bool =
  match l with
  | [] -> false
  | a::q -> if solve_or_delay a then true else (later (); pick_next q)

let rec resolve_tac () : Tac unit =
  match goals () with
  | [] -> ()
  | g ->
    if pick_next g then resolve_tac ()
    else
      (norm [delta_only [`%delay]];
      resolve_tac ())

let typ_contains_req_ens (t:term) : Tac bool =
  let name, _ = collect_app t in
  if term_eq name (`req_t) || term_eq name (`ens_t) then true
  else false

let rec filter_goals (l:list goal) : Tac (list goal * list goal) =
  match l with
  | [] -> [], []
  | hd::tl ->
      let slgoals, loggoals = filter_goals tl in
      match term_as_formula' (goal_type hd) with
      | Comp (Eq t) _ _ ->
        if Some? t then
          let b = typ_contains_req_ens (Some?.v t) in
          if b then slgoals, hd::loggoals
          else hd::slgoals, loggoals
        else hd::slgoals, loggoals
      | App t _ -> if term_eq t (`squash) then hd::slgoals, loggoals else slgoals, loggoals
      | _ -> slgoals, loggoals

[@@ resolve_implicits; framing_implicit]
let init_resolve_tac () : Tac unit =
  let slgs, loggs = filter_goals (goals()) in
  set_goals slgs;
  // We first need to solve the trivial equalities to ensure we're not restricting
  // scopes for annotated slprops
  solve_triv_eqs (goals ());
  solve_indirection_eqs (goals());
  solve_subcomp_post (goals ());
  resolve_tac ();
  set_goals loggs;
  resolve_tac ()
