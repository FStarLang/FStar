module Selectors.Tests

open Steel.Memory
open Steel.SelectorEffect

open FStar.Tactics

let lemma_sl_implies_refl (p:viewables) : Lemma
  (ensures p `sl_implies` p)
  = admit()

let vemp' : viewable =
  { fp = emp;
    a = unit;
    sel = fun _ -> () }

let vemp : viewables = VUnit vemp'

let emp_unit_variant (#a:Type) (p:a -> viewables) : Lemma
   (ensures can_be_split_forall (fun x -> p x `star` vemp) p)
  = admit()

module AE = FStar.Algebra.CommMonoid.Equiv
module CE = FStar.Tactics.CanonCommMonoidSimple.Equiv

assume val equiv (p1 p2:viewables) : Type0

let equiv_refl (x:viewables) : Lemma (equiv x x) = admit()

let equiv_sym (x y:viewables) : Lemma
  (requires equiv x y)
  (ensures equiv y x)
  = admit()

let equiv_trans (x y z:viewables) : Lemma
  (requires equiv x y /\ equiv y z)
  (ensures equiv x z)
  = admit()

let equiv_sl_implies (p1 p2:viewables) : Lemma
  (requires p1 `equiv` p2)
  (ensures p1 `sl_implies` p2)
  = admit()

inline_for_extraction noextract let req : AE.equiv viewables =
  AE.EQ equiv
     equiv_refl
     equiv_sym
     equiv_trans

let cm_identity (x:viewables) : Lemma ((vemp `star` x) `equiv` x)
  = admit()

let star_associative (x y z:viewables) : Lemma (
  ((x `star` y) `star` z) `equiv` (x `star` (y `star` z)))
  = admit()

let star_commutative (x y:viewables) : Lemma ((x `star` y) `equiv` (y `star` x))
  = admit()

let star_congruence (x y z w:viewables) : Lemma
  (requires (x `equiv` z /\ y `equiv` w))
  (ensures ((x `star` y) `equiv` (z `star` w)))
  = admit()

//[@@__reduce__]
inline_for_extraction noextract let rm : AE.cm viewables req =
  AE.CM vemp
     star
     cm_identity
     star_associative
     star_commutative
     star_congruence

inline_for_extraction noextract let canon_viewables () : Tac unit =
  CE.canon_monoid (`req) (`rm)

let canon' (_:unit) : Tac unit =
  or_else (fun _ -> canon_viewables())
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

let rec filter_goals (l:list goal) : Tac (list goal) =
  match l with
  | [] -> []
  | hd::tl ->
      match term_as_formula' (goal_type hd) with
      | Comp (Eq _) _ _ -> hd::filter_goals tl
      | App t _ -> if term_eq t (`squash) then hd::filter_goals tl else filter_goals tl
      | _ -> filter_goals tl

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
      if lnbr = 0 || rnbr = 0 then trefl () else later();
      solve_triv_eqs tl
    | _ -> later(); solve_triv_eqs tl

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
  | _ -> fail "unexpected goal"; false


// Returns true if it successfully solved a goal
// If it returns false, it means it didn't find any solvable goal,
// which should mean only delayed goals are left
let rec pick_next (l:list goal) : Tac bool =
  match l with
  | [] -> false
  | a::q -> if solve_or_delay a then true else (later (); pick_next q)



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
          apply_lemma (`emp_unit_variant)
          ))
        else (later());
        solve_subcomp_post tl
    | _ -> later(); solve_subcomp_post tl

let rec resolve_sel_rec () : Tac unit =
  match goals () with
  | [] -> ()
  | g -> if pick_next g then resolve_sel_rec ()
        else (norm [delta_only [`%delay]]; resolve_sel_rec ())

[@@ resolve_implicits; framing_implicit_sel]
let resolve_sel () : Tac unit =
  let gs = filter_goals (goals()) in
  set_goals gs;
  solve_triv_eqs (goals());
  solve_subcomp_post (goals());
  resolve_sel_rec ()

assume val ref : Type0
assume val ptr (_:ref) : hprop u#1
assume val sel (r:ref) : projection int (ptr r)

let vptr' (r:ref) : viewable =
  { fp = ptr r;
    a = int;
    sel = sel r }

let vptr (r:ref) : viewables = VUnit (vptr' r)

assume val alloc (x:int) : Steel_Sel ref vemp (fun r -> vptr r)
  (fun _ -> True) (fun _ r h1 ->  h1 (vptr r) == x)
assume val free (r:ref) : Steel_Sel unit (vptr r) (fun _ -> vemp) (fun _ -> True) (fun _ _ _ -> True)
assume val read (r:ref) : Steel_Sel int (vptr r) (fun _ -> vptr r)
  (fun _ -> True)
  (fun h0 x h1 -> h0 (vptr r) == h1 (vptr r) /\ x == h1 (vptr r))

assume val ret (#a:Type) (x:a) (p:a -> viewables) (pre:selector (p x) -> GTot prop)
  : Steel_Sel a (p x) p (fun h0 -> pre h0) (fun h0 v h1 -> x == v /\ h0 == h1 /\ pre h1)

assume val h_assert (pre:viewables) (req:req_t pre) :
  Steel_Sel unit pre (fun _ -> pre)
    (fun h -> req h)
    (fun _ _ h1 -> req h1)

assume val h_admit (#a:Type)
  (#[@@framing_implicit_sel] pre:viewables) (#[@@framing_implicit_sel] post:post_t a)
  (#ens:ens_t pre a post) (_:unit) : Steel_Sel a pre post (fun _ -> True) ens

let test0 (r:ref) : Steel_Sel int (vptr r) (fun _ -> vptr r) (fun _ -> True)
  // (fun _ _ _ -> True) =
  // (fun h0 x h1 -> h0 (vptr r) == h1 (vptr r)) =
  (fun h0 x h1 -> x == h1 (vptr r)) =
  let x = read r in
//  h_assert (vptr r) (fun h -> h (vptr r) == x);
  /// assert (1 == 1);
  ret x (fun _ -> vptr r) (fun h -> h (vptr r) == x)

let test1 (x:int) : Steel_Sel ref vemp vptr (fun _ -> True)// (fun _ _ _ -> True) =
 (fun _ r h1 -> h1 (vptr r) == x) =
  let y = alloc x in
//  h_assert (vptr y) (fun _ -> True);
  ret y vptr (fun h -> h (vptr y) == x)

let test8 (x:ref) : Steel_Sel int (vptr x) (fun _ -> vptr x) (fun _ -> True) (fun _ _ _ -> True)
  = let v = read x in
    let y = alloc v in
    let v = read y in
    free y;
    // Can mix assertions
    assert (1 == 1);
    v
