module NewCanon

open FStar.Tactics

open Steel.Memory

let is_uvar (t:term) : Tac bool = match t with
  | Tv_Uvar _ _ -> true
  | _ -> false

(* For a given term t, collect all terms in the list l with the same head symbol *)
let rec get_candidates (t:term) (l:list term) : Tac (list term) =
  let name, _ = collect_app t in
  match l with
  | [] -> []
  | hd::tl ->
      let n, _ = collect_app hd in
      if term_eq n name then (
        hd::(get_candidates t tl)
      ) else get_candidates t tl

(* Try to remove a term that is exactly matching, not just that can be unified *)
let rec trivial_cancel (t:term) (l:list term) =
  match l with
  | [] -> false, l
  | hd::tl ->
      if term_eq hd t then
        // These elements match, we remove them
        true, tl
      else (let b, res = trivial_cancel t tl in b, hd::res)

(* Call trivial_cancel on all elements of l1.
   The first two lists returned are the remainders of l1 and l2.
   The last two lists are the removed parts of l1 and l2, with
   the additional invariant that they are equal *)
let rec trivial_cancels (l1 l2:list term)
  : Tac (list term * list term * list term * list term) =
  match l1 with
  | [] -> [], l2, [], []
  | hd::tl ->
      let b, l2'   = trivial_cancel hd l2 in
      let l1', l2', l1_del, l2_del = trivial_cancels tl l2' in
      (if b then l1' else hd::l1'), l2',
      (if b then hd::l1_del else l1_del), (if b then hd::l2_del else l2_del)

exception Failed
exception Success

(* For a list of candidates l, count the number that can unify with t *)
let rec try_candidates (t:term) (l:list term) : Tac (term * int) =
  match l with
  | [] -> t, 0
  | hd::tl ->
      // Encapsulate unify in a try/with to ensure unification is not actually performed
      let res = try if unify t hd then raise Success else raise Failed
                with | Success -> true | _ -> false in
      let t', n' = try_candidates t tl in
      if res then hd, 1 + n'  else t', n'

(* Remove one term from the list if it can unify. Only to be called when
   try_candidates succeeded *)
let rec remove_from_list (t:term) (l:list term) : Tac (list term) =
  match l with
  | [] -> fail "should not happen"; []
  | hd::tl ->
      if unify t hd then tl else hd::remove_from_list t tl

(* Check if two lists of slprops are equivalent by recursively calling
   try_candidates.
   Assumes that only l2 contains terms with the head symbol unresolved.
   It returns all elements that were not resolved during this iteration *)
let rec equivalent_lists_once (l1 l2 l1_del l2_del:list term)
  : Tac (list term * list term * list term * list term) =
  match l1 with
  | [] -> [], l2, l1_del, l2_del
  | hd::tl ->
    let t, n = try_candidates hd l2 in
    if n = 0 then
      fail ("not equiv: no candidate found for scrutinee " ^ term_to_string hd)
    else if n = 1 then (
      let l2 = remove_from_list t l2 in
      equivalent_lists_once tl l2 (hd::l1_del) (t::l2_del)
    ) else
      // Too many candidates for this scrutinee
      let rem1, rem2, l1'_del, l2'_del = equivalent_lists_once tl l2 l1_del l2_del in
      hd::rem1, rem2, l1'_del, l2'_del

let get_head (l:list term) : term = match l with
  | [] -> `()
  | hd::_ -> hd

(* Recursively calls equivalent_lists_once.
   Stops when we're done with unification, or when we didn't make any progress
   If we didn't make any progress, we have too many candidates for some terms.
   Accumulates rewritings of l1 and l2 in l1_del and l2_del, with the invariant
   that the two lists are unifiable at any point
   *)
let rec equivalent_lists' (n:nat) (l1 l2 l1_del l2_del:list term)
  : Tac (list term * list term) =
  match l1 with
  | [] -> begin match l2 with
    | [] -> dump "equiv"; (l1_del, l2_del)
    | [hd] ->
      // Succeed if there is only one uvar left in l2, which can be therefore
      // be unified with emp
      if is_uvar hd then (dump "equiv with remaining emp uvar"; ((`emp)::l1_del, hd::l2_del))
      else (dump "not equiv"; (l1_del, l2_del))
    | _ -> dump "not equiv"; (l1_del, l2_del)
    end
  | _ ->
    let rem1, rem2, l1_del', l2_del' = equivalent_lists_once l1 l2 l1_del l2_del in
    let n' = List.Tot.length rem1 in
    if n' >= n then
      // Should always be smaller or equal to n
      // If it is equal, no progress was made.
      fail ("too many candidates for scrutinee " ^ term_to_string (get_head rem1))
    else equivalent_lists' n' rem1 rem2 l1_del' l2_del'

(* First remove all trivially equal terms, then try to decide equivalence *)
let equivalent_lists (l1 l2:list term) : Tac (list term * list term) =
  let l1, l2, l1_del, l2_del = trivial_cancels l1 l2 in
  let n = List.Tot.length l1 in
  let l1_del, l2_del = equivalent_lists' n l1 l2 l1_del l2_del in
  l1_del, l2_del

open FStar.Reflection.Derived.Lemmas

let rec list_to_string (l:list term) : Tac string =
  match l with
  | [] -> "end"
  | hd::tl -> term_to_string hd ^ " " ^ list_to_string tl


noeq
type exp : Type =
  | Unit : exp
  | Mult : exp -> exp -> exp
  | Atom : term -> exp

let rec reification_aux (mult unit t:term) : Tac (exp * list term) =
  let hd, tl = collect_app_ref t in
  match inspect hd, List.Tot.Base.list_unref tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1, ts1) = reification_aux mult unit t1 in
          let (e2, ts2) = reification_aux mult unit t2 in
          (Mult e1 e2, ts1 `List.Tot.append` ts2))
    else Atom t, [t]
  | _, _ ->
    if term_eq t unit
    // Do not add emps to the list of slprops
    then (Unit, [])
    else Atom t, [t]


let reification (eq: term) (m: term) (t:term) :
    Tac (exp * list term) =
  let open FStar.Algebra.CommMonoid.Equiv in
  let mult = norm_term [iota; zeta; delta] (`CM?.mult (`#m)) in
  let unit = norm_term [iota; zeta; delta] (`CM?.unit (`#m)) in
  let t    = norm_term [iota; zeta] t in
  reification_aux mult unit t


let canon_l_r (eq: term) (m: term) (lhs rhs:term) : Tac unit =
  let open FStar.Algebra.CommMonoid.Equiv in
  let m_unit = norm_term [iota; zeta; delta](`CM?.unit (`#m)) in
  let (r1, ts1) = reification eq m lhs in
  let (r2, ts2) = reification eq m rhs in
  dump (list_to_string ts1);
  dump (list_to_string ts2);
  dump "ending";
  let l1, l2 = equivalent_lists ts1 ts2 in
  ()


let canon_monoid (eq:term) (m:term) : Tac unit =
  norm [iota; zeta];
  let t = cur_goal () in
  // removing top-level squash application
  let sq, rel_xy = collect_app_ref t in
  // unpacking the application of the equivalence relation (lhs `EQ?.eq eq` rhs)
  (match rel_xy with
   | [(rel_xy,_)] -> (
       let open FStar.List.Tot.Base in
       let rel, xy = collect_app_ref rel_xy in
       if (length xy >= 2)
       then (
         match index xy (length xy - 2) , index xy (length xy - 1) with
         | (lhs, Q_Explicit) , (rhs, Q_Explicit) ->
           canon_l_r eq m lhs rhs
         | _ -> fail "Goal should have been an application of a binary relation to 2 explicit arguments"
       )
       else (
         fail "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments"
       )
     )
   | _ -> fail "Goal should be squash applied to a binary relation")

#set-options "--print_implicits"


(* Try to integrate it into larger tactic *)

open Steel.FramingEffect

let canon' () : Tac unit =
  canon_monoid (`Steel.Memory.Tactics.req) (`Steel.Memory.Tactics.rm)

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
                       dump "can_be_split";
                       canon'()));
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
                       dump "can_be_split_forall";
                       canon'()));
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
                       dump "subcomp";
                       canon'()))
          ))
        else (later());
        solve_subcomp_post tl
    | _ -> later(); solve_subcomp_post tl

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

assume val p (#n:int) (n2:int) : slprop
assume val q (#n:int) (#n':int) (n2:int) : slprop

assume val palloc (#n:int) (n2:int) : SteelT unit emp (fun _ -> p #n n2)

let l:list int = [0; 1; 2]

let rec string_of_list (l:list slprop) = match l with
  | [] -> ""
  | a::q -> term_to_string (`a) ^ " " ^ string_of_list q


assume val ref : Type0
assume val ptr (_:ref) : slprop u#1

assume val alloc (x:int)  : SteelT ref emp (fun y -> ptr y)
assume val free (r:ref) : SteelT unit (ptr r) (fun _ -> emp)
assume val read (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)



let test1 (x:int) : SteelT unit emp (fun _ -> p #1 1)  =
  let _ = palloc #_ 1 in ()


// let f (#r:slprop) =
//   let terms:slprop =
//     (p #0 1) `star` (p #2 1) in
// //    [(`p #0 1); (`p #2 1); (`p #1 0); (`q #1 #2 1); (`q #_ #3 1)] in
// //    [(p #0 1); (p #2 1); (p #1 0); (q #i1 #3 1); (q #1 #2 1); (p #2 2)] in
//   let p_terms:slprop =
//     (p #0 1) `star` (p #i1 1) in
//     // A uvar is also added at the head in the assert .. by
// //    [(`p #2 1); (`p #_ 0); (`p #_ 1); (`q #_ #3 1); (`q #_ #_ 1)] in
//   // The assertion fails because implicits are not unified in this case,
//   // but the important part is the result of equivalent_lists, given as
//   // a dump in the tactic.
//   assert (terms `equiv` p_terms) by (
// //    let u = fresh_uvar (Some (`slprop)) in
//     // dump (string_of_list [r]);
//     // dump (string_of_list terms);
//     dump "test";
//     apply_lemma (`equiv_symmetric);
//     dump "here"
//     // let l1_del, l2_del = equivalent_lists terms (r::p_terms) in
//     // dump (string_of_list l1_del);
//     // dump (string_of_list l2_del)
//     );
//   ()
