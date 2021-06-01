module Steel.Effect.Common

open Steel.Memory

irreducible let framing_implicit : unit = ()
irreducible let __reduce__ : unit = ()
irreducible let smt_fallback : unit = ()

let return_pre (p:slprop u#1) : slprop u#1 = p

type pre_t = slprop u#1
type post_t (a:Type) = a -> slprop u#1

let maybe_emp (framed:bool) (frame:pre_t) = if framed then frame == emp else True
let maybe_emp_dep (#a:Type) (framed:bool) (frame:post_t a) =
  if framed then (forall x. frame x == emp) else True

// Needed to avoid some logical vs prop issues during unification with no subtyping
let true_p : prop = True

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

val sl_implies (p q:slprop u#1) : Type0

val sl_implies_reflexive (p:slprop u#1)
: Lemma (p `sl_implies` p)
  [SMTPat (p `sl_implies` p)]

val sl_implies_interp (p q:slprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures forall (m:mem) (f:slprop). interp (p `star` f) m ==>  interp (q `star` f) m)
  [SMTPat (p `sl_implies` q)]

val sl_implies_interp_emp (p q:slprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures forall (m:mem). interp p m ==>  interp q m)
  [SMTPat (p `sl_implies` q)]

let can_be_split (t1 t2:pre_t) = t1 `sl_implies` t2

let can_be_split_dep (p:prop) (t1 t2:pre_t) = p ==> t1 `sl_implies` t2

let can_be_split_forall (#a:Type) (t1 t2:post_t a) =
  forall (x:a). t1 x `sl_implies` t2 x

let can_be_split_forall_dep (#a:Type) (p:a -> prop) (t1 t2:post_t a) =
  forall (x:a). p x ==> t1 x `sl_implies` t2 x

val destruct_can_be_split_forall_dep (#a:Type) (p:a -> prop) (t1 t2:post_t a) : Lemma
  (requires forall x. p x == True /\ t1 x `sl_implies` t2 x)
  (ensures can_be_split_forall_dep p t1 t2)

val equiv_forall (#a:Type) (t1 t2:post_t a) : Type0

val equiv_forall_refl (#a:Type) (t:post_t a)
  : Lemma (t `equiv_forall` t)

val equiv_forall_split (#a:Type) (t1 t2:post_t a)
  : Lemma (requires t1 `equiv_forall` t2)
          (ensures can_be_split_forall t1 t2 /\ can_be_split_forall t2 t1)
          [SMTPat (t1 `equiv_forall` t2)]

val equiv_forall_elim (#a:Type) (t1 t2:post_t a)
  : Lemma (requires (forall (x:a). t1 x `equiv` t2 x))
          (ensures t1 `equiv_forall` t2)

let can_be_split_post (#a #b:Type) (t1:a -> post_t b) (t2:post_t b) =
  forall (x:a). equiv_forall (t1 x) t2

val can_be_split_post_elim (#a #b:Type) (t1:a -> post_t b) (t2:post_t b)
  : Lemma (requires (forall (x:a) (y:b). t1 x y `equiv` t2 y))
          (ensures t1 `can_be_split_post` t2)

val can_be_split_forall_frame (#a:Type) (p q:post_t a) (frame:slprop u#1) (x:a)
 : Lemma (requires can_be_split_forall p q)
         (ensures (frame `star` p x)  `sl_implies` (frame `star` q x))

/// Tactic for inferring frame automatically

val equiv_sl_implies (p1 p2:slprop) : Lemma
  (requires p1 `equiv` p2)
  (ensures p1 `sl_implies` p2)

val lemma_sl_implies_refl (p:slprop) : Lemma
  (ensures p `sl_implies` p)

open FStar.Tactics

(* TODO: Remove once it lands in master ulib/ *)
exception Yes

let name_appears_in (nm:name) (t:term) : Tac bool =
  let ff (t : term) : Tac term =
    match t with
    | Tv_FVar fv ->
      if inspect_fv fv = nm then
        raise Yes;
      t
    | t -> t
  in
  try ignore (visit_tm ff t); false with
  | Yes -> true
  | e -> raise e

let term_appears_in (t:term) (i:term) : Tac bool = name_appears_in (explode_qn (term_to_string t)) i

let atom : eqtype = int

let rec atoms_to_string (l:list atom) = match l with
  | [] -> ""
  | hd::tl -> string_of_int hd ^ " " ^ atoms_to_string tl

type exp : Type =
  | Unit : exp
  | Mult : exp -> exp -> exp
  | Atom : atom -> exp

let amap (a:Type) = list (atom * a) * a
let const (#a:Type) (xa:a) : amap a = ([], xa)
let select (#a:Type) (x:atom) (am:amap a) : Tot a =
  match List.Tot.Base.assoc #atom #a x (fst am) with
  | Some a -> a
  | _ -> snd am
let update (#a:Type) (x:atom) (xa:a) (am:amap a) : amap a =
  (x, xa)::fst am, snd am

let is_uvar (t:term) : Tac bool = match t with
  | Tv_Uvar _ _ -> true
  | Tv_App _ _ ->
      let hd, args = collect_app t in
      Tv_Uvar? hd
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
let rec trivial_cancel (t:atom) (l:list atom) =
  match l with
  | [] -> false, l
  | hd::tl ->
      if hd = t then
        // These elements match, we remove them
        true, tl
      else (let b, res = trivial_cancel t tl in b, hd::res)

(* Call trivial_cancel on all elements of l1.
   The first two lists returned are the remainders of l1 and l2.
   The last two lists are the removed parts of l1 and l2, with
   the additional invariant that they are equal *)
let rec trivial_cancels (l1 l2:list atom) (am:amap term)
  : Tac (list atom * list atom * list atom * list atom) =
  match l1 with
  | [] -> [], l2, [], []
  | hd::tl ->
      let b, l2'   = trivial_cancel hd l2 in
      let l1', l2', l1_del, l2_del = trivial_cancels tl l2' am in
      (if b then l1' else hd::l1'), l2',
      (if b then hd::l1_del else l1_del), (if b then hd::l2_del else l2_del)

exception Failed
exception Success

(* For a list of candidates l, count the number that can unify with t.
   Does not try to unify with a uvar, this will be done at the very end.
   Tries to unify with slprops with a different head symbol, it might
   be an abbreviation
 *)
let rec try_candidates (t:atom) (l:list atom) (am:amap term) : Tac (atom * int) =
  match l with
  | [] -> t, 0
  | hd::tl ->
      if is_uvar (select hd am) then (try_candidates t tl am)
      else
        // Encapsulate unify in a try/with to ensure unification is not actually performed
        let res = try if unify (select t am) (select hd am) then raise Success else raise Failed
                  with | Success -> true | _ -> false in
        let t', n' = try_candidates t tl am in
        if res then hd, 1 + n'  else t', n'

(* Remove the given term from the list. Only to be called when
   try_candidates succeeded *)
let rec remove_from_list (t:atom) (l:list atom) : Tac (list atom) =
  match l with
  | [] -> fail "atom in remove_from_list not found: should not happen"; []
  | hd::tl -> if t = hd then tl else hd::remove_from_list t tl

(* Check if two lists of slprops are equivalent by recursively calling
   try_candidates.
   Assumes that only l2 contains terms with the head symbol unresolved.
   It returns all elements that were not resolved during this iteration *)
let rec equivalent_lists_once (l1 l2 l1_del l2_del:list atom) (am:amap term)
  : Tac (list atom * list atom * list atom * list atom) =
  match l1 with
  | [] -> [], l2, l1_del, l2_del
  | hd::tl ->
    let t, n = try_candidates hd l2 am in
    // if n = 0 then
    //   fail ("not equiv: no candidate found for scrutinee " ^ term_to_string (select hd am))
    if n = 1 then (
      let l2 = remove_from_list t l2 in
      equivalent_lists_once tl l2 (hd::l1_del) (t::l2_del) am
    ) else
      // Either too many candidates for this scrutinee, or no candidate but the uvar
      let rem1, rem2, l1'_del, l2'_del = equivalent_lists_once tl l2 l1_del l2_del am in
      hd::rem1, rem2, l1'_del, l2'_del

let get_head (l:list atom) (am:amap term) : term = match l with
  | [] -> `()
  | hd::_ -> select hd am

let is_only_uvar (l:list atom) (am:amap term) : Tac bool =
  if List.Tot.Base.length l = 1 then is_uvar (select (List.Tot.Base.hd l) am)
  else false

(* Assumes that u is a uvar, checks that all variables in l can be unified with it.
   Later in the tactic, the uvar will be unified to a star of l *)
let rec try_unifying_remaining (l:list atom) (u:term) (am:amap term) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
      try if unify u (select hd am) then raise Success else raise Failed with
      | Success -> try_unifying_remaining tl u am
      | _ -> fail ("could not find candidate for scrutinee " ^ term_to_string (select hd am))

let rec print_atoms (l:list atom) (am:amap term) : Tac string =
  match l with
  | [] -> ""
  | [hd] -> term_to_string (select hd am)
  | hd::tl -> term_to_string (select hd am) ^ " * " ^ print_atoms tl am

let is_smt_binder (b:binder) : Tac bool =
  let (bv, aqual) = inspect_binder b in
  let l = snd aqual in
  not (List.Tot.isEmpty (filter (fun t -> term_eq t (`smt_fallback)) l))

let rec new_args_for_smt_attrs (env:env) (l:list argv) (ty:typ) : Tac (list argv * list term) =
  match l, inspect ty with
  | (arg, aqualv)::tl, Tv_Arrow binder comp ->
    let needs_smt = is_smt_binder binder in
    let new_hd =
      if needs_smt then (
        let arg_ty = tc env arg in
        let uvar = fresh_uvar (Some arg_ty) in
        unshelve uvar;
        flip ();
        (uvar, aqualv)
      ) else (arg, aqualv)
    in
    begin
    match inspect_comp comp with
    | C_Total ty2 _ ->
      let tl_argv, tl_terms = new_args_for_smt_attrs env tl ty2 in
      new_hd::tl_argv, (if needs_smt then arg::tl_terms else tl_terms)
    | _ -> fail "computation type not supported in definition of slprops"
    end
  | [], Tv_FVar fv -> [], []
  | _ -> fail "should not happen. Is an slprop partially applied?"


let rewrite_term_for_smt (env:env) (am:amap term * list term) (a:atom) : Tac (amap term * list term)
  = let am, prev_uvar_terms = am in
    let term = select a am in
    let hd, args = collect_app term in
    let t = tc env hd in
    let new_args, uvar_terms = new_args_for_smt_attrs env args t in
    let new_term = mk_app hd new_args in
    update a new_term am, uvar_terms@prev_uvar_terms

let fail_atoms (#a:Type) (l1 l2:list atom) (am:amap term) : Tac a
  = fail ("could not find a solution for unifying\n" ^ print_atoms l1 am ^ "\nand\n" ^ print_atoms l2 am)

let rec equivalent_lists_fallback (n:nat) (l1 l2 l1_del l2_del:list atom) (am:amap term)
  : Tac (list atom * list atom * bool) =
  match l1 with
  | [] -> begin match l2 with
    | [] -> (l1_del, l2_del, false)
    | [hd] ->
      // Succeed if there is only one uvar left in l2, which can be therefore
      // be unified with emp
      if is_uvar (select hd am) then (
        // xsdenote is left associative: We put hd at the top to get
        // ?u `star` p <==> emp `star` p
        (l1_del, hd :: l2_del, true))
      else fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    | _ -> fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    end
  | _ ->
    if is_only_uvar l2 am then (
      // Terms left in l1, but only a uvar left in l2.
      // Put all terms left at the end of l1_rem, so that they can be unified
      // with exactly the uvar because of the structure of xsdenote
      try_unifying_remaining l1 (get_head l2 am) am;
      l1_del @ l1, l2_del @ l2, false
    ) else
      let rem1, rem2, l1_del', l2_del' = equivalent_lists_once l1 l2 l1_del l2_del am in
      let n' = List.Tot.length rem1 in
      if n' >= n then
        // Should always be smaller or equal to n
        // If it is equal, no progress was made.
        fail_atoms rem1 rem2 am
        // fail ("could not find a solution for unifying\n" ^ print_atoms rem1 am ^ "\nand\n" ^ print_atoms rem2 am)
//        fail ("could not find candidate for this scrutinee " ^ term_to_string (get_head rem2 am))
      else equivalent_lists_fallback n' rem1 rem2 l1_del' l2_del' am

let replace_smt_uvars (l1 l2:list atom) (am:amap term) : Tac (amap term * list term)
  = let env = cur_env () in
    fold_left (rewrite_term_for_smt env) (am, []) l2

(* Recursively calls equivalent_lists_once.
   Stops when we're done with unification, or when we didn't make any progress
   If we didn't make any progress, we have too many candidates for some terms.
   Accumulates rewritings of l1 and l2 in l1_del and l2_del, with the invariant
   that the two lists are unifiable at any point
   The boolean indicates if there is a leftover empty frame
   *)
let rec equivalent_lists' (n:nat) (use_smt:bool) (l1 l2 l1_del l2_del:list atom) (am:amap term)
  : Tac (list atom * list atom * bool * list term) =
  match l1 with
  | [] -> begin match l2 with
    | [] -> (l1_del, l2_del, false, [])
    | [hd] ->
      // Succeed if there is only one uvar left in l2, which can be therefore
      // be unified with emp
      if is_uvar (select hd am) then (
        // xsdenote is left associative: We put hd at the top to get
        // ?u `star` p <==> emp `star` p
        (l1_del, hd :: l2_del, true, []))
      else fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    | _ -> fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    end
  | _ ->
    if is_only_uvar l2 am then (
      // Terms left in l1, but only a uvar left in l2.
      // Put all terms left at the end of l1_rem, so that they can be unified
      // with exactly the uvar because of the structure of xsdenote
      try_unifying_remaining l1 (get_head l2 am) am;
      l1_del @ l1, l2_del @ l2, false, []
    ) else
      let rem1, rem2, l1_del', l2_del' = equivalent_lists_once l1 l2 l1_del l2_del am in
      let n' = List.Tot.length rem1 in
      if n' >= n then (
        // Should always be smaller or equal to n
        // If it is equal, no progress was made.
        if use_smt then
          // SMT fallback is allowed
          let new_am, uvar_terms  = replace_smt_uvars rem1 rem2 am in
          let l1_f, l2_f, b = equivalent_lists_fallback n' rem1 rem2 l1_del' l2_del' new_am in
          l1_f, l2_f, b, uvar_terms
        else fail_atoms rem1 rem2 am
      ) else equivalent_lists' n' use_smt rem1 rem2 l1_del' l2_del' am

(* Checks if term for atom t unifies with fall uvars in l *)
let rec unifies_with_all_uvars (t:term) (l:list atom) (am:amap term) : Tac bool =
  match l with
  | [] -> true
  | hd::tl ->
      if unifies_with_all_uvars t tl am then (
        // Unified with tail, try this term
        let hd_t = select hd am in
        if is_uvar hd_t then (
          // The head term is a uvar, try unifying
          try if unify t hd_t then raise Success else raise Failed
          with | Success -> true | _ -> false
        ) else true // The uvar is not a head term, we do not need to try it
      ) else false

(* Puts all terms in l1 that cannot unify with the uvars in l2 at the top:
   They need to be solved first *)
let rec most_restricted_at_top (l1 l2:list atom) (am:amap term) : Tac (list atom) =
  match l1 with
  | [] -> []
  | hd::tl ->
    if unifies_with_all_uvars (select hd am) l2 am then (most_restricted_at_top tl l2 am)@[hd]
    else hd::(most_restricted_at_top tl l2 am)

(* First remove all trivially equal terms, then try to decide equivalence.
   Assumes that l1 does not contain any slprop uvar.
   If it succeeds, returns permutations of l1, l2, and a boolean indicating
   if l2 has a trailing empty frame to be unified
*)
let equivalent_lists (use_smt:bool) (l1 l2:list atom) (am:amap term)
  : Tac (list atom * list atom * bool * list term)
= let l1, l2, l1_del, l2_del = trivial_cancels l1 l2 am in
  let l1 = most_restricted_at_top l1 l2 am in
  let n = List.Tot.length l1 in
  let l1_del, l2_del, emp_frame, uvar_terms = equivalent_lists' n use_smt l1 l2 l1_del l2_del am in
  l1_del, l2_del, emp_frame, uvar_terms

open FStar.Reflection.Derived.Lemmas

let rec list_to_string (l:list term) : Tac string =
  match l with
  | [] -> "end"
  | hd::tl -> term_to_string hd ^ " " ^ list_to_string tl

open FStar.Algebra.CommMonoid.Equiv

let rec mdenote (#a:Type u#aa) (eq:equiv a) (m:cm a eq) (am:amap a) (e:exp) : a =
  match e with
  | Unit -> CM?.unit m
  | Atom x -> select x am
  | Mult e1 e2 -> CM?.mult m (mdenote eq m am e1) (mdenote eq m am e2)

let rec xsdenote (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs:list atom) : a =
  match xs with
  | [] -> CM?.unit m
  | [x] -> select x am
  | x::xs' -> CM?.mult m (select x am) (xsdenote eq m am xs')

let rec flatten (e:exp) : list atom =
  match e with
  | Unit -> []
  | Atom x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

let rec flatten_correct_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs1 xs2:list atom)
  : Lemma (xsdenote eq m am (xs1 @ xs2) `EQ?.eq eq` CM?.mult m (xsdenote eq m am xs1)
                                                               (xsdenote eq m am xs2)) =
  match xs1 with
  | [] ->
      CM?.identity m (xsdenote eq m am xs2);
      EQ?.symmetry eq (CM?.mult m (CM?.unit m) (xsdenote eq m am xs2)) (xsdenote eq m am xs2)
  | [x] -> (
      if (Nil? xs2)
      then (right_identity eq m (select x am);
            EQ?.symmetry eq (CM?.mult m (select x am) (CM?.unit m)) (select x am))
      else EQ?.reflexivity eq (CM?.mult m (xsdenote eq m am [x]) (xsdenote eq m am xs2)))
  | x::xs1' ->
      flatten_correct_aux eq m am xs1' xs2;
      EQ?.reflexivity eq (select x am);
      CM?.congruence m (select x am) (xsdenote eq m am (xs1' @ xs2))
                       (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2));
      CM?.associativity m (select x am) (xsdenote eq m am xs1') (xsdenote eq m am xs2);
      EQ?.symmetry eq (CM?.mult m (CM?.mult m (select x am) (xsdenote eq m am xs1')) (xsdenote eq m am xs2))
                      (CM?.mult m (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2)));
      EQ?.transitivity eq (CM?.mult m (select x am) (xsdenote eq m am (xs1' @ xs2)))
                          (CM?.mult m (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2)))
                          (CM?.mult m (CM?.mult m (select x am) (xsdenote eq m am xs1')) (xsdenote eq m am xs2))

let rec flatten_correct (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e:exp)
  : Lemma (mdenote eq m am e `EQ?.eq eq` xsdenote eq m am (flatten e)) =
  match e with
  | Unit -> EQ?.reflexivity eq (CM?.unit m)
  | Atom x -> EQ?.reflexivity eq (select x am)
  | Mult e1 e2 ->
      flatten_correct_aux eq m am (flatten e1) (flatten e2);
      EQ?.symmetry eq (xsdenote eq m am (flatten e1 @ flatten e2))
                      (CM?.mult m (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2)));
      flatten_correct eq m am e1;
      flatten_correct eq m am e2;
      CM?.congruence m (mdenote eq m am e1) (mdenote eq m am e2)
                       (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2));
      EQ?.transitivity eq (CM?.mult m (mdenote eq m am e1) (mdenote eq m am e2))
                          (CM?.mult m (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2)))
                          (xsdenote eq m am (flatten e1 @ flatten e2))

let monoid_reflect (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e1 e2:exp)
    (_ : squash (xsdenote eq m am (flatten e1) `EQ?.eq eq` xsdenote eq m am (flatten e2)))
       : squash (mdenote eq m am e1 `EQ?.eq eq` mdenote eq m am e2) =
    flatten_correct eq m am e1;
    flatten_correct eq m am e2;
    EQ?.symmetry eq (mdenote eq m am e2) (xsdenote eq m am (flatten e2));
    EQ?.transitivity eq
      (xsdenote eq m am (flatten e1))
      (xsdenote eq m am (flatten e2))
      (mdenote eq m am e2);
    EQ?.transitivity eq
      (mdenote eq m am e1)
      (xsdenote eq m am (flatten e1))
      (mdenote eq m am e2)

// Here we sort the variable numbers

let permute = list atom -> list atom
let sort : permute = List.Tot.Base.sortWith #int (List.Tot.Base.compare_of_bool (<))

#push-options "--fuel 1 --ifuel 1"

let lemma_xsdenote_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (hd:atom) (tl:list atom)
  : Lemma (xsdenote eq m am (hd::tl) `EQ?.eq eq`
         (CM?.mult m (select hd am) (xsdenote eq m am tl)))
  = match tl with
    | [] ->
      assert (xsdenote eq m am (hd::tl) == select hd am);
      CM?.identity m (select hd am);
      EQ?.symmetry eq (CM?.unit m `CM?.mult m` select hd am) (select hd am);
      CM?.commutativity m (CM?.unit m) (select hd am);
      EQ?.transitivity eq
        (xsdenote eq m am (hd::tl))
        (CM?.unit m `CM?.mult m` select hd am)
        (CM?.mult m (select hd am) (xsdenote eq m am tl))
    | _ -> EQ?.reflexivity eq (xsdenote eq m am (hd::tl))

let rec partition_equiv (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (pivot:atom) (q:list atom)
  : Lemma
    (let open FStar.List.Tot.Base in
     let hi, lo = partition (bool_of_compare (compare_of_bool (<)) pivot) q in
     EQ?.eq eq
      (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
      (xsdenote eq m am q))
   = let open FStar.List.Tot.Base in
     let f = bool_of_compare (compare_of_bool (<)) pivot in
     let hi, lo = partition f q in
     match q with
     | [] -> CM?.identity m (xsdenote eq m am hi)
     | hd::tl ->
         let l1, l2 = partition f tl in
         partition_equiv eq m am pivot tl;
         assert (EQ?.eq eq
           (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2)
           (xsdenote eq m am tl));

         EQ?.reflexivity eq (xsdenote eq m am l1);
         EQ?.reflexivity eq (xsdenote eq m am l2);
         EQ?.reflexivity eq (xsdenote eq m am hi);
         EQ?.reflexivity eq (xsdenote eq m am lo);


         if f hd then begin
           assert (hi == hd::l1 /\ lo == l2);
           lemma_xsdenote_aux eq m am hd l1;
           CM?.congruence m
             (xsdenote eq m am hi)
             (xsdenote eq m am lo)
             (select hd am `CM?.mult m` xsdenote eq m am l1)
             (xsdenote eq m am l2);
           CM?.associativity m
             (select hd am)
             (xsdenote eq m am l1)
             (xsdenote eq m am l2);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             ((select hd am `CM?.mult m` xsdenote eq m am l1) `CM?.mult m` xsdenote eq m am l2)
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2));

           EQ?.reflexivity eq (select hd am);
           CM?.congruence m
             (select hd am)
             (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2)
             (select hd am)
             (xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2))
             (select hd am `CM?.mult m` xsdenote eq m am tl);

           lemma_xsdenote_aux eq m am hd tl;
           EQ?.symmetry eq
             (xsdenote eq m am (hd::tl))
             (select hd am `CM?.mult m` xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` xsdenote eq m am tl)
             (xsdenote eq m am (hd::tl))

         end else begin
           assert (hi == l1 /\ lo == hd::l2);
           lemma_xsdenote_aux eq m am hd l2;
           CM?.congruence m
             (xsdenote eq m am hi)
             (xsdenote eq m am lo)
             (xsdenote eq m am l1)
             (select hd am `CM?.mult m` xsdenote eq m am l2);
           CM?.commutativity m
             (xsdenote eq m am l1)
             (select hd am `CM?.mult m` xsdenote eq m am l2);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (xsdenote eq m am l1 `CM?.mult m` (select hd am `CM?.mult m` xsdenote eq m am l2))
             ((select hd am `CM?.mult m` xsdenote eq m am l2) `CM?.mult m` xsdenote eq m am l1);

           CM?.associativity m
             (select hd am)
             (xsdenote eq m am l2)
             (xsdenote eq m am l1);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             ((select hd am `CM?.mult m` xsdenote eq m am l2) `CM?.mult m` xsdenote eq m am l1)
             (select hd am `CM?.mult m` (xsdenote eq m am l2 `CM?.mult m` xsdenote eq m am l1));

           CM?.commutativity m (xsdenote eq m am l2) (xsdenote eq m am l1);
           EQ?.reflexivity eq (select hd am);
           CM?.congruence m
             (select hd am)
             (xsdenote eq m am l2 `CM?.mult m` xsdenote eq m am l1)
             (select hd am)
             (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` (xsdenote eq m am l2 `CM?.mult m` xsdenote eq m am l1))
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2));

           CM?.congruence m
             (select hd am)
             (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2)
             (select hd am)
             (xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2))
             (select hd am `CM?.mult m` xsdenote eq m am tl);

           lemma_xsdenote_aux eq m am hd tl;
           EQ?.symmetry eq
             (xsdenote eq m am (hd::tl))
             (select hd am `CM?.mult m` xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` xsdenote eq m am tl)
             (xsdenote eq m am (hd::tl))
         end

let rec sort_correct_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs:list atom)
  : Lemma (requires True)
          (ensures xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (sort xs))
          (decreases (FStar.List.Tot.Base.length xs))
  = match xs with
  | [] -> EQ?.reflexivity eq (xsdenote eq m am [])
  | pivot::q ->
      let open FStar.List.Tot.Base in
      let f:int -> int -> int = compare_of_bool (<) in
      let hi, lo = partition (bool_of_compare f pivot) q in
      flatten_correct_aux eq m am (sort lo) (pivot::sort hi);
      assert (xsdenote eq m am (sort xs) `EQ?.eq eq`
        CM?.mult m (xsdenote eq m am (sort lo))
                   (xsdenote eq m am (pivot::sort hi)));

      lemma_xsdenote_aux eq m am pivot (sort hi);

      EQ?.reflexivity eq (xsdenote eq m am (sort lo));
      CM?.congruence m
        (xsdenote eq m am (sort lo))
        (xsdenote eq m am (pivot::sort hi))
        (xsdenote eq m am (sort lo))
        (select pivot am `CM?.mult m` xsdenote eq m am (sort hi));
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (xsdenote eq m am (sort lo) `CM?.mult m` xsdenote eq m am (pivot::sort hi))
        (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi)));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi))));

      CM?.commutativity m
        (xsdenote eq m am (sort lo))
        (select pivot am `CM?.mult m` xsdenote eq m am (sort hi));
      CM?.associativity m
        (select pivot am)
        (xsdenote eq m am (sort hi))
        (xsdenote eq m am (sort lo));
      EQ?.transitivity eq
         (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi)))
        ((select pivot am `CM?.mult m` xsdenote eq m am (sort hi)) `CM?.mult m` xsdenote eq m am (sort lo))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo)));
      EQ?.transitivity eq
         (xsdenote eq m am (sort xs))
         (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi)))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo)));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo))));


      partition_length (bool_of_compare f pivot) q;
      sort_correct_aux eq m am hi;
      sort_correct_aux eq m am lo;
      EQ?.symmetry eq (xsdenote eq m am lo) (xsdenote eq m am (sort lo));
      EQ?.symmetry eq (xsdenote eq m am hi) (xsdenote eq m am (sort hi));
      CM?.congruence m
        (xsdenote eq m am (sort hi))
        (xsdenote eq m am (sort lo))
        (xsdenote eq m am hi)
        (xsdenote eq m am lo);
      assert (EQ?.eq eq
        (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo))
        (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo));

      EQ?.reflexivity eq (select pivot am);
      CM?.congruence m
        (select pivot am)
        (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo))
        (select pivot am)
        (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo);
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo)))
        (select pivot am `CM?.mult m` (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)));

      partition_equiv eq m am pivot q;
      CM?.congruence m
        (select pivot am)
        (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
        (select pivot am)
        (xsdenote eq m am q);
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo))
        (select pivot am `CM?.mult m` (xsdenote eq m am q));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am q)));

      lemma_xsdenote_aux eq m am pivot q;
      EQ?.symmetry eq
        (xsdenote eq m am (pivot::q))
        (select pivot am `CM?.mult m` (xsdenote eq m am q));
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am q))
        (xsdenote eq m am xs);
      EQ?.symmetry eq (xsdenote eq m am (sort xs)) (xsdenote eq m am xs)

#pop-options

#push-options "--fuel 0 --ifuel 0"

let smt_reflexivity (#a:Type) (eq:equiv a) (x y:a)
  : Lemma (requires x == y)
          (ensures EQ?.eq eq x y)
  = EQ?.reflexivity eq x

let identity_left_smt (#a:Type) (eq:equiv a) (m:cm a eq) (x y:a)
  : Lemma
    (requires x == y)
    (ensures EQ?.eq eq x (CM?.mult m (CM?.unit m) y))
  = CM?.identity m x;
    EQ?.symmetry eq (CM?.mult m (CM?.unit m) x) x

let identity_left (#a:Type) (eq:equiv a) (m:cm a eq) (x:a)
  : Lemma (EQ?.eq eq x (CM?.mult m (CM?.unit m) x))
  = CM?.identity m x;
    EQ?.symmetry eq (CM?.mult m (CM?.unit m) x) x

let identity_right_diff (#a:Type) (eq:equiv a) (m:cm a eq) (x y:a) : Lemma
  (requires EQ?.eq eq x y)
  (ensures EQ?.eq eq (CM?.mult m x (CM?.unit m)) y)
  = right_identity eq m x;
    EQ?.transitivity eq (CM?.mult m x (CM?.unit m)) x y

let rec dismiss_slprops () : Tac unit =
  match term_as_formula' (cur_goal ()) with
    | App t _ -> if term_eq t (`squash) then () else (dismiss(); dismiss_slprops ())
    | _ -> dismiss(); dismiss_slprops ()

let rec n_identity_left (n:int) (eq m:term) : Tac unit
  = if n = 0 then (
      apply_lemma (`(EQ?.reflexivity (`#eq)));
      // Cleaning up, in case a uvar has been generated here. It'll be solved later
      set_goals [])
    else (
      apply_lemma (`identity_right_diff (`#eq) (`#m));
      // Drop the slprops generated, they will be solved later
      dismiss_slprops ();
      n_identity_left (n-1) eq m
    )

let equivalent_sorted (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (l1 l2 l1' l2':list atom)
    : Lemma (requires
              sort l1 == sort l1' /\
              sort l2 == sort l2' /\
              xsdenote eq m am l1 `EQ?.eq eq` xsdenote eq m am l2)
           (ensures xsdenote eq m am l1' `EQ?.eq eq` xsdenote eq m am l2')
  = sort_correct_aux eq m am l1';
    sort_correct_aux eq m am l1;
    EQ?.symmetry eq (xsdenote eq m am l1) (xsdenote eq m am (sort l1));
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am (sort l1'))
      (xsdenote eq m am l1);
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am l1)
      (xsdenote eq m am l2);
    sort_correct_aux eq m am l2;
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am l2)
      (xsdenote eq m am (sort l2));
    sort_correct_aux eq m am l2';
    EQ?.symmetry eq (xsdenote eq m am l2') (xsdenote eq m am (sort l2'));
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am (sort l2))
      (xsdenote eq m am l2')

#pop-options

(* Finds the position of first occurrence of x in xs.
   This is now specialized to terms and their funny term_eq. *)
let rec where_aux (n:nat) (x:term) (xs:list term) :
    Tot (option nat) (decreases xs) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

let fatom (t:term) (ts:list term) (am:amap term) : Tac (exp * list term * amap term) =
  match where t ts with
  | Some v -> (Atom v, ts, am)
  | None ->
    let vfresh = List.Tot.Base.length ts in
    let t = norm_term [iota; zeta] t in
    (Atom vfresh, ts @ [t], update vfresh t am)

// This expects that mult, unit, and t have already been normalized
let rec reification_aux (ts:list term) (am:amap term)
                        (mult unit t : term) : Tac (exp * list term * amap term) =
  let hd, tl = collect_app_ref t in
  match inspect hd, List.Tot.Base.list_unref tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1, ts, am) = reification_aux ts am mult unit t1 in
          let (e2, ts, am) = reification_aux ts am mult unit t2 in
          (Mult e1 e2, ts, am))
    else fatom t ts am
  | _, _ ->
    if term_eq t unit
    then (Unit, ts, am)
    else fatom t ts am

let reification (eq: term) (m: term) (ts:list term) (am:amap term) (t:term) :
    Tac (exp * list term * amap term) =
  let mult = norm_term [iota; zeta; delta] (`CM?.mult (`#m)) in
  let unit = norm_term [iota; zeta; delta] (`CM?.unit (`#m)) in
  let t    = norm_term [iota; zeta] t in
  reification_aux ts am mult unit t

let rec convert_map (m : list (atom * term)) : term =
  match m with
  | [] -> `[]
  | (a, t)::ps ->
      let a = pack_ln (Tv_Const (C_Int a)) in
      (* let t = norm_term [delta] t in *)
      `((`#a, (`#t)) :: (`#(convert_map ps)))


(* `am` is an amap (basically a list) of terms, each representing a value
of type `a` (whichever we are canonicalizing). This functions converts
`am` into a single `term` of type `amap a`, suitable to call `mdenote` with *)
let convert_am (am : amap term) : term =
  let (map, def) = am in
  (* let def = norm_term [delta] def in *)
  `( (`#(convert_map map), `#def) )

let rec quote_exp (e:exp) : term =
    match e with
    | Unit -> (`Unit)
    | Mult e1 e2 -> (`Mult (`#(quote_exp e1)) (`#(quote_exp e2)))
    | Atom n -> let nt = pack_ln (Tv_Const (C_Int n)) in
                (`Atom (`#nt))

let rec quote_atoms (l:list atom) = match l with
  | [] -> `[]
  | hd::tl -> let nt = pack_ln (Tv_Const (C_Int hd)) in
              (`Cons (`#nt) (`#(quote_atoms tl)))

let normal_steps = [primops; iota; zeta; delta_only [
          `%mdenote; `%select; `%List.Tot.Base.assoc; `%List.Tot.Base.append;
          `%flatten; `%sort;
          `%List.Tot.Base.sortWith; `%List.Tot.Base.partition;
          `%List.Tot.Base.bool_of_compare; `%List.Tot.Base.compare_of_bool;
          `%fst; `%__proj__Mktuple2__item___1;
          `%snd; `%__proj__Mktuple2__item___2;
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%Steel.Memory.Tactics.rm]]

let normal (#a:Type) (x:a) : a = FStar.Pervasives.norm normal_steps x

let normal_elim (x:Type0) : Lemma
  (requires x)
  (ensures normal x)
  = ()

exception Result of list atom * list atom * bool * list term

let close_equality_typ' (t:term) : Tac unit =
  let f = term_as_formula' t in
  match f with
  | Comp (Eq (Some u)) l _ -> if is_uvar u then (unshelve u; exact_with_ref (tc (cur_env()) l))
  | _ -> ()

let close_equality_typ (t:term) : Tac unit =
  let ff = fun t' -> close_equality_typ' t'; t' in
  ignore (visit_tm ff t)

let canon_l_r (use_smt:bool) (eq: term) (m: term) (pr:term) (pr_bind:term) (lhs rhs:term) : Tac unit =
  let m_unit = norm_term [iota; zeta; delta](`CM?.unit (`#m)) in
  let am = const m_unit in (* empty map *)
  let (r1_raw, ts, am) = reification eq m [] am lhs in
  let (r2_raw,  _, am) = reification eq m ts am rhs in

// Encapsulating this in a try/with to avoid spawning uvars for smt_fallback
  let l1_raw, l2_raw, emp_frame, uvar_terms =
    try
      let res = equivalent_lists use_smt (flatten r1_raw) (flatten r2_raw) am in
      raise (Result res) with
    | TacticFailure m -> fail m
    | Result res -> res
    | _ -> fail "uncaught exception in equivalent_lists"
  in

  let am = convert_am am in
  let r1 = quote_exp r1_raw in
  let r2 = quote_exp r2_raw in
  let l1 = quote_atoms l1_raw in
  let l2 = quote_atoms l2_raw in
  change_sq (`(normal (mdenote (`#eq) (`#m) (`#am) (`#r1)
                 `EQ?.eq (`#eq)`
               mdenote (`#eq) (`#m) (`#am) (`#r2))));
  apply_lemma (`normal_elim);

  apply (`monoid_reflect );


  apply_lemma (`equivalent_sorted (`#eq) (`#m) (`#am) (`#l1) (`#l2));
  let g = goals () in
  if List.Tot.Base.length g = 0 then
    // The application of equivalent_sorted seems to sometimes solve
    // all goals
    ()
  else (
    norm [primops; iota; zeta; delta_only
      [`%xsdenote; `%select; `%List.Tot.Base.assoc; `%List.Tot.Base.append;
        `%flatten; `%sort;
        `%List.Tot.Base.sortWith; `%List.Tot.Base.partition;
        `%List.Tot.Base.bool_of_compare; `%List.Tot.Base.compare_of_bool;
        `%fst; `%__proj__Mktuple2__item___1;
        `%snd; `%__proj__Mktuple2__item___2;
        `%__proj__CM__item__unit;
        `%__proj__CM__item__mult;
        `%Steel.Memory.Tactics.rm

        ]];

    split();
    split();
    // equivalent_lists should have built valid permutations.
    // If that's not the case, it is a bug in equivalent_lists
    or_else trefl (fun _ -> fail "first equivalent_lists did not build a valid permutation");
    or_else trefl (fun _ -> fail "second equivalent_lists did not build a valid permutation");

    match uvar_terms with
    | [] -> // Closing unneded prop uvar
            if unify pr (`true_p) then () else fail "could not unify SMT prop with True";
            if emp_frame then apply_lemma (`identity_left (`#eq) (`#m))
            else apply_lemma (`(EQ?.reflexivity (`#eq)))
    | l -> if emp_frame then (
             apply_lemma (`identity_left_smt (`#eq) (`#m))
           ) else (
             apply_lemma (`smt_reflexivity (`#eq))
           );
           t_trefl true;
           close_equality_typ (cur_goal());
           exact (`(FStar.Squash.return_squash (`#pr_bind)))
 )

let canon_monoid (use_smt:bool) (eq:term) (m:term) (pr:term) (pr_bind:term) : Tac unit =
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
           canon_l_r use_smt eq m pr pr_bind lhs rhs
         | _ -> fail "Goal should have been an application of a binary relation to 2 explicit arguments"
       )
       else (
         fail "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments"
       )
     )
   | _ -> fail "Goal should be squash applied to a binary relation")

(* Try to integrate it into larger tactic *)

let canon' (use_smt:bool) (pr:term) (pr_bind:term) : Tac unit =
  canon_monoid use_smt (`Steel.Memory.Tactics.req) (`Steel.Memory.Tactics.rm) pr pr_bind

let rec slterm_nbr_uvars (t:term) : Tac int =
  match inspect t with
  | Tv_Uvar _ _ -> 1
  | Tv_App _ _ ->
    let hd, args = collect_app t in
    if term_eq hd (`star) then

      // Only count the number of unresolved slprops, not program implicits
      fold_left (fun n (x, _) -> n + slterm_nbr_uvars x) 0 args
    else if is_uvar hd then 1
    else 0
  | Tv_Abs _ t -> slterm_nbr_uvars t
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
                      if rnbr = 0 then apply_lemma (`Steel.Memory.Tactics.equiv_sym);

                       norm [delta_only [
                              `%__proj__CM__item__unit;
                              `%__proj__CM__item__mult;
                              `%Steel.Memory.Tactics.rm;
                              `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                              `%fst; `%snd];
                            delta_attr [`%__reduce__];
                            primops; iota; zeta];
                       canon' false (`true_p) (`true_p)));
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen

let solve_can_be_split_dep (args:list argv) : Tac bool =
  match args with
  | [(p, _); (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ ->
          norm [delta_only [`%can_be_split]];
          let p_bind = implies_intro () in
          or_else
            (fun _ ->
              let b = unify p (`true_p) in
              if not b then fail "could not unify SMT prop with True";
              apply_lemma (`lemma_sl_implies_refl))
            (fun _ ->
              apply_lemma (`equiv_sl_implies);
              // TODO: Do this count in a better way
              if lnbr <> 0 && rnbr = 0 then apply_lemma (`Steel.Memory.Tactics.equiv_sym);
              or_else (fun _ ->  flip()) (fun _ -> ());
              norm [delta_only [
                     `%__proj__CM__item__unit;
                     `%__proj__CM__item__mult;
                     `%Steel.Memory.Tactics.rm;
                     `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                     `%fst; `%snd];
                   delta_attr [`%__reduce__];
                   primops; iota; zeta];
              canon' true p p_bind));
        true

      ) else false

  | _ -> fail "ill-formed can_be_split_dep"

let emp_unit_variant (p:slprop) : Lemma
   (ensures can_be_split p (p `star` emp))
  = Classical.forall_intro emp_unit;
    equiv_symmetric (p `star` emp) p;
    equiv_sl_implies p (p `star` emp)

let solve_can_be_split_forall (args:list argv) : Tac bool =
  match args with
  | [_; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ ->
          ignore (forall_intro());
          norm [delta_only [`%can_be_split_forall]];
          or_else (fun _ -> apply_lemma (`lemma_sl_implies_refl))
            (fun _ ->
            apply_lemma (`equiv_sl_implies);
            // TODO: Do this count in a better way
            if lnbr <> 0 && rnbr = 0 then apply_lemma (`Steel.Memory.Tactics.equiv_sym);
            or_else (fun _ ->  flip()) (fun _ -> ());
            norm [delta_only [
                   `%__proj__CM__item__unit;
                   `%__proj__CM__item__mult;
                   `%Steel.Memory.Tactics.rm;
                   `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                   `%fst; `%snd];
                 delta_attr [`%__reduce__];
                 primops; iota; zeta];
            canon' false (`true_p) (`true_p)));
        true
      ) else false

  | _ -> fail "Ill-formed can_be_split_forall, should not happen"

let solve_can_be_split_forall_dep (args:list argv) : Tac bool =
  match args with
  | [_; (pr, _); (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ ->
          let x = forall_intro() in
          let pr = mk_app pr [(binder_to_term x, Q_Explicit)] in
          norm [delta_only [`%can_be_split_forall_dep]];
          let pr_bind = implies_intro () in
          or_else
            (fun _ ->
              let b = unify pr (`true_p) in
              if not b then fail "could not unify SMT prop with True";
              apply_lemma (`lemma_sl_implies_refl))
            (fun _ ->
            apply_lemma (`equiv_sl_implies);
            // TODO: Do this count in a better way
            if lnbr <> 0 && rnbr = 0 then apply_lemma (`Steel.Memory.Tactics.equiv_sym);
            or_else (fun _ ->  flip()) (fun _ -> ());
            norm [delta_only [
                   `%__proj__CM__item__unit;
                   `%__proj__CM__item__mult;
                   `%Steel.Memory.Tactics.rm;
                   `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                   `%fst; `%snd];
                 delta_attr [`%__reduce__];
                 primops; iota; zeta];
            canon' true pr pr_bind));
        true

      ) else false

  | _ -> fail "Ill-formed can_be_split_forall_dep, should not happen"

let solve_equiv_forall (args:list argv) : Tac bool =
  match args with
  | [_; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ ->
          or_else (fun _ -> apply_lemma (`equiv_forall_refl))
                  (fun _ ->
                      apply_lemma (`equiv_forall_elim);
                      match goals () with
                      | [] -> ()
                      | _ ->
                        dismiss_slprops ();
                        ignore (forall_intro());
                        // TODO: Do this count in a better way
                        if lnbr <> 0 && rnbr = 0 then apply_lemma (`Steel.Memory.Tactics.equiv_sym);
                        or_else (fun _ ->  flip()) (fun _ -> ());
                        norm [delta_only [
                                `%__proj__CM__item__unit;
                                `%__proj__CM__item__mult;
                                `%Steel.Memory.Tactics.rm;
                                `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                                `%fst; `%snd];
                              delta_attr [`%__reduce__];
                              primops; iota; zeta];
                        canon' false (`true_p) (`true_p)));
        true
      ) else false

  | _ -> fail "Ill-formed equiv_forall, should not happen"

let solve_equiv (args:list argv) : Tac bool =
  match args with
  | [(t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
        if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ ->  // TODO: Do this count in a better way
                       if lnbr <> 0 && rnbr = 0 then apply_lemma (`Steel.Memory.Tactics.equiv_sym);
                       or_else (fun _ ->  flip()) (fun _ -> ());
                       norm [delta_only [
                               `%__proj__CM__item__unit;
                               `%__proj__CM__item__mult;
                               `%Steel.Memory.Tactics.rm;
                               `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                               `%fst; `%snd];
                             delta_attr [`%__reduce__];
                             primops; iota; zeta];
                       canon' false (`true_p) (`true_p));
        true
      ) else false

  | _ -> fail "ill-formed equiv"


let solve_can_be_split_post (args:list argv) : Tac bool =
  match args with
  | [_; _; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> norm[];
                      let g = _cur_goal () in
                      ignore (forall_intro());
              or_else (fun _ -> apply_lemma (`equiv_forall_refl))
                      (fun _ ->
                      apply_lemma (`equiv_forall_elim);
                      match goals () with
                      | [] -> ()
                      | _ ->
                        dismiss_slprops ();
                        ignore (forall_intro());
                        // TODO: Do this count in a better way
                        if lnbr <> 0 && rnbr = 0 then apply_lemma (`Steel.Memory.Tactics.equiv_sym);
                        or_else (fun _ ->  flip()) (fun _ -> ());
                        norm [delta_only [
                                `%__proj__CM__item__unit;
                                `%__proj__CM__item__mult;
                                `%Steel.Memory.Tactics.rm;
                                `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                                `%fst; `%snd];
                              delta_attr [`%__reduce__];
                              primops; iota; zeta];
                        canon' false (`true_p) (`true_p)));
        true
      ) else false

  | _ -> fail "ill-formed can_be_split_post"

let is_return_eq (l r:term) : Tac bool =
  let nl, al = collect_app l in
  let nr, ar = collect_app r in
  term_eq nl (`return_pre) || term_eq nr (`return_pre)

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


let rec solve_all_eqs (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        trefl();
        solve_all_eqs tl
    | _ -> later(); solve_all_eqs tl

// It is important to not normalize the return_pre eqs goals before unifying
// See test7 in FramingTestSuite for a detailed explanation
let rec solve_return_eqs (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        trefl();
        solve_return_eqs tl
    | _ -> later(); solve_return_eqs tl

/// Strip annotations in a goal, to get to the underlying slprop equivalence
let goal_to_equiv (t:term) (loc:string) : Tac unit
  = if term_appears_in (`can_be_split) t then (
      norm [delta_only [`%can_be_split]];
      apply_lemma (`equiv_sl_implies)
    ) else if term_appears_in (`can_be_split_forall) t then (
      ignore (forall_intro ());
      norm [delta_only [`%can_be_split_forall]];
      apply_lemma (`equiv_sl_implies)
    ) else if term_appears_in (`equiv_forall) t then (
      apply_lemma (`equiv_forall_elim);
      ignore (forall_intro())
    ) else if term_appears_in (`can_be_split_post) t then (
      apply_lemma (`can_be_split_post_elim);
      dismiss_slprops();
      ignore (forall_intro ());
      ignore (forall_intro ())
    ) else if term_appears_in (`can_be_split_dep) t then (
      fail ("can_be_split_dep not supported in " ^ loc)
    ) else if term_appears_in (`can_be_split_forall_dep) t then (
      apply_lemma (`destruct_can_be_split_forall_dep);
      // Ignore the prop term that just got created
      dismiss ();
      ignore (forall_intro());
      split();
      // Now closing the prop that is unused here.
      trefl ();

      // Finally rewriting sl_implies into equiv
      apply_lemma (`equiv_sl_implies)
    ) else
      // This should never happen
      fail (loc ^ " goal in unexpected position")

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
  // Beta-reduce the goal first if possible
  norm [];
  let f = term_as_formula' (cur_goal ()) in
  match f with
  | App _ t ->
      let hd, args = collect_app t in
      if term_eq hd (`can_be_split) then solve_can_be_split args
      else if term_eq hd (`can_be_split_forall) then solve_can_be_split_forall args
      else if term_eq hd (`equiv_forall) then solve_equiv_forall args
      else if term_eq hd (`can_be_split_post) then solve_can_be_split_post args
      else if term_eq hd (`Steel.Memory.equiv) then solve_equiv args
      else if term_eq hd (`can_be_split_dep) then solve_can_be_split_dep args
      else if term_eq hd (`can_be_split_forall_dep) then solve_can_be_split_forall_dep args
      else false
  | Comp (Eq _) l r ->
    let lnbr = List.Tot.length (FStar.Reflection.Builtins.free_uvars l) in
    let rnbr = List.Tot.length (FStar.Reflection.Builtins.free_uvars r) in
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
    norm [];
    // TODO: If it picks a goal it cannot solve yet, try all the other ones?
    if pick_next g then resolve_tac ()
    else fail "Could not make progress, no solvable goal found"


let rec resolve_tac_logical () : Tac unit =
  match goals () with
  | [] -> ()
  | g ->
    if pick_next g then resolve_tac_logical ()
    else
      // This is only for requires/ensures constraints, which are equalities
      // There should always be a scheduling of constraints, but it can happen
      // that some uvar for the type of an equality is not resolved.
      // If we reach this point, we try to simply call the unifier instead of failing directly
      solve_all_eqs g


let typ_contains_req_ens (t:term) : Tac bool =
  let name, _ = collect_app t in
  if term_eq name (`req_t) || term_eq name (`ens_t) || term_eq name (`pure_wp) then true
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


// Solve the maybe_emp goals:
// Normalize to unfold maybe_emp(_dep) and the reduce the if/then/else, and
// solve the goal (either an equality through trefl, or True through trivial)
let rec solve_maybe_emps (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (cur_goal ()) in (
    match f with
    | App _ t ->
      let hd, args = collect_app t in
      if term_eq hd (`maybe_emp) then
        focus (fun _ ->
          (norm [delta_only [`%maybe_emp]; iota; zeta; primops; simplify];
          or_else trivial trefl))
      else if term_eq hd (`maybe_emp_dep) then
        focus (fun _ ->
          (norm [delta_only [`%maybe_emp_dep]; iota; zeta; primops; simplify];
          or_else trivial (fun _ -> ignore (forall_intro ()); trefl()) )
        )
      else later()
    | _ -> later()
    );
    solve_maybe_emps tl

let rec norm_return_pre (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl -> norm [delta_only [`%return_pre]]; later(); norm_return_pre tl

[@@ resolve_implicits; framing_implicit; plugin]
let init_resolve_tac () : Tac unit =
  // We split goals between framing goals, about slprops (slgs)
  // and goals related to requires/ensures, that depend on slprops (loggs)
  let slgs, loggs = filter_goals (goals()) in

  // We first solve the slprops
  set_goals slgs;

  // We solve all the maybe_emp goals first: All "extra" frames are directly set to emp
  solve_maybe_emps (goals ());

  // We first solve all indirection equalities that will not lead to imprecise unification
  // i.e. we can solve all equalities inserted by layered effects, except the ones corresponding
  // to the preconditions of a pure return
  solve_indirection_eqs (goals());

  // To debug, it is best to look at the goals at this stage. Uncomment the next line
  // dump "initial goals";

  // We can now solve the equalities for returns
  solve_return_eqs (goals());

  // It is important to not normalize the return_pre equalities before solving them
  // Else, we lose some variables dependencies, leading to the tactic being stuck
  // See test7 in FramingTestSuite for more explanations of what is failing
  // Once unification has been done, we can then safely normalize and remove all return_pre
  norm_return_pre (goals());

  // Finally running the core of the tactic, scheduling and solving goals
  resolve_tac ();

  // We now solve the requires/ensures goals, which are all equalities
  // All slprops are resolved by now
  set_goals loggs;

  resolve_tac_logical ()
