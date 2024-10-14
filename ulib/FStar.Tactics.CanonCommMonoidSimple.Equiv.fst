(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Tactics.CanonCommMonoidSimple.Equiv

open FStar.Algebra.CommMonoid.Equiv
open FStar.List
open FStar.Classical
open FStar.Tactics.CanonCommSwaps
open FStar.Tactics.V2.Bare

private
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

(* A simple expression canonizer for commutative monoids (working up to
   some given equivalence relation as opposed to just propositional equality).
   For a canonizer with more features see FStar.Tactics.CanonCommMonoid.fst.

   Based on FStar.Tactics.CanonCommMonoidSimple.fst
*)

(* Only dump when debugging is on *)
//let dump m = if debugging () then dump m

(***** Expression syntax *)

// GM: ugh, we had `nat`, but then we get bitten by lack
//     of subtyping over datatypes when we typecheck the amap term
//     we generate (see convert_am).
let atom : eqtype = int

type exp : Type =
  | Unit : exp
  | Mult : exp -> exp -> exp
  | Atom : atom -> exp

let rec exp_to_string (e:exp) : string =
  match e with
  | Unit -> "Unit"
  | Atom x -> "Atom " ^ string_of_int (x <: atom)
  | Mult e1 e2 -> "Mult (" ^ exp_to_string e1
                   ^ ") (" ^ exp_to_string e2 ^ ")"

(***** Expression denotation *)

// Use a map that stores for each atom
// (1) its denotation that should be treated abstractly (type a) and
// (2) user-specified extra information depending on its term (type b)

let amap (a:Type) = list (atom & a) & a
let const (#a:Type) (xa:a) : amap a = ([], xa)
let select (#a:Type) (x:atom) (am:amap a) : Tot a =
  match assoc #atom #a x (fst am) with
  | Some a -> a
  | _ -> snd am
let update (#a:Type) (x:atom) (xa:a) (am:amap a) : amap a =
  (x, xa)::fst am, snd am

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

(***** Flattening expressions to lists of atoms *)

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

(***** Permuting the lists of atoms
       by swapping adjacent elements *)

let permute = list atom -> list atom

// high-level correctness criterion for permutations
let permute_correct (p:permute) =
  #a:Type -> eq:equiv a -> m:cm a eq -> am:amap a -> xs:list atom ->
    Lemma (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (p xs))

// sufficient condition:
// permutation has to be expressible as swaps of adjacent list elements

// In the general case, an arbitrary permutation can be done via swaps.
// (see FStar.Tactics.CanonCommSwaps for a proof)

let rec apply_swap_aux_correct (#a:Type) (n:nat) (eq:equiv a) (m:cm a eq) (am:amap a)
                           (xs:list atom) (s:swap (length xs + n))
  : Lemma (requires True)
      (ensures (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (apply_swap_aux n xs s)))
      (decreases xs) =
  match xs with
  | [] -> EQ?.reflexivity eq (CM?.unit m)
  | [x] -> EQ?.reflexivity eq (select x am)
  | [x1;x2] ->
      if n = (s <: nat)
      then CM?.commutativity m (select x1 am) (select x2 am)
      else EQ?.reflexivity eq (xsdenote eq m am [x1;x2])
  | x1 :: x2 :: xs' ->
      if n = (s <: nat)
      then (
        CM?.associativity m (select x1 am) (select x2 am) (xsdenote eq m am xs');
        EQ?.symmetry eq (CM?.mult m (CM?.mult m (select x1 am) (select x2 am)) (xsdenote eq m am xs'))
                        (CM?.mult m (select x1 am) (CM?.mult m (select x2 am) (xsdenote eq m am xs')));
        CM?.commutativity m (select x1 am) (select x2 am);
        EQ?.reflexivity eq (xsdenote eq m am xs');
        CM?.congruence m (CM?.mult m (select x1 am) (select x2 am)) (xsdenote eq m am xs')
                         (CM?.mult m (select x2 am) (select x1 am)) (xsdenote eq m am xs');
        CM?.associativity m (select x2 am) (select x1 am) (xsdenote eq m am xs');
        EQ?.transitivity eq (CM?.mult m (select x1 am) (CM?.mult m (select x2 am) (xsdenote eq m am xs')))
                            (CM?.mult m (CM?.mult m (select x1 am) (select x2 am)) (xsdenote eq m am xs'))
                            (CM?.mult m (CM?.mult m (select x2 am) (select x1 am)) (xsdenote eq m am xs'));
        EQ?.transitivity eq (CM?.mult m (select x1 am) (CM?.mult m (select x2 am) (xsdenote eq m am xs')))
                            (CM?.mult m (CM?.mult m (select x2 am) (select x1 am)) (xsdenote eq m am xs'))
                            (CM?.mult m (select x2 am) (CM?.mult m (select x1 am) (xsdenote eq m am xs'))))
      else (
        apply_swap_aux_correct (n+1) eq m am (x2 :: xs') s;
        EQ?.reflexivity eq (select x1 am);
        CM?.congruence m (select x1 am) (xsdenote eq m am (x2 :: xs'))
                         (select x1 am) (xsdenote eq m am (apply_swap_aux (n+1) (x2 :: xs') s)))

let apply_swap_correct (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a)
                       (xs:list atom) (s:swap (length xs))
  : Lemma (ensures (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (apply_swap xs s)))
          (decreases xs) =
  apply_swap_aux_correct 0 eq m am xs s

let rec apply_swaps_correct (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a)
                            (xs:list atom) (ss:list (swap (length xs)))
  : Lemma (requires True)
      (ensures (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (apply_swaps xs ss)))
      (decreases ss) =
  match ss with
  | [] -> EQ?.reflexivity eq (xsdenote eq m am xs)
  | s::ss' ->
      apply_swap_correct eq m am xs s;
      apply_swaps_correct eq m am (apply_swap xs s) ss';
      EQ?.transitivity eq (xsdenote eq m am xs)
                          (xsdenote eq m am (apply_swap xs s))
                          (xsdenote eq m am (apply_swaps (apply_swap xs s) ss'))

let permute_via_swaps (p:permute) =
  (#a:Type) -> (am:amap a) -> xs:list atom ->
    Lemma (exists (ss:swaps_for xs). p xs == apply_swaps xs ss)

let permute_via_swaps_correct_aux (p:permute) (pvs:permute_via_swaps p)
                               (#a:Type) (eq:equiv a)(m:cm a eq) (am:amap a) (xs:list atom)
  : Lemma (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (p xs)) =
  pvs am xs;
  assert(exists (ss:swaps_for xs). p xs == apply_swaps xs ss);
  exists_elim (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (p xs))
    (() <: squash (exists (ss:swaps_for xs). p xs == apply_swaps xs ss))
    (fun ss -> apply_swaps_correct eq m am xs ss)

let permute_via_swaps_correct
  (p:permute) (pvs:permute_via_swaps p) : permute_correct p =
     fun #a -> permute_via_swaps_correct_aux p pvs #a

(***** Sorting atoms is a correct permutation
       (since it can be done by swaps) *)

// Here we sort the variable numbers

let sort : permute = List.Tot.Base.sortWith #int (compare_of_bool (<))

let sort_via_swaps (#a:Type) (am:amap a)  (xs:list atom)
  : Lemma (exists (ss:swaps_for xs). sort xs == apply_swaps xs ss) 
  = List.Tot.Properties.sortWith_permutation #int (compare_of_bool (<)) xs;
    let ss = equal_counts_implies_swaps xs (sort xs) in
    ()

let sort_correct_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs:list atom)
  : Lemma (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (sort xs)) =
  permute_via_swaps_correct sort (fun #a am -> sort_via_swaps am) eq m am xs

let sort_correct : permute_correct sort = (fun #a -> sort_correct_aux #a)

(***** Canonicalization tactics *)

let canon (e:exp) = sort (flatten e)

let canon_correct (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e:exp)
  : Lemma (mdenote eq m am e `EQ?.eq eq` xsdenote eq m am (canon e)) =
  flatten_correct eq m am e;
  sort_correct eq m am (flatten e);
  EQ?.transitivity eq (mdenote eq m am e)
                      (xsdenote eq m am (flatten e))
                      (xsdenote eq m am (sort (flatten e)))

let monoid_reflect_orig (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e1 e2:exp)
  : Lemma (requires (xsdenote eq m am (canon e1) `EQ?.eq eq` xsdenote eq m am (canon e2)))
          (ensures (mdenote eq m am e1 `EQ?.eq eq` mdenote eq m am e2)) =
  canon_correct eq m am e1;
  canon_correct eq m am e2;
  EQ?.symmetry eq (mdenote eq m am e2) (xsdenote eq m am (canon e2));
  EQ?.transitivity eq (mdenote eq m am e1)
                      (xsdenote eq m am (canon e1))
                      (xsdenote eq m am (canon e2));
  EQ?.transitivity eq (mdenote eq m am e1)
                      (xsdenote eq m am (canon e2))
                      (mdenote eq m am e2)

let monoid_reflect (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e1 e2:exp)
    (_ : squash (xsdenote eq m am (canon e1) `EQ?.eq eq` xsdenote eq m am (canon e2)))
       : squash (mdenote eq m am e1 `EQ?.eq eq` mdenote eq m am e2) =
  monoid_reflect_orig #a eq m am e1 e2

(* Finds the position of first occurrence of x in xs.
   This is now specialized to terms and their funny term_eq. *)
let rec where_aux (n:nat) (x:term) (xs:list term) :
    Tac (option nat) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

let fatom (t:term) (ts:list term) (am:amap term) : Tac (exp & list term & amap term) =
  match where t ts with
  | Some v -> (Atom v, ts, am)
  | None ->
    let vfresh = length ts in
    let t = norm_term [iota; zeta] t in
    (Atom vfresh, ts @ [t], update vfresh t am)

// This expects that mult, unit, and t have already been normalized
let rec reification_aux (ts:list term) (am:amap term)
                        (mult unit t : term) : Tac (exp & list term & amap term) =
  let hd, tl = collect_app t in
  match inspect hd, tl with
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
    Tac (exp & list term & amap term) =
  let mult = norm_term [iota; zeta; delta] (`CM?.mult (`#m)) in
  let unit = norm_term [iota; zeta; delta] (`CM?.unit (`#m)) in
  let t    = norm_term [iota; zeta] t in
  reification_aux ts am mult unit t

let rec repeat_cong_right_identity (eq: term) (m: term) : Tac unit =
  or_else (fun _ -> apply_lemma (`right_identity))
          (fun _ -> apply_lemma (`CM?.congruence (`#m));
                    split ();
                    apply_lemma (`EQ?.reflexivity (`#eq));
                    repeat_cong_right_identity eq m
                    )

let rec convert_map (m : list (atom & term)) : term =
  match m with
  | [] -> `[]
  | (a, t)::ps ->
      let a = pack (Tv_Const (C_Int a)) in
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
    | Atom n -> let nt = pack (Tv_Const (C_Int n)) in
                (`Atom (`#nt))

let canon_lhs_rhs (eq: term) (m: term) (lhs rhs:term) : Tac unit =
  let m_unit = norm_term [iota; zeta; delta](`CM?.unit (`#m)) in
  let am = const m_unit in (* empty map *)
  let (r1, ts, am) = reification eq m [] am lhs in
  let (r2,  _, am) = reification eq m ts am rhs in
  //dump ("am = " ^ term_to_string (quote am));
  //dump ("r1 = " ^ term_to_string (norm_term [delta;primops] (quote (mdenote eq m am r1))));
  //dump ("r2 = " ^ term_to_string (norm_term [delta;primops] (quote (mdenote eq m am r2))));
  //dump ("before = " ^ term_to_string (norm_term [hnf;delta;primops]
  //   (quote (mdenote eq m am r1 `EQ?.eq eq` mdenote eq m am r2))));
  //dump ("current goal -- " ^ term_to_string (cur_goal ()));
  let am = convert_am am in
  let r1 = quote_exp r1 in
  let r2 = quote_exp r2 in
  change_sq (`(mdenote (`#eq) (`#m) (`#am) (`#r1)
                 `EQ?.eq (`#eq)`
               mdenote (`#eq) (`#m) (`#am) (`#r2)));
  (* dump ("expected after = " ^ term_to_string (norm_term [delta;primops] *)
  (*    (quote (xsdenote eq m am (canon r1) `EQ?.eq eq` *)
  (*            xsdenote eq m am (canon r2))))); *)
  apply (`monoid_reflect);
  //dump ("after apply monoid_reflect");
  norm [iota; zeta; delta_only [`%canon; `%xsdenote; `%flatten; `%sort;
                    `%select; `%assoc; `%fst; `%__proj__Mktuple2__item___1;
                    `%(@); `%append; `%List.Tot.sortWith;
                    `%List.Tot.partition; `%bool_of_compare;
                    `%compare_of_bool;
       ]; primops];
  //dump "before refl";
  or_else (fun _ -> apply_lemma (`(EQ?.reflexivity (`#eq))))
          (fun _ -> repeat_cong_right_identity eq m)

[@@plugin]
let canon_monoid (eq: term) (m: term) : Tac unit =
  norm [iota; zeta];
  let t = cur_goal () in
  // removing top-level squash application
  let sq, rel_xy = collect_app t in
  // unpacking the application of the equivalence relation (lhs `EQ?.eq eq` rhs)
  (match rel_xy with
   | [(rel_xy,_)] -> (
       let rel, xy = collect_app rel_xy in
       if (length xy >= 2)
       then (
         match FStar.List.Tot.Base.index xy (length xy - 2) , FStar.List.Tot.index xy (length xy - 1) with
         | (lhs, Q_Explicit) , (rhs, Q_Explicit) -> canon_lhs_rhs eq m lhs rhs
         | _ -> fail "Goal should have been an application of a binary relation to 2 explicit arguments"
       )
       else (
         fail "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments"
       )
     )
   | _ -> fail "Goal should be squash applied to a binary relation")
