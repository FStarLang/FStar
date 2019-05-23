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
open FStar.Tactics
open FStar.Reflection
open FStar.Classical
open FStar.Tactics.CanonCommSwaps

(* A simple expression canonizer for commutative monoids (working up to 
   some given equivalence relation as opposed to just propositional equality).
   For a canonizer with more features see FStar.Tactics.CanonCommMonoid.fst.

   Based on FStar.Tactics.CanonCommMonoidSimple.fst
*)

(* Only dump when debugging is on *)
//let dump m = if debugging () then dump m

(***** Expression syntax *)

let atom : eqtype = nat

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

let amap (a:Type) = list (atom * a) * a
let const (#a:Type) (xa:a) : amap a = ([], xa)
let select (#a:Type) (x:atom) (am:amap a) : Tot a =
  match assoc #atom #a x (fst am) with
  | Some a -> a
  | _ -> snd am
let update (#a:Type) (x:atom) (xa:a) (am:amap a) : amap a =
  (x, xa)::fst am, snd am

let rec mdenote (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e:exp) : a =
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

let swap (n:nat) :Type = x:nat{x < n-1}

let rec apply_swap_aux (#a:Type) (n:nat) (xs:list a) (s:swap (length xs + n))
  : Pure (list a) (requires True)
                  (ensures (fun zs -> length zs == length xs)) (decreases xs) =
  match xs with
  | [] | [_] -> xs
  | x1 :: x2 :: xs' -> 
      if n = (s <: nat)
      then x2 :: x1 :: xs'
      else x1 :: apply_swap_aux (n+1) (x2 :: xs') s

let apply_swap (#a:Type) = apply_swap_aux #a 0

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

let rec apply_swaps (#a:Type) (xs:list a) (ss:list (swap (length xs))) 
  : Pure (list a) (requires True)
                  (ensures (fun zs -> length zs == length xs)) (decreases ss) =
  match ss with
  | [] -> xs
  | s::ss' -> apply_swaps (apply_swap xs s) ss'

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

let rec permute_via_swaps_correct_aux (p:permute) (pvs:permute_via_swaps p)
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

let sort : permute = List.Tot.sortWith #nat (compare_of_bool (<))

let sort_via_swaps (#a:Type) (am:amap a)  (xs:list atom) 
  : Lemma (exists (ss:swaps_for xs). sort xs == apply_swaps xs ss) =
  List.Tot.Properties.sortWith_permutation #nat (compare_of_bool (<)) xs;
  let (ss:swaps_for xs) = equal_counts_implies_swaps #nat xs (sort xs) in
  assume (sort xs == apply_swaps xs ss)
  // this should just work from the type of ss 
  // (and the postcondition of equal_counts_implies_swaps),
  // but ss gets substituted by its definition in the WP
  // (the same already in FStar.Tactics.CanonCommMonoidSimple.fst)

let rec sort_correct_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs:list atom) 
  : Lemma (xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (sort xs)) =
  permute_via_swaps_correct sort (fun #a am -> sort_via_swaps am) eq m am xs

let sort_correct : permute_correct sort = (fun #a -> sort_correct_aux #a)

(***** Canonicalization tactics *)

[@plugin]
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
    Tot (option nat) (decreases xs) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

// This expects that mult, unit, and t have already been normalized
let rec reification_aux (#a:Type) (ts:list term) (am:amap a)
                        (mult unit t : term) : Tac (exp * list term * amap a) =
  let hd, tl = collect_app_ref t in
  let fatom (t:term) (ts:list term) (am:amap a) : Tac (exp * list term * amap a) =
    match where t ts with
    | Some v -> (Atom v, ts, am)
    | None -> let vfresh = length ts in let z = unquote t in
              (Atom vfresh, ts @ [t], update vfresh z am)
  in
  match inspect hd, list_unref tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1,ts,am) = reification_aux ts am mult unit t1 in
          let (e2,ts,am) = reification_aux ts am mult unit t2 in
          (Mult e1 e2, ts, am))
    else fatom t ts am
  | _, _ ->
    if term_eq t unit
    then (Unit, ts, am)
    else fatom t ts am

let reification (#a:Type) (eq:equiv a) (m:cm a eq) (ts:list term) (am:amap a) (t:term) :
    Tac (exp * list term * amap a) =
  let mult = norm_term [delta] (quote (CM?.mult m)) in
  let unit = norm_term [delta] (quote (CM?.unit m)) in
  let t    = norm_term [delta] t in
  reification_aux ts am mult unit t

let eq_refl (#a:Type) (eq:equiv a) (x:a) 
  : (_:squash (x `EQ?.eq eq` x)) =
  EQ?.reflexivity eq x

let canon_monoid (#a:Type) (eq:equiv a) (m:cm a eq) : Tac unit =
  norm [];
  let t = cur_goal () in 
  // removing top-level squash application
  let sq, rel_xy = collect_app_ref t in
  // unpacking the application of the equivalence relation (lhs `EQ?.eq eq` rhs)
  (match list_unref rel_xy with
   | [(rel_xy,_)] -> (
       let rel, xy = collect_app_ref rel_xy in
       match list_unref xy with 
       // when the relation takes zero implicit arguments
       | [(lhs, Q_Explicit) ; (rhs, Q_Explicit)] -> (
           let (r1, ts, am) = reification eq m [] (const (CM?.unit m)) lhs in
           let (r2, _, am) = reification eq m ts am rhs in
           //dump ("am = " ^ term_to_string (quote am));
           //dump ("r1 = " ^ term_to_string (norm_term [delta;primops] (quote (mdenote eq m am r1))));
           //dump ("r2 = " ^ term_to_string (norm_term [delta;primops] (quote (mdenote eq m am r2))));
           //dump ("before = " ^ term_to_string (norm_term [hnf;delta;primops]
           //   (quote (mdenote eq m am r1 `EQ?.eq eq` mdenote eq m am r2)))); 
           //dump ("current goal" ^ term_to_string (cur_goal ()));
           change_sq (quote (mdenote eq m am r1 `EQ?.eq eq` mdenote eq m am r2));
           //dump ("expected after = " ^ term_to_string (norm_term [delta;primops]
           //   (quote (xsdenote eq m am (canon r1) `EQ?.eq eq`
           //           xsdenote eq m am (canon r2)))));
           apply (`monoid_reflect);
           //dump ("after apply monoid_reflect");
           norm [delta_only [`%canon; `%xsdenote; `%flatten; `%sort;
                             `%select; `%assoc; `%fst; `%__proj__Mktuple2__item___1;
                             `%(@); `%append; `%List.Tot.Base.sortWith;
                             `%List.Tot.Base.partition; `%bool_of_compare; 
                             `%compare_of_bool; //`%EQ?.eq;
                ]; primops];
           apply (quote eq_refl)
           //;dump "after norm in canon_monoid"
         )
       // when the relation takes one implicit argument
       | [_ ; (lhs, Q_Explicit) ; (rhs, Q_Explicit)] -> (
           let (r1, ts, am) = reification eq m [] (const (CM?.unit m)) lhs in
           let (r2, _, am) = reification eq m ts am rhs in
           //dump ("am = " ^ term_to_string (quote am));
           change_sq (quote (mdenote eq m am r1 `EQ?.eq eq` mdenote eq m am r2));
           //dump ("before = " ^ term_to_string (norm_term [delta;primops]
           //   (quote (mdenote eq m am r1 `EQ?.eq eq` mdenote eq m am r2)))); 
           //dump ("expected after = " ^ term_to_string (norm_term [delta;primops]
           //   (quote (xsdenote eq m am (canon r1) `EQ?.eq eq`
           //           xsdenote eq m am (canon r2)))));
           apply (`monoid_reflect);
           //dump ("after apply monoid_reflect");
           norm [delta_only [`%canon; `%xsdenote; `%flatten; `%sort;
                             `%select; `%assoc; `%fst; `%__proj__Mktuple2__item___1;
                             `%(@); `%append; `%List.Tot.Base.sortWith;
                             `%List.Tot.Base.partition; `%bool_of_compare; 
                             `%compare_of_bool; //`%EQ?.eq;
                ]; primops];
           apply (quote eq_refl)
           //;dump "after norm in canon_monoid"
         )
       | _ -> fail "Goal should be a binary relation"
     )
   | _ -> fail "Goal should be squash applied to a binary relation")

(***** Example *)

(*
let test1 (a b c d : int) =
  assert_by_tactic (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1)
  (fun _ -> canon_monoid (equality_equiv int) int_plus_cm)

open FStar.Mul

let test2 =
  assert_by_tactic (forall (a b c d : int). ((b + 1) * 1) * 2 * a * (c * a) * 1 == a * (b + 1) * c * a * 2)
  (fun _ -> ignore (forall_intros()); canon_monoid (equality_equiv int) int_multiply_cm)
*)


/////////////////////////////////////////////


open LowStar.Resource

let req : equiv resource = 
  EQ equal 
     equal_refl 
     equal_symm 
     equal_trans

let rm : cm resource req =
  CM empty_resource 
     (<*>) 
     equal_comm_monoid_left_unit 
     equal_comm_monoid_associativity 
     equal_comm_monoid_commutativity 
     equal_comm_monoid_cong

let resolve_delta (outer inner:term) : Tac unit =

  dump "initial goal";

  refine_intro ();

  dump "after refine_intro";

  flip ();

  dump "after flip";

  canon_monoid req rm;

  dump "after canon_monoid"
  

let test_res1 (outer inner:resource) 
         (#[resolve_delta (quote outer) (quote inner)] 
             delta:resource{(inner <*> delta) `equal` outer})
  : resource = delta
let test_res2 (r1 r2 r3:resource) = 
  admit (); // resolve_delta solves (all) the two goals (finding the 
            // delta and showing that it and inner amount to outer)
            // but in the end F* still reports an error that the
            // (computed) r2 does not satisfy its refinement
  assert (test_res1 (r3 <*> r2 <*> r1) (r1 <*> r3) == r2)


/////////////////////////////////////////////







(*
  match term_as_formula (cur_goal ()) with
  | Comp (Eq (Some t)) t1 t2 ->
      // dump ("t1 =" ^ term_to_string t1 ^
      //     "; t2 =" ^ term_to_string t2);
      if term_eq t (quote a) then
        let (r1, ts, am) = reification eq m [] (const (CM?.unit m)) t1 in
        let (r2, _, am) = reification eq m ts am t2 in
        // dump ("am =" ^ term_to_string (quote am));
        change_sq (quote (mdenote eq m am r1 `EQ?.eq eq` mdenote eq m am r2));
        // dump ("before =" ^ term_to_string (norm_term [delta;primops]
        //   (quote (mdenote eq m am r1 `EQ?.eq eq` mdenote eq m am r2)))); 
        // dump ("expected after =" ^ term_to_string (norm_term [delta;primops]
        //   (quote (xsdenote eq m am (canon r1) `EQ?.eq eq`
        //           xsdenote eq m am (canon r2)))));
        apply (`monoid_reflect);
        // dump ("after apply");
        norm [delta_only [`%canon; `%xsdenote; `%flatten; `%sort;
                `%select; `%assoc; `%fst; `%__proj__Mktuple2__item___1;
                `%(@); `%append; `%List.Tot.Base.sortWith;
                `%List.Tot.Base.partition; `%bool_of_compare; `%compare_of_bool;
                `%EQ?.eq;
           ]; primops]
        //;dump "done"
      else fail "Goal should be an equality at the right monoid type"
  | _ -> fail "Goal should be an equality"
*)
