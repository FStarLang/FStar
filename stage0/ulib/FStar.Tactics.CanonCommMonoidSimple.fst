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
module FStar.Tactics.CanonCommMonoidSimple

open FStar.Algebra.CommMonoid
open FStar.List
open FStar.Reflection.V2
open FStar.Tactics.V2.Bare
open FStar.Classical
open FStar.Tactics.CanonCommSwaps

let term_eq = FStar.Stubs.Tactics.V2.Builtins.term_eq_old

(* A simple expression canonizer for commutative monoids.
   For a canonizer with more features see FStar.Tactics.CanonCommMonoid.fst.

   Inspired by:
   - http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html
   - http://poleiro.info/posts/2015-04-13-writing-reflective-tactics.html
*)

(* Only dump when debugging is on *)
let dump m = if debugging () then dump m

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

let amap (a:Type) = list (atom & a) & a
let const (#a:Type) (xa:a) : amap a = ([], xa)
let select (#a:Type) (x:atom) (am:amap a) : Tot a =
  match assoc #atom #a x (fst am) with
  | Some a -> a
  | _ -> snd am
let update (#a:Type) (x:atom) (xa:a) (am:amap a) : amap a =
  (x, xa)::fst am, snd am

let rec mdenote (#a:Type) (m:cm a) (am:amap a) (e:exp) : a =
  match e with
  | Unit -> CM?.unit m
  | Atom x -> select x am
  | Mult e1 e2 -> CM?.mult m (mdenote m am e1) (mdenote m am e2)

let rec xsdenote (#a:Type) (m:cm a) (am:amap a) (xs:list atom) : a =
  match xs with
  | [] -> CM?.unit m
  | [x] -> select x am
  | x::xs' -> CM?.mult m (select x am) (xsdenote m am xs')

(***** Flattening expressions to lists of atoms *)

let rec flatten (e:exp) : list atom =
  match e with
  | Unit -> []
  | Atom x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

let rec flatten_correct_aux (#a:Type) (m:cm a) (am:amap a) (xs1 xs2:list atom) :
    Lemma (xsdenote m am (xs1 @ xs2) == CM?.mult m (xsdenote m am xs1)
                                                   (xsdenote m am xs2)) =
  match xs1 with
  | [] -> CM?.identity m (xsdenote m am xs2)
  | [x] -> if (Nil? xs2) then right_identity m (select x am)
  | x::xs1' -> (CM?.associativity m (select x am)
                      (xsdenote m am xs1') (xsdenote m am xs2);
                flatten_correct_aux m am xs1' xs2)

let rec flatten_correct (#a:Type) (m:cm a) (am:amap a) (e:exp) :
    Lemma (mdenote m am e == xsdenote m am (flatten e)) =
  match e with
  | Unit | Atom _ -> ()
  | Mult e1 e2 -> flatten_correct_aux m am (flatten e1) (flatten e2);
                  flatten_correct m am e1; flatten_correct m am e2

(***** Permuting the lists of atoms
       by swapping adjacent elements *)

let permute = list atom -> list atom

// high-level correctness criterion for permutations
let permute_correct (p:permute) =
  #a:Type -> m:cm a -> am:amap a -> xs:list atom ->
    Lemma (xsdenote m am xs == xsdenote m am (p xs))

// sufficient condition:
// permutation has to be expressible as swaps of adjacent list elements

// In the general case, an arbitrary permutation can be done via swaps.
// (see FStar.Tactics.CanonCommSwaps for a proof)


let rec apply_swap_aux_correct (#a:Type) (n:nat) (m:cm a) (am:amap a)
                           (xs:list atom) (s:swap (length xs + n)) :
    Lemma (requires True)
      (ensures (xsdenote m am xs == xsdenote m am (apply_swap_aux n xs s)))
      (decreases xs) =
  match xs with
  | [] | [_] -> ()
  | x1 :: x2 :: xs' ->
      if n = (s <: nat)
      then (// x1 + (x2 + xs') =a (x1 + x2) + xs'
            //                 =c (x2 + x1) + xs' = a x2 + (x1 + xs')
           let a = CM?.associativity m in
           a (select x1 am) (select x2 am) (xsdenote m am xs');
           a (select x2 am) (select x1 am) (xsdenote m am xs');
           CM?.commutativity m (select x1 am) (select x2 am))
      else apply_swap_aux_correct (n+1) m am (x2 :: xs') s

let apply_swap_correct (#a:Type) (m:cm a) (am:amap a)
                       (xs:list atom) (s:swap (length xs)):
    Lemma (ensures (xsdenote m am xs == xsdenote m am (apply_swap xs s)))
          (decreases xs) = apply_swap_aux_correct 0 m am xs s

let rec apply_swaps_correct (#a:Type) (m:cm a) (am:amap a)
                            (xs:list atom) (ss:list (swap (length xs))):
    Lemma (requires True)
      (ensures (xsdenote m am xs == xsdenote m am (apply_swaps xs ss)))
      (decreases ss) =
  match ss with
  | [] -> ()
  | s::ss' -> apply_swap_correct m am xs s;
              apply_swaps_correct m am (apply_swap xs s) ss'

let permute_via_swaps (p:permute) =
  (#a:Type) -> (am:amap a) -> xs:list atom ->
    Lemma (exists ss. p xs == apply_swaps xs ss)

let permute_via_swaps_correct_aux (p:permute) (pvs:permute_via_swaps p)
                               (#a:Type) (m:cm a) (am:amap a) (xs:list atom) :
    Lemma (xsdenote m am xs == xsdenote m am (p xs)) =
  pvs am xs;
  assert(exists ss. p xs == apply_swaps xs ss);
  exists_elim (xsdenote m am xs == xsdenote m am (p xs))
    (() <: squash (exists ss. p xs == apply_swaps xs ss))
    (fun ss -> apply_swaps_correct m am xs ss)

let permute_via_swaps_correct
  (p:permute) (pvs:permute_via_swaps p) : permute_correct p =
     fun #a -> permute_via_swaps_correct_aux p pvs #a

(***** Sorting atoms is a correct permutation
       (since it can be done by swaps) *)

// Here we sort the variable numbers

let sort : permute = List.Tot.Base.sortWith #nat (compare_of_bool (<))

let sort_via_swaps (#a:Type) (am : amap a)  (xs:list atom)
  : Lemma (exists ss. sort xs == apply_swaps xs ss)
  =
  List.Tot.Properties.sortWith_permutation #nat (compare_of_bool (<)) xs;
  let ss = equal_counts_implies_swaps #nat xs (sort xs) in
  ()

let sort_correct_aux (#a:Type) (m:cm a) (am:amap a) (xs:list atom) :
    Lemma (xsdenote m am xs == xsdenote m am (sort xs)) =
  permute_via_swaps_correct sort (fun #a am -> sort_via_swaps am) m am xs

let sort_correct : permute_correct sort = (fun #a -> sort_correct_aux #a)

(***** Canonicalization tactics *)

(* [@@plugin] *)
let canon (e:exp) = sort (flatten e)

let canon_correct (#a:Type) (m:cm a) (am:amap a) (e:exp) :
    Lemma (mdenote m am e == xsdenote m am (canon e)) =
  flatten_correct m am e; sort_correct m am (flatten e)

let monoid_reflect_orig (#a:Type) (m:cm a) (am:amap a) (e1 e2:exp) :
  Lemma (requires (xsdenote m am (canon e1) == xsdenote m am (canon e2)))
        (ensures (mdenote m am e1 == mdenote m am e2)) =
  canon_correct m am e1; canon_correct m am e2

let monoid_reflect (#a:Type) (m:cm a) (am:amap a) (e1 e2:exp)
    (_ : squash (xsdenote m am (canon e1) == xsdenote m am (canon e2)))
       : squash (mdenote m am e1 == mdenote m am e2) =
  canon_correct m am e1; canon_correct m am e2

(* Finds the position of first occurrence of x in xs.
   This is now specialized to terms and their funny term_eq. *)
let rec where_aux (n:nat) (x:term) (xs:list term) :
    Tac (option nat) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

// This expects that mult, unit, and t have already been normalized
let rec reification_aux (#a:Type) (ts:list term) (am:amap a)
                        (mult unit t : term) : Tac (exp & list term & amap a) =
  let hd, tl = collect_app_ref t in
  let fatom (t:term) (ts:list term) (am:amap a) : Tac (exp & list term & amap a) =
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

let reification (#a:Type) (m:cm a) (ts:list term) (am:amap a) (t:term) :
    Tac (exp & list term & amap a) =
  let mult = norm_term [delta;zeta;iota] (quote (CM?.mult m)) in
  let unit = norm_term [delta;zeta;iota] (quote (CM?.unit m)) in
  let t    = norm_term [delta;zeta;iota] t in
  reification_aux ts am mult unit t

let canon_monoid (#a:Type) (m:cm a) : Tac unit =
  norm [];
  match term_as_formula (cur_goal ()) with
  | Comp (Eq (Some t)) t1 t2 ->
      // dump ("t1 =" ^ term_to_string t1 ^
      //     "; t2 =" ^ term_to_string t2);
      if term_eq t (quote a) then
        let (r1, ts, am) = reification m [] (const (CM?.unit m)) t1 in
        let (r2, _, am) = reification m ts am t2 in
         dump ("am =" ^ term_to_string (quote am));
        change_sq (quote (mdenote m am r1 == mdenote m am r2));
        // dump ("before =" ^ term_to_string (norm_term [delta;primops]
        //   (quote (mdenote m am r1 == mdenote m am r2))));
        // dump ("expected after =" ^ term_to_string (norm_term [delta;primops]
        //   (quote (xsdenote m am (canon r1) ==
        //           xsdenote m am (canon r2)))));
        apply (`monoid_reflect);
        // dump ("after apply");
        norm [delta_only [`%canon; `%xsdenote; `%flatten; `%sort;
                `%select; `%assoc; `%fst; `%__proj__Mktuple2__item___1;
                `%(@); `%append; `%List.Tot.sortWith;
                `%List.Tot.partition; `%bool_of_compare; `%compare_of_bool;
           ]; primops]
        // ;dump "done"
      else fail "Goal should be an equality at the right monoid type"
  | _ -> fail "Goal should be an equality"
