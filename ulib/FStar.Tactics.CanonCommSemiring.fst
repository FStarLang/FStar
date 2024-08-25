(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.Tactics.CanonCommSemiring

/// A tactic to solve equalities on a commutative semiring (a, +, *, 0, 1)
///
/// The tactic [canon_semiring] is parameterized by the base type [a] and
/// a semiring theory [cr a]. This requires:
///
/// - A commutative monoid (a, +, 0) for addition
///   That is, + is associative, commutative and has identity element 0
/// - An additive inverse operator for (a, +, 0), making it an Abelian group
///   That is, a + -a = 0
/// - A commutative monoid (a, *, 1) for multiplication
///   That is, * is associative, commutative and has identity element 1
/// - Multiplication left-distributes over addition
///   That is, a * (b + c) == a * b + a * c
/// - 0 is an absorbing element of multiplication
///   That is, 0 * a = 0
///
/// In contrast to the previous version of FStar.Tactics.CanonCommSemiring,
/// the tactic defined here canonizes products, additions and additive inverses,
/// collects coefficients in monomials, and eliminates trivial expressions.
///
/// This is based on the legacy (second) version of Coq's ring tactic:
///  -  https://github.com/coq-contribs/legacy-ring/
///
/// See also the newest ring tactic in Coq, which is even more general
/// and efficient:
///  - https://coq.inria.fr/refman/addendum/ring.html
///  - http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf

open FStar.List
open FStar.Algebra.CommMonoid

(* Trying to not just open FStar.Tactics.V2 to reduce deps.
TODO: Add an interface to this module. It's non trivial due to the quoting. *)
open FStar.Stubs.Reflection.Types
open FStar.Reflection.V2
open FStar.Reflection.V2.Formula
open FStar.Stubs.Tactics.Types
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Tactics.V2.Derived
open FStar.Tactics.Util
open FStar.Tactics.NamedView
open FStar.Tactics.MApply

private
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

(** An attribute for marking definitions to unfold by the tactic *)
irreducible let canon_attr = ()

///
/// Commutative semiring theory
///

let distribute_left_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  let ( + ) = cm_add.mult in
  let ( * ) = cm_mult.mult in
  x:a -> y:a -> z:a -> Lemma (x * (y + z) == x * y + x * z)

let distribute_right_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  let ( + ) = cm_add.mult in
  let ( * ) = cm_mult.mult in
  x:a -> y:a -> z:a -> Lemma ((x + y) * z == x * z + y * z)

let mult_zero_l_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  x:a -> Lemma (cm_mult.mult cm_add.unit x == cm_add.unit)

let add_opp_r_lemma (a:Type) (cm_add:cm a) (opp:(a -> a)) =
  let ( + ) = cm_add.mult in
  x:a -> Lemma (x + opp x == cm_add.unit)

[@@canon_attr]
unopteq
type cr (a:Type) =
  | CR :
    cm_add: cm a ->
    cm_mult: cm a ->
    opp: (a -> a) ->
    add_opp: add_opp_r_lemma a cm_add opp ->
    distribute: distribute_left_lemma a cm_add cm_mult ->
    mult_zero_l: mult_zero_l_lemma a cm_add cm_mult ->
    cr a

let distribute_right (#a:Type) (r:cr a) : distribute_right_lemma a r.cm_add r.cm_mult =
  fun x y z ->
    r.cm_mult.commutativity (r.cm_add.mult x y) z;
    r.distribute z x y;
    r.cm_mult.commutativity x z;
    r.cm_mult.commutativity y z

///
/// Syntax of canonical ring expressions
///

(**
 * Marking expressions we would like to normalize fully.
 * This does not do anything at the moment, but it would be nice
 * to have a cheap mechanism to make this work without traversing the
 * whole goal.
**)
[@@canon_attr]
unfold let norm_fully (#a:Type) (x:a) = x

let index: eqtype = nat

(*
 * A list of variables represents a sorted product of one or more variables.
 * We do not need to prove sortedness to prove correctness, so we never
 * make it explicit.
 *)
type varlist =
  | Nil_var : varlist
  | Cons_var : index -> varlist -> varlist

(*
 * A canonical expression represents an ordered sum of monomials.
 * Each monomial is either:
 * - a varlist (a product of variables): x1 * ... * xk
 * - a product of a scalar and a varlist: c * x1 * ... * xk
 *
 * The order on monomials is the lexicographic order on varlist, with the
 * additional convention that monomials with a scalar are less than monomials
 * without a scalar.
 *)
type canonical_sum a =
  | Nil_monom : canonical_sum a
  | Cons_monom : a -> varlist -> canonical_sum a -> canonical_sum a
  | Cons_varlist : varlist -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec varlist_lt (x y:varlist) : bool =
  match x, y with
  | Nil_var, Cons_var _ _ -> true
  | Cons_var i xs, Cons_var j ys ->
    if i < j then true else i = j && varlist_lt xs ys
  | _, _ -> false

[@@canon_attr]
val varlist_merge: l1:varlist -> l2:varlist -> Tot varlist (decreases %[l1; l2; 0])

[@@canon_attr]
val vm_aux: index -> t1:varlist -> l2:varlist -> Tot varlist (decreases %[t1; l2; 1])

(* Merges two lists of variables, preserving sortedness *)
[@@canon_attr]
let rec varlist_merge l1 l2 =
  match l1, l2 with
  | _, Nil_var -> l1
  | Nil_var, _ -> l2
  | Cons_var v1 t1, Cons_var v2 t2 -> vm_aux v1 t1 l2
and vm_aux v1 t1 l2 =
  match l2 with
  | Cons_var v2 t2 ->
    if v1 < v2
    then Cons_var v1 (varlist_merge t1 l2)
    else Cons_var v2 (vm_aux v1 t1 t2)
  | _ -> Cons_var v1 t1

(*
 * Merges two canonical expressions
 *
 * We require that [a] is eqtype for better reasons later.
 * Here it is convenient to fix the universe of [a] in
 * mutually recursive functions.
 *)
[@@canon_attr]
val canonical_sum_merge : #a:eqtype -> cr a
  -> s1:canonical_sum a -> s2:canonical_sum a
  -> Tot (canonical_sum a) (decreases %[s1; s2; 0])

[@@canon_attr]
val csm_aux: #a:eqtype -> r:cr a -> c1:a -> l1:varlist -> t1:canonical_sum a
  -> s2:canonical_sum a -> Tot (canonical_sum a) (decreases %[t1; s2; 1])

[@@canon_attr]
let rec canonical_sum_merge #a r s1 s2 =
  let aplus = r.cm_add.mult in
  let aone  = r.cm_mult.unit in
  match s1 with
  | Cons_monom c1 l1 t1 -> csm_aux r c1 l1 t1 s2
  | Cons_varlist l1 t1  -> csm_aux r aone l1 t1 s2
  | Nil_monom -> s2

and csm_aux #a r c1 l1 t1 s2 =
  let aplus = r.cm_add.mult in
  let aone  = r.cm_mult.unit in
  match s2 with
  | Cons_monom c2 l2 t2 ->
    if l1 = l2
    then Cons_monom (norm_fully (aplus c1 c2)) l1 (canonical_sum_merge r t1 t2)
    else
      if varlist_lt l1 l2
      then Cons_monom c1 l1 (canonical_sum_merge r t1 s2)
      else Cons_monom c2 l2 (csm_aux #a r c1 l1 t1 t2)
  | Cons_varlist l2 t2 ->
    if l1 = l2
    then Cons_monom (norm_fully (aplus c1 aone)) l1 (canonical_sum_merge r t1 t2)
    else
      if varlist_lt l1 l2
      then Cons_monom c1 l1 (canonical_sum_merge r t1 s2)
      else Cons_varlist l2 (csm_aux r c1 l1 t1 t2)
  | Nil_monom ->
    //if c1 = aone then Cons_varlist l1 t1 else
    Cons_monom c1 l1 t1

(* Inserts a monomial into the appropriate position in a canonical sum *)
val monom_insert: #a:eqtype -> r:cr a
  -> c1:a -> l1:varlist -> s2:canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec monom_insert #a r c1 l1 s2 =
  let aplus = r.cm_add.mult in
  let aone  = r.cm_mult.unit in
  match s2 with
  | Cons_monom c2 l2 t2 ->
    if l1 = l2
    then Cons_monom (norm_fully (aplus c1 c2)) l1 t2
    else
      if varlist_lt l1 l2
      then Cons_monom c1 l1 s2
      else Cons_monom c2 l2 (monom_insert r c1 l1 t2)
  | Cons_varlist l2 t2 ->
    if l1 = l2
    then Cons_monom (norm_fully (aplus c1 aone)) l1 t2
    else
      if varlist_lt l1 l2
      then Cons_monom c1 l1 s2
      else Cons_varlist l2 (monom_insert r c1 l1 t2)
  | Nil_monom ->
    if c1 = aone
    then Cons_varlist l1 Nil_monom
    else Cons_monom c1 l1 Nil_monom

(* Inserts a monomial without scalar into a canonical sum *)
val varlist_insert: #a:eqtype -> cr a -> varlist -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let varlist_insert #a r l1 s2 =
  let aone = r.cm_mult.unit in
  monom_insert r aone l1 s2

(* Multiplies a sum by a scalar c0 *)
val canonical_sum_scalar: #a:Type -> cr a -> a -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_scalar #a r c0 s =
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t -> Cons_monom (norm_fully (amult c0 c)) l (canonical_sum_scalar r c0 t)
  | Cons_varlist l t -> Cons_monom c0 l (canonical_sum_scalar r c0 t)
  | Nil_monom -> Nil_monom

(* Multiplies a sum by a monomial without scalar *)
val canonical_sum_scalar2: #a:eqtype -> cr a -> varlist
  -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_scalar2 #a r l0 s =
  match s with
  | Cons_monom c l t ->
    monom_insert r c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t)
  | Cons_varlist l t ->
    varlist_insert r (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t)
  | Nil_monom -> Nil_monom


(* Multiplies a sum by a monomial with scalar *)
val canonical_sum_scalar3: #a:eqtype -> cr a -> a -> varlist
  -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_scalar3 #a r c0 l0 s =
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t ->
    monom_insert r (norm_fully (amult c0 c)) (varlist_merge l0 l)
                 (canonical_sum_scalar3 r c0 l0 t)
  | Cons_varlist l t ->
    monom_insert r c0 (varlist_merge l0 l)
                 (canonical_sum_scalar3 r c0 l0 t)
  | Nil_monom -> s

(* Multiplies two canonical sums *)
val canonical_sum_prod: #a:eqtype -> cr a
  -> canonical_sum a -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_prod #a r s1 s2 =
  match s1 with
  | Cons_monom c1 l1 t1 ->
    canonical_sum_merge r (canonical_sum_scalar3 r c1 l1 s2)
                          (canonical_sum_prod r t1 s2)
  | Cons_varlist l1 t1 ->
    canonical_sum_merge r (canonical_sum_scalar2 r l1 s2)
                          (canonical_sum_prod r t1 s2)
  | Nil_monom -> s1

///
/// Syntax of concrete semiring polynomials
///

(* This is the type where we reflect expressions before normalization *)
type spolynomial a =
  | SPvar   : index -> spolynomial a
  | SPconst : a -> spolynomial a
  | SPplus  : spolynomial a -> spolynomial a -> spolynomial a
  | SPmult  : spolynomial a -> spolynomial a -> spolynomial a

(** Canonize a reflected expression *)
val spolynomial_normalize: #a:eqtype -> cr a -> spolynomial a -> canonical_sum a

[@@canon_attr]
let rec spolynomial_normalize #a r p =
  match p with
  | SPvar i -> Cons_varlist (Cons_var i Nil_var) Nil_monom
  | SPconst c -> Cons_monom c Nil_var Nil_monom
  | SPplus l q ->
    canonical_sum_merge r (spolynomial_normalize r l) (spolynomial_normalize r q)
  | SPmult l q ->
    canonical_sum_prod r (spolynomial_normalize r l) (spolynomial_normalize r q)

(**
 * Simplify a canonical sum.
 * Removes 0 * x1 * ... * xk and turns 1 * x1 * ... * xk into x1 * ... * xk
**)
val canonical_sum_simplify: #a:eqtype -> cr a -> canonical_sum a -> canonical_sum a

[@@canon_attr]
let rec canonical_sum_simplify #a r s =
  let azero = r.cm_add.unit in
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  match s with
  | Cons_monom c l t ->
    if norm_fully (c = azero) then canonical_sum_simplify r t
    else
      if norm_fully (c = aone)
      then Cons_varlist l (canonical_sum_simplify r t)
      else Cons_monom c l (canonical_sum_simplify r t)
  | Cons_varlist l t -> Cons_varlist l (canonical_sum_simplify r t)
  | Nil_monom -> s

(**
 * The main canonization algorithm: turn an expression into a sum and
 * simplify it.
**)
val spolynomial_simplify: #a:eqtype -> cr a -> spolynomial a -> canonical_sum a

[@@canon_attr]
let spolynomial_simplify #a r p =
  canonical_sum_simplify r
    (spolynomial_normalize r p)

///
/// Interpretation of varlists, monomials and canonical sums
///

type var = nat

(**
 * The variable map:
 * This maps polynomial variables to ring expressions. That is, any term
 * that is not an addition or a multiplication is turned into a variable
 *
 * The representation is inefficient. For large terms it might be worthwhile
 * using a better data structure.
**)
let vmap a = list (var & a) & a

(** Add a new entry in a variable map *)
let update (#a:Type) (x:var) (xa:a) (vm:vmap a) : vmap a =
  let l, y = vm in (x, xa) :: l, y

(** Quotes a list *)
let rec quote_list (#a:Type) (ta:term) (quotea:a -> Tac term) (xs:list a) :
    Tac term =
  match xs with
  | [] -> mk_app (`Nil) [(ta, Q_Implicit)]
  | x::xs' -> mk_app (`Cons) [(ta, Q_Implicit);
                             (quotea x, Q_Explicit);
                             (quote_list ta quotea xs', Q_Explicit)]

(** Quotes a variable map *)
let quote_vm (#a:Type) (ta: term) (quotea:a -> Tac term) (vm:vmap a) : Tac term =
  let quote_map_entry (p:(nat & a)) : Tac term =
    mk_app (`Mktuple2) [(`nat, Q_Implicit); (ta, Q_Implicit);
      (pack (Tv_Const (C_Int (fst p))), Q_Explicit);
      (quotea (snd p), Q_Explicit)] in
  let tyentry = mk_e_app (`tuple2) [(`nat); ta] in
  let tlist = quote_list tyentry quote_map_entry (fst vm) in
  let tylist = mk_e_app (`list) [tyentry] in
  mk_app (`Mktuple2) [(tylist, Q_Implicit); (ta, Q_Implicit);
                      (tlist, Q_Explicit); (quotea (snd vm), Q_Explicit)]

(**
 * A varlist is interpreted as the product of the entries in the variable map
 *
 * Unbound variables are mapped to the default value according to the map.
 * This would normally never occur, but it makes it easy to prove correctness.
 *)
[@@canon_attr]
let interp_var (#a:Type) (vm:vmap a) (i:index) =
  match List.Tot.Base.assoc i (fst vm) with
  | Some x -> x
  | _ -> snd vm

[@@canon_attr]
private
let rec ivl_aux (#a:Type) (r:cr a) (vm:vmap a) (x:index) (t:varlist)
  : Tot a (decreases t) =
  let amult = r.cm_mult.mult in
  match t with
  | Nil_var -> interp_var vm x
  | Cons_var x' t' -> amult (interp_var vm x) (ivl_aux r vm x' t')

[@@canon_attr]
let interp_vl (#a:Type) (r:cr a) (vm:vmap a) (l:varlist) =
  let aone  = r.cm_mult.unit in
  match l with
  | Nil_var -> aone
  | Cons_var x t -> ivl_aux r vm x t

[@@canon_attr]
let interp_m (#a:Type) (r:cr a) (vm:vmap a) (c:a) (l:varlist) =
  let amult = r.cm_mult.mult in
  match l with
  | Nil_var -> c
  | Cons_var x t -> amult c (ivl_aux r vm x t)

[@@canon_attr]
let rec ics_aux (#a:Type) (r:cr a) (vm:vmap a) (x:a) (s:canonical_sum a)
  : Tot a (decreases s) =
  let aplus = r.cm_add.mult in
  match s with
  | Nil_monom -> x
  | Cons_varlist l t -> aplus x (ics_aux r vm (interp_vl r vm l) t)
  | Cons_monom c l t -> aplus x (ics_aux r vm (interp_m r vm c l) t)

(** Interpretation of a canonical sum *)
[@@canon_attr]
let interp_cs (#a:Type) (r:cr a) (vm:vmap a) (s:canonical_sum a) : a =
  let azero = r.cm_add.unit in
  match s with
  | Nil_monom -> azero
  | Cons_varlist l t -> ics_aux r vm (interp_vl r vm l) t
  | Cons_monom c l t -> ics_aux r vm (interp_m r vm c l) t

(** Interpretation of a polynomial *)
[@@canon_attr]
let rec interp_sp (#a:Type) (r:cr a) (vm:vmap a) (p:spolynomial a) : a =
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match p with
  | SPconst c -> c
  | SPvar i -> interp_var vm i
  | SPplus p1 p2 -> aplus (interp_sp r vm p1) (interp_sp r vm p2)
  | SPmult p1 p2 -> amult (interp_sp r vm p1) (interp_sp r vm p2)

///
/// Proof of correctness
///

val mult_one_l (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_mult.mult r.cm_mult.unit x == x)
  [SMTPat (r.cm_mult.mult r.cm_mult.unit x)]
let mult_one_l #a r x =
  r.cm_mult.identity x

val mult_one_r (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_mult.mult x r.cm_mult.unit == x)
  [SMTPat (r.cm_mult.mult x r.cm_mult.unit)]
let mult_one_r #a r x =
  r.cm_mult.commutativity r.cm_mult.unit x

val mult_zero_l (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_mult.mult r.cm_add.unit x == r.cm_add.unit)
  [SMTPat (r.cm_mult.mult r.cm_add.unit x)]
let mult_zero_l #a r x =
  r.mult_zero_l x

val mult_zero_r (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_mult.mult x r.cm_add.unit == r.cm_add.unit)
  [SMTPat (r.cm_mult.mult x r.cm_add.unit)]
let mult_zero_r #a r x =
  r.cm_mult.commutativity x r.cm_add.unit

val add_zero_l (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_add.mult r.cm_add.unit x == x)
  [SMTPat (r.cm_add.mult r.cm_add.unit x)]
let add_zero_l #a r x =
  r.cm_add.identity  x

val add_zero_r (#a:Type) (r:cr a) (x:a) :
  Lemma (r.cm_add.mult x r.cm_add.unit == x)
  [SMTPat (r.cm_add.mult x r.cm_add.unit)]
let add_zero_r #a r x =
  r.cm_add.commutativity r.cm_add.unit x

val opp_unique (#a:Type) (r:cr a) (x y:a) : Lemma
  (requires r.cm_add.mult x y == r.cm_add.unit)
  (ensures  y == r.opp x)
let opp_unique #a r x y =
  let ( + ) = r.cm_add.mult in
  let zero = r.cm_add.unit in
  calc (==) {
    y;
    == { r.add_opp x }
    y + (x + r.opp x);
    == { r.cm_add.associativity y x (r.opp x) }
    (y + x) + r.opp x;
    == { r.cm_add.commutativity x y }
    zero + r.opp x;
    == { }
    r.opp x;
  }

val add_mult_opp (#a:Type) (r:cr a) (x:a) : Lemma
  (r.cm_add.mult x (r.cm_mult.mult (r.opp r.cm_mult.unit) x) == r.cm_add.unit)
let add_mult_opp #a r x =
  let ( + ) = r.cm_add.mult in
  let ( * ) = r.cm_mult.mult in
  let zero = r.cm_add.unit in
  let one = r.cm_mult.unit in
  calc (==) {
    x + r.opp one * x;
    == { }
    one * x + r.opp one * x;
    == { distribute_right r one (r.opp one) x }
    (one + r.opp one) * x;
    == { r.add_opp one }
    zero * x;
    == { }
    zero;
  }

val ivl_aux_ok (#a:Type) (r:cr a) (vm:vmap a) (v:varlist) (i:index) : Lemma
  (ivl_aux r vm i v == r.cm_mult.mult (interp_var vm i) (interp_vl r vm v))
let ivl_aux_ok #a r vm v i = ()

val vm_aux_ok (#a:eqtype) (r:cr a) (vm:vmap a) (v:index) (t l:varlist) :
  Lemma
  (ensures
    interp_vl r vm (vm_aux v t l) ==
    r.cm_mult.mult (interp_vl r vm (Cons_var v t)) (interp_vl r vm l))
  (decreases %[t; l; 1])

val varlist_merge_ok (#a:eqtype) (r:cr a) (vm:vmap a) (x y:varlist) :
  Lemma
  (ensures
    interp_vl r vm (varlist_merge x y) ==
    r.cm_mult.mult (interp_vl r vm x) (interp_vl r vm y))
  (decreases %[x; y; 0])

let rec varlist_merge_ok #a r vm x y =
  let amult = r.cm_mult.mult in
  match x, y with
  | Cons_var v1 t1, Nil_var -> ()
  | Cons_var v1 t1, Cons_var v2 t2 ->
    if v1 < v2
    then
      begin
      varlist_merge_ok r vm t1 y;
      assert (
        interp_vl r vm (varlist_merge x y) ==
        amult (interp_var vm v1) (amult (interp_vl r vm t1) (interp_vl r vm y)));
      r.cm_mult.associativity
        (interp_var vm v1) (interp_vl r vm t1) (interp_vl r vm y)
      end
    else
      vm_aux_ok r vm v1 t1 y
  | Nil_var, _ -> ()
and vm_aux_ok #a r vm v1 t1 l2 =
  match l2 with
  | Cons_var v2 t2 ->
    if v1 < v2
    then
      begin
      varlist_merge_ok r vm t1 l2;
      r.cm_mult.associativity
        (interp_var vm v1) (interp_vl r vm t1) (interp_vl r vm l2)
      end
    else
      begin
      vm_aux_ok r vm v1 t1 t2;
      calc (==) {
        interp_vl r vm (Cons_var v2 (vm_aux v1 t1 t2));
        == { }
        ivl_aux r vm v2 (vm_aux v1 t1 t2);
        == { }
        r.cm_mult.mult (interp_var vm v2) (interp_vl r vm (vm_aux v1 t1 t2));
        == { }
        r.cm_mult.mult (interp_var vm v2) (r.cm_mult.mult (interp_vl r vm (Cons_var v1 t1)) (interp_vl r vm t2));
        == { r.cm_mult.commutativity
               (interp_vl r vm (Cons_var v1 t1)) (interp_vl r vm t2) }
        r.cm_mult.mult (interp_var vm v2)
          (r.cm_mult.mult (interp_vl r vm t2) (interp_vl r vm (Cons_var v1 t1)) );
        == { r.cm_mult.associativity
              (interp_var vm v2)
              (interp_vl r vm t2) (interp_vl r vm (Cons_var v1 t1)) }
        r.cm_mult.mult
         (r.cm_mult.mult (interp_var vm v2) (interp_vl r vm t2))
         (interp_vl r vm (Cons_var v1 t1));
        == { r.cm_mult.commutativity
            (interp_vl r vm (Cons_var v1 t1)) (interp_vl r vm (Cons_var v2 t2)) }
        r.cm_mult.mult (interp_vl r vm (Cons_var v1 t1)) (interp_vl r vm (Cons_var v2 t2));
      }
      end
  | _ -> ()

val ics_aux_ok: #a:eqtype -> r:cr a -> vm:vmap a -> x:a -> s:canonical_sum a ->
  Lemma (ensures ics_aux r vm x s == r.cm_add.mult x (interp_cs r vm s))
  (decreases s)
let rec ics_aux_ok #a r vm x s =
  match s with
  | Nil_monom -> ()
  | Cons_varlist l t ->
    ics_aux_ok r vm (interp_vl r vm l) t
  | Cons_monom c l t ->
    ics_aux_ok r vm (interp_m r vm c l) t

val interp_m_ok: #a:eqtype -> r:cr a -> vm:vmap a -> x:a -> l:varlist ->
  Lemma (interp_m r vm x l == r.cm_mult.mult x (interp_vl r vm l))
let interp_m_ok #a r vm x l = ()

val aplus_assoc_4: #a:Type -> r:cr a -> w:a -> x:a -> y:a -> z:a -> Lemma
  (let aplus = r.cm_add.mult in
   aplus (aplus w x) (aplus y z) == aplus (aplus w y) (aplus x z))
let aplus_assoc_4 #a r w x y z =
  let aplus = r.cm_add.mult in
  let assoc = r.cm_add.associativity in
  let comm = r.cm_add.commutativity in
  calc (==) {
    aplus (aplus w x) (aplus y z);
    == { assoc w x (aplus y z) }
    aplus w (aplus x (aplus y z));
    == { comm x (aplus y z) }
    aplus w (aplus (aplus y z) x);
    == { assoc w (aplus y z) x }
    aplus (aplus w (aplus y z)) x;
    == { assoc w y z }
    aplus (aplus (aplus w y) z) x;
    == { assoc (aplus w y) z x }
    aplus (aplus w y) (aplus z x);
    == { comm z x }
    aplus (aplus w y) (aplus x z);
  }

val canonical_sum_merge_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> s1:canonical_sum a -> s2:canonical_sum a ->
  Lemma
  (ensures
    interp_cs r vm (canonical_sum_merge r s1 s2) ==
    r.cm_add.mult (interp_cs r vm s1) (interp_cs r vm s2))
  (decreases %[s1; s2; 0])

val csm_aux_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> c1:a -> l1:varlist -> t1:canonical_sum a -> s2:canonical_sum a ->
  Lemma
  (ensures
    interp_cs r vm (csm_aux r c1 l1 t1 s2) ==
    r.cm_add.mult (interp_cs r vm (Cons_monom c1 l1 t1)) (interp_cs r vm s2))
  (decreases %[t1; s2; 1])

let rec canonical_sum_merge_ok #a r vm s1 s2 =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s1 with
  | Cons_monom c1 l1 t1 -> csm_aux_ok #a r vm c1 l1 t1 s2
  | Cons_varlist l1 t1  ->
    calc (==) {
      interp_cs r vm (canonical_sum_merge r s1 s2);
      == { }
      interp_cs r vm (csm_aux r aone l1 t1 s2);
      == { csm_aux_ok #a r vm aone l1 t1 s2 }
      aplus (interp_cs r vm (Cons_monom aone l1 t1))
            (interp_cs r vm s2);
      == { ics_aux_ok r vm (interp_vl r vm l1) t1 }
      aplus (interp_cs r vm (Cons_varlist l1 t1))
            (interp_cs r vm s2);
    }
  | Nil_monom -> ()
and csm_aux_ok #a r vm c1 l1 t1 s2 =
  let aplus = r.cm_add.mult in
  let aone  = r.cm_mult.unit in
  let amult = r.cm_mult.mult in
  match s2 with
  | Nil_monom -> ()
  | Cons_monom c2 l2 t2 ->
    let s1 = Cons_monom c1 l1 t1 in
    if l1 = l2 then
    begin
    calc (==) {
      interp_cs r vm (csm_aux r c1 l1 t1 s2);
      == { }
      ics_aux r vm (interp_m r vm (aplus c1 c2) l1)
                   (canonical_sum_merge r t1 t2);
      == { ics_aux_ok r vm (interp_m r vm (aplus c1 c2) l1)
                           (canonical_sum_merge r t1 t2) }
      aplus (interp_m r vm (aplus c1 c2) l1)
            (interp_cs r vm (canonical_sum_merge r t1 t2));
      == { interp_m_ok r vm (aplus c1 c2) l1 }
      aplus (amult (aplus c1 c2) (interp_vl r vm l1))
            (interp_cs r vm (canonical_sum_merge r t1 t2));
      == { canonical_sum_merge_ok r vm t1 t2 }
      aplus (amult (aplus c1 c2) (interp_vl r vm l1))
            (aplus (interp_cs r vm t1) (interp_cs r vm t2));
      == { distribute_right r c1 c2 (interp_vl r vm l1) }
      aplus (aplus (amult c1 (interp_vl r vm l1))
                   (amult c2 (interp_vl r vm l2)))
            (aplus (interp_cs r vm t1)
                   (interp_cs r vm t2));
      == { aplus_assoc_4 r
             (amult c1 (interp_vl r vm l1))
             (amult c2 (interp_vl r vm l2))
             (interp_cs r vm t1)
             (interp_cs r vm t2) }
      aplus (aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm t1))
            (aplus (amult c2 (interp_vl r vm l2)) (interp_cs r vm t2));
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s1)
            (aplus (amult c2 (interp_vl r vm l2)) (interp_cs r vm t2));
      == { ics_aux_ok r vm (amult c2 (interp_vl r vm l2)) t2;
           interp_m_ok r vm c2 l2 }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
    else if varlist_lt l1 l2 then
    begin
    calc (==) {
      interp_cs r vm (canonical_sum_merge r s1 s2);
      == { }
      ics_aux r vm (interp_m r vm c1 l1)
                   (canonical_sum_merge r t1 s2);
      == { ics_aux_ok r vm (interp_m r vm c1 l1)
                           (canonical_sum_merge r t1 s2) }
      aplus (interp_m r vm c1 l1)
            (interp_cs r vm (canonical_sum_merge r t1 s2));
      == { interp_m_ok r vm c1 l1 }
      aplus (amult c1 (interp_vl r vm l1))
            (interp_cs r vm (canonical_sum_merge r t1 s2));
      == { canonical_sum_merge_ok r vm t1 s2 }
      aplus (amult c1 (interp_vl r vm l1))
            (aplus (interp_cs r vm t1) (interp_cs r vm s2));
      == { r.cm_add.associativity
             (amult c1 (interp_vl r vm l1))
             (interp_cs r vm t1)
             (interp_cs r vm s2)
         }
      aplus (aplus (amult c1 (interp_vl r vm l1))
                   (interp_cs r vm t1))
            (interp_cs r vm s2);
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
    else
    begin
    calc (==) {
      interp_cs r vm (csm_aux r c1 l1 t1 s2);
      == { }
      ics_aux r vm (interp_m r vm c2 l2)
                   (csm_aux r c1 l1 t1 t2);
      == { ics_aux_ok r vm (interp_m r vm c2 l2)
                           (csm_aux r c1 l1 t1 t2) }
      aplus (interp_m r vm c2 l2)
            (interp_cs r vm (csm_aux r c1 l1 t1 t2));
      == { interp_m_ok r vm c2 l2 }
      aplus (amult c2 (interp_vl r vm l2))
            (interp_cs r vm (csm_aux r c1 l1 t1 t2));
      == { csm_aux_ok r vm c1 l1 t1 t2 }
      aplus (amult c2 (interp_vl r vm l2))
            (aplus (interp_cs r vm s1) (interp_cs r vm t2));
      == { r.cm_add.commutativity (interp_cs r vm s1) (interp_cs r vm t2) }
      aplus (amult c2 (interp_vl r vm l2))
            (aplus (interp_cs r vm t2) (interp_cs r vm s1));
      == { r.cm_add.associativity
             (amult c2 (interp_vl r vm l2))
             (interp_cs r vm t2)
             (interp_cs r vm s1)
         }
      aplus (aplus (amult c2 (interp_vl r vm l2))
                   (interp_cs r vm t2))
            (interp_cs r vm s1);
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s2) (interp_cs r vm s1);
      == { r.cm_add.commutativity (interp_cs r vm s1) (interp_cs r vm s2) }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
  | Cons_varlist l2 t2 -> // Same as Cons_monom with c2 = aone
    let c2 = aone in
    let s1 = Cons_monom c1 l1 t1 in
    if l1 = l2 then
    begin
    calc (==) {
      interp_cs r vm (csm_aux r c1 l1 t1 s2);
      == { }
      ics_aux r vm (interp_m r vm (aplus c1 c2) l1)
                   (canonical_sum_merge r t1 t2);
      == { ics_aux_ok r vm (interp_m r vm (aplus c1 c2) l1)
                           (canonical_sum_merge r t1 t2) }
      aplus (interp_m r vm (aplus c1 c2) l1)
            (interp_cs r vm (canonical_sum_merge r t1 t2));
      == { interp_m_ok r vm (aplus c1 c2) l1 }
      aplus (amult (aplus c1 c2) (interp_vl r vm l1))
            (interp_cs r vm (canonical_sum_merge r t1 t2));
      == { canonical_sum_merge_ok r vm t1 t2 }
      aplus (amult (aplus c1 c2) (interp_vl r vm l1))
            (aplus (interp_cs r vm t1) (interp_cs r vm t2));
      == { distribute_right r c1 c2 (interp_vl r vm l1) }
      aplus (aplus (amult c1 (interp_vl r vm l1))
                   (amult c2 (interp_vl r vm l2)))
            (aplus (interp_cs r vm t1)
                   (interp_cs r vm t2));
      == { aplus_assoc_4 r
             (amult c1 (interp_vl r vm l1))
             (amult c2 (interp_vl r vm l2))
             (interp_cs r vm t1)
             (interp_cs r vm t2) }
      aplus (aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm t1))
            (aplus (amult c2 (interp_vl r vm l2)) (interp_cs r vm t2));
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s1)
            (aplus (amult c2 (interp_vl r vm l2)) (interp_cs r vm t2));
      == { ics_aux_ok r vm (amult c2 (interp_vl r vm l2)) t2;
           interp_m_ok r vm c2 l2 }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
    else if varlist_lt l1 l2 then
    begin
    calc (==) {
      interp_cs r vm (canonical_sum_merge r s1 s2);
      == { }
      ics_aux r vm (interp_m r vm c1 l1)
                   (canonical_sum_merge r t1 s2);
      == { ics_aux_ok r vm (interp_m r vm c1 l1)
                           (canonical_sum_merge r t1 s2) }
      aplus (interp_m r vm c1 l1)
            (interp_cs r vm (canonical_sum_merge r t1 s2));
      == { interp_m_ok r vm c1 l1 }
      aplus (amult c1 (interp_vl r vm l1))
            (interp_cs r vm (canonical_sum_merge r t1 s2));
      == { canonical_sum_merge_ok r vm t1 s2 }
      aplus (amult c1 (interp_vl r vm l1))
            (aplus (interp_cs r vm t1) (interp_cs r vm s2));
      == { r.cm_add.associativity
             (amult c1 (interp_vl r vm l1))
             (interp_cs r vm t1)
             (interp_cs r vm s2)
         }
      aplus (aplus (amult c1 (interp_vl r vm l1))
                   (interp_cs r vm t1))
            (interp_cs r vm s2);
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end
    else
    begin
    calc (==) {
      interp_cs r vm (csm_aux r c1 l1 t1 s2);
      == { }
      ics_aux r vm (interp_m r vm c2 l2)
                   (csm_aux r c1 l1 t1 t2);
      == { ics_aux_ok r vm (interp_m r vm c2 l2)
                           (csm_aux r c1 l1 t1 t2) }
      aplus (interp_m r vm c2 l2)
            (interp_cs r vm (csm_aux r c1 l1 t1 t2));
      == { interp_m_ok r vm c2 l2 }
      aplus (amult c2 (interp_vl r vm l2))
            (interp_cs r vm (csm_aux r c1 l1 t1 t2));
      == { csm_aux_ok r vm c1 l1 t1 t2 }
      aplus (amult c2 (interp_vl r vm l2))
            (aplus (interp_cs r vm s1) (interp_cs r vm t2));
      == { r.cm_add.commutativity (interp_cs r vm s1) (interp_cs r vm t2) }
      aplus (amult c2 (interp_vl r vm l2))
            (aplus (interp_cs r vm t2) (interp_cs r vm s1));
      == { r.cm_add.associativity
             (amult c2 (interp_vl r vm l2))
             (interp_cs r vm t2)
             (interp_cs r vm s1)
         }
      aplus (aplus (amult c2 (interp_vl r vm l2))
                   (interp_cs r vm t2))
            (interp_cs r vm s1);
      == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
           interp_m_ok r vm c1 l1 }
      aplus (interp_cs r vm s2) (interp_cs r vm s1);
      == { r.cm_add.commutativity (interp_cs r vm s1) (interp_cs r vm s2) }
      aplus (interp_cs r vm s1) (interp_cs r vm s2);
    }
    end

val monom_insert_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> c1:a -> l1:varlist -> s2:canonical_sum a ->
  Lemma
  (interp_cs r vm (monom_insert r c1 l1 s2) ==
   r.cm_add.mult (r.cm_mult.mult c1 (interp_vl r vm l1)) (interp_cs r vm s2))
let rec monom_insert_ok #a r vm c1 l1 s2 =
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  let aone  = r.cm_mult.unit in
  match s2 with
  | Cons_monom c2 l2 t2 ->
    if l1 = l2
    then
      calc (==) {
        interp_cs r vm (monom_insert r c1 l1 s2);
        == { }
        interp_cs r vm (Cons_monom (aplus c1 c2) l1 t2);
        == { }
        ics_aux r vm (interp_m r vm (aplus c1 c2) l1) t2;
        == { ics_aux_ok r vm (interp_m r vm (aplus c1 c2) l1) t2 }
        aplus (interp_m r vm (aplus c1 c2) l1) (interp_cs r vm t2);
        == { interp_m_ok r vm (aplus c1 c2) l1 }
        aplus (amult (aplus c1 c2) (interp_vl r vm l2)) (interp_cs r vm t2);
        == { distribute_right r c1 c2 (interp_vl r vm l2) }
        aplus (aplus (amult c1 (interp_vl r vm l1))
                     (amult c2 (interp_vl r vm l2)))
              (interp_cs r vm t2);
        == { r.cm_add.associativity
               (amult c1 (interp_vl r vm l1))
               (amult c2 (interp_vl r vm l2))
               (interp_cs r vm t2) }
        aplus (amult c1 (interp_vl r vm l1))
              (aplus (amult c2 (interp_vl r vm l2))
                     (interp_cs r vm t2));
        == { ics_aux_ok r vm (interp_m r vm c2 l2) t2 }
        aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2);
      }
    else
     if varlist_lt l1 l2 then ()
     else
       calc (==) {
        interp_cs r vm (monom_insert r c1 l1 s2);
        == { }
        interp_cs r vm (Cons_monom c2 l2 (monom_insert r c1 l1 t2));
        == { }
        aplus (amult c2 (interp_vl r vm l2))
              (interp_cs r vm (monom_insert r c1 l1 t2));
        == { monom_insert_ok r vm c1 l1 t2 }
        aplus (amult c2 (interp_vl r vm l2))
              (aplus (amult c1 (interp_vl r vm l1))
                     (interp_cs r vm t2));
        == { r.cm_add.commutativity
               (amult c1 (interp_vl r vm l1))
               (interp_cs r vm t2) }
        aplus (amult c2 (interp_vl r vm l2))
              (aplus (interp_cs r vm t2)
                     (amult c1 (interp_vl r vm l1)));
        == { r.cm_add.associativity
              (amult c2 (interp_vl r vm l2))
              (interp_cs r vm t2)
              (amult c1 (interp_vl r vm l1)) }
        aplus (aplus (amult c2 (interp_vl r vm l2))
                     (interp_cs r vm t2))
              (amult c1 (interp_vl r vm l1));
        == { ics_aux_ok r vm (interp_m r vm c2 l2) t2 }
        aplus (interp_cs r vm s2) (amult c1 (interp_vl r vm l1));
        == { r.cm_add.commutativity
              (interp_cs r vm s2)
              (amult c1 (interp_vl r vm l1)) }
        aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2);
       }
  | Cons_varlist l2 t2 -> // Same as Cons_monom with c2 = aone
    let c2 = aone in
    if l1 = l2
    then
      calc (==) {
        interp_cs r vm (monom_insert r c1 l1 s2);
        == { }
        interp_cs r vm (Cons_monom (aplus c1 c2) l1 t2);
        == { }
        ics_aux r vm (interp_m r vm (aplus c1 c2) l1) t2;
        == { ics_aux_ok r vm (interp_m r vm (aplus c1 c2) l1) t2 }
        aplus (interp_m r vm (aplus c1 c2) l1) (interp_cs r vm t2);
        == { interp_m_ok r vm (aplus c1 c2) l1 }
        aplus (amult (aplus c1 c2) (interp_vl r vm l2)) (interp_cs r vm t2);
        == { distribute_right r c1 c2 (interp_vl r vm l2) }
        aplus (aplus (amult c1 (interp_vl r vm l1))
                     (amult c2 (interp_vl r vm l2)))
              (interp_cs r vm t2);
        == { r.cm_add.associativity
               (amult c1 (interp_vl r vm l1))
               (amult c2 (interp_vl r vm l2))
               (interp_cs r vm t2) }
        aplus (amult c1 (interp_vl r vm l1))
              (aplus (amult c2 (interp_vl r vm l2))
                     (interp_cs r vm t2));
        == { ics_aux_ok r vm (interp_m r vm c2 l2) t2 }
        aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2);
      }
    else
     if varlist_lt l1 l2 then ()
     else
       calc (==) {
        interp_cs r vm (monom_insert r c1 l1 s2);
        == { }
        interp_cs r vm (Cons_monom c2 l2 (monom_insert r c1 l1 t2));
        == { }
        aplus (amult c2 (interp_vl r vm l2))
              (interp_cs r vm (monom_insert r c1 l1 t2));
        == { monom_insert_ok r vm c1 l1 t2 }
        aplus (amult c2 (interp_vl r vm l2))
              (aplus (amult c1 (interp_vl r vm l1))
                     (interp_cs r vm t2));
        == { r.cm_add.commutativity
               (amult c1 (interp_vl r vm l1))
               (interp_cs r vm t2) }
        aplus (amult c2 (interp_vl r vm l2))
              (aplus (interp_cs r vm t2)
                     (amult c1 (interp_vl r vm l1)));
        == { r.cm_add.associativity
              (amult c2 (interp_vl r vm l2))
              (interp_cs r vm t2)
              (amult c1 (interp_vl r vm l1)) }
        aplus (aplus (amult c2 (interp_vl r vm l2))
                     (interp_cs r vm t2))
              (amult c1 (interp_vl r vm l1));
        == { ics_aux_ok r vm (interp_m r vm c2 l2) t2 }
        aplus (interp_cs r vm s2) (amult c1 (interp_vl r vm l1));
        == { r.cm_add.commutativity
              (interp_cs r vm s2)
              (amult c1 (interp_vl r vm l1)) }
        aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2);
       }
  | Nil_monom -> ()

val varlist_insert_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> l1:varlist -> s2:canonical_sum a ->
  Lemma (interp_cs r vm (varlist_insert r l1 s2) ==
         r.cm_add.mult (interp_vl r vm l1) (interp_cs r vm s2))
let varlist_insert_ok #a r vm l1 s2 =
  let aone = r.cm_mult.unit in
  monom_insert_ok r vm aone l1 s2

val canonical_sum_scalar_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> c0:a -> s:canonical_sum a ->
  Lemma (
    interp_cs r vm (canonical_sum_scalar r c0 s) ==
    r.cm_mult.mult c0 (interp_cs r vm s))
let rec canonical_sum_scalar_ok #a r vm c0 s =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t ->
    calc (==) {
      interp_cs r vm (canonical_sum_scalar r c0 s);
      == { }
      interp_cs r vm (Cons_monom (amult c0 c) l (canonical_sum_scalar r c0 t));
      == { }
      aplus (amult (amult c0 c) (interp_vl r vm l))
            (interp_cs r vm (canonical_sum_scalar r c0 t));
      == { r.cm_mult.associativity c0 c (interp_vl r vm l) }
      aplus (amult c0 (amult c (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar r c0 t));
      == { canonical_sum_scalar_ok r vm c0 t }
      aplus (amult c0 (amult c (interp_vl r vm l)))
            (amult c0 (interp_cs r vm t));
      == { r.distribute c0 (amult c (interp_vl r vm l))
                              (interp_cs r vm t) }
      amult c0 (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == { }
      amult c0 (interp_cs r vm s);
    }
  | Cons_varlist l t -> // Same as Cons_monom c l t with c = r.cm_mult.unit
    let c = aone in
        calc (==) {
      interp_cs r vm (canonical_sum_scalar r c0 s);
      == { }
      interp_cs r vm (Cons_monom (amult c0 c) l (canonical_sum_scalar r c0 t));
      == { }
      aplus (amult (amult c0 c) (interp_vl r vm l))
            (interp_cs r vm (canonical_sum_scalar r c0 t));
      == { r.cm_mult.associativity c0 c (interp_vl r vm l) }
      aplus (amult c0 (amult c (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar r c0 t));
      == { canonical_sum_scalar_ok r vm c0 t }
      aplus (amult c0 (amult c (interp_vl r vm l)))
            (amult c0 (interp_cs r vm t));
      == { r.distribute c0 (amult c (interp_vl r vm l))
                              (interp_cs r vm t) }
      amult c0 (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == { }
      amult c0 (interp_cs r vm s);
    }
  | Nil_monom -> ()

val canonical_sum_scalar2_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> l0:varlist -> s:canonical_sum a ->
  Lemma (
    interp_cs r vm (canonical_sum_scalar2 r l0 s) ==
    r.cm_mult.mult (interp_vl r vm l0) (interp_cs r vm s))
let rec canonical_sum_scalar2_ok #a r vm l0 s =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t ->
    calc (==) {
      interp_cs r vm (canonical_sum_scalar2 r l0 s);
      == { }
      interp_cs r vm
        (monom_insert r c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t));
      == { monom_insert_ok r vm c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t) }
      aplus (amult c (interp_vl r vm (varlist_merge l0 l)))
            (interp_cs r vm (canonical_sum_scalar2 r l0 t));
      == { varlist_merge_ok r vm l0 l }
      aplus (amult c (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar2 r l0 t));
      == { canonical_sum_scalar2_ok r vm l0 t }
      aplus (amult c (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.associativity c (interp_vl r vm l0)
             (interp_vl r vm l) }
      aplus (amult (amult c (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.commutativity (interp_vl r vm l0) c }
      aplus (amult (amult (interp_vl r vm l0) c) (interp_vl r vm l))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.associativity (interp_vl r vm l0) c (interp_vl r vm l) }
      aplus (amult (interp_vl r vm l0) (amult c (interp_vl r vm l)))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.distribute (interp_vl r vm l0)
             (amult c (interp_vl r vm l)) (interp_cs r vm t) }
      amult (interp_vl r vm l0)
            (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == {  }
      amult (interp_vl r vm l0) (interp_cs r vm s);
    }
  | Cons_varlist l t -> // Same as Cons_monom c l t with c = aone
    let c = aone in
    calc (==) {
      interp_cs r vm (canonical_sum_scalar2 r l0 s);
      == { }
      interp_cs r vm
        (monom_insert r c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t));
      == { monom_insert_ok r vm c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t) }
      aplus (amult c (interp_vl r vm (varlist_merge l0 l)))
            (interp_cs r vm (canonical_sum_scalar2 r l0 t));
      == { varlist_merge_ok r vm l0 l }
      aplus (amult c (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar2 r l0 t));
      == { canonical_sum_scalar2_ok r vm l0 t }
      aplus (amult c (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.associativity c (interp_vl r vm l0)
             (interp_vl r vm l) }
      aplus (amult (amult c (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.commutativity (interp_vl r vm l0) c }
      aplus (amult (amult (interp_vl r vm l0) c) (interp_vl r vm l))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.cm_mult.associativity (interp_vl r vm l0) c (interp_vl r vm l) }
      aplus (amult (interp_vl r vm l0) (amult c (interp_vl r vm l)))
            (amult (interp_vl r vm l0) (interp_cs r vm t));
      == { r.distribute (interp_vl r vm l0)
             (amult c (interp_vl r vm l)) (interp_cs r vm t) }
      amult (interp_vl r vm l0)
            (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == {  }
      amult (interp_vl r vm l0) (interp_cs r vm s);
    }
  | Nil_monom -> ()

val canonical_sum_scalar3_ok: #a:eqtype -> r:cr a -> vm:vmap a
  -> c0:a -> l0:varlist -> s:canonical_sum a ->
  Lemma (
    interp_cs r vm (canonical_sum_scalar3 r c0 l0 s) ==
    r.cm_mult.mult (r.cm_mult.mult c0 (interp_vl r vm l0)) (interp_cs r vm s))
let rec canonical_sum_scalar3_ok #a r vm c0 l0 s =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s with
  | Cons_monom c l t ->
    calc (==) {
      interp_cs r vm (canonical_sum_scalar3 r c0 l0 s);
      == { }
      interp_cs r vm
        (monom_insert r (amult c0 c) (varlist_merge l0 l)
          (canonical_sum_scalar3 r c0 l0 t));
      == { monom_insert_ok r vm (amult c0 c) (varlist_merge l0 l) (canonical_sum_scalar3 r c0 l0 t) }
      aplus (amult (amult c0 c) (interp_vl r vm (varlist_merge l0 l)))
            (interp_cs r vm (canonical_sum_scalar3 r c0 l0 t));
      == { varlist_merge_ok r vm l0 l }
      aplus (amult (amult c0 c) (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar3 r c0 l0 t));
      == { canonical_sum_scalar3_ok r vm c0 l0 t }
      aplus (amult (amult c0 c) (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity (amult c0 c)
             (interp_vl r vm l0) (interp_vl r vm l) }
      aplus (amult (amult (amult c0 c) (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.commutativity c0 c }
      aplus (amult (amult (amult c c0) (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity c c0 (interp_vl r vm l0) }
      aplus (amult (amult c (amult c0 (interp_vl r vm l0))) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.commutativity c (amult c0 (interp_vl r vm l0)) }
      aplus (amult (amult (amult c0 (interp_vl r vm l0)) c) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity (amult c0 (interp_vl r vm l0)) c (interp_vl r vm l) }
      aplus (amult (amult c0 (interp_vl r vm l0)) (amult c (interp_vl r vm l)))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.distribute (amult c0 (interp_vl r vm l0))
             (amult c (interp_vl r vm l)) (interp_cs r vm t) }
      amult (amult c0 (interp_vl r vm l0))
            (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == {  }
      amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm s);
    }
  | Cons_varlist l t -> // Same as Cons_monom c l t with c = aone
    let c = aone in
    calc (==) {
      interp_cs r vm (canonical_sum_scalar3 r c0 l0 s);
      == { }
      interp_cs r vm
        (monom_insert r (amult c0 c) (varlist_merge l0 l)
          (canonical_sum_scalar3 r c0 l0 t));
      == { monom_insert_ok r vm (amult c0 c) (varlist_merge l0 l) (canonical_sum_scalar3 r c0 l0 t) }
      aplus (amult (amult c0 c) (interp_vl r vm (varlist_merge l0 l)))
            (interp_cs r vm (canonical_sum_scalar3 r c0 l0 t));
      == { varlist_merge_ok r vm l0 l }
      aplus (amult (amult c0 c) (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (interp_cs r vm (canonical_sum_scalar3 r c0 l0 t));
      == { canonical_sum_scalar3_ok r vm c0 l0 t }
      aplus (amult (amult c0 c) (amult (interp_vl r vm l0) (interp_vl r vm l)))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity (amult c0 c)
             (interp_vl r vm l0) (interp_vl r vm l) }
      aplus (amult (amult (amult c0 c) (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.commutativity c0 c }
      aplus (amult (amult (amult c c0) (interp_vl r vm l0)) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity c c0 (interp_vl r vm l0) }
      aplus (amult (amult c (amult c0 (interp_vl r vm l0))) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.commutativity c (amult c0 (interp_vl r vm l0)) }
      aplus (amult (amult (amult c0 (interp_vl r vm l0)) c) (interp_vl r vm l))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.cm_mult.associativity (amult c0 (interp_vl r vm l0)) c (interp_vl r vm l) }
      aplus (amult (amult c0 (interp_vl r vm l0)) (amult c (interp_vl r vm l)))
            (amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm t));
      == { r.distribute (amult c0 (interp_vl r vm l0))
             (amult c (interp_vl r vm l)) (interp_cs r vm t) }
      amult (amult c0 (interp_vl r vm l0))
            (aplus (amult c (interp_vl r vm l)) (interp_cs r vm t));
      == {  }
      amult (amult c0 (interp_vl r vm l0)) (interp_cs r vm s);
    }
  | Nil_monom -> ()

val canonical_sum_prod_ok: #a:eqtype -> r:cr a -> vm:vmap a ->
  s1:canonical_sum a -> s2:canonical_sum a ->
  Lemma (interp_cs r vm (canonical_sum_prod r s1 s2) ==
         r.cm_mult.mult (interp_cs r vm s1) (interp_cs r vm s2))
let rec canonical_sum_prod_ok #a r vm s1 s2 =
  let aone  = r.cm_mult.unit in
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match s1 with
  | Cons_monom c1 l1 t1 ->
    calc (==) {
      interp_cs r vm (canonical_sum_prod r s1 s2);
      == { }
      interp_cs r vm
        (canonical_sum_merge r (canonical_sum_scalar3 r c1 l1 s2)
                               (canonical_sum_prod r t1 s2));
      == { canonical_sum_merge_ok r vm
             (canonical_sum_scalar3 r c1 l1 s2)
             (canonical_sum_prod r t1 s2) }
      aplus (interp_cs r vm (canonical_sum_scalar3 r c1 l1 s2))
            (interp_cs r vm (canonical_sum_prod r t1 s2));
      == { canonical_sum_scalar3_ok r vm c1 l1 s2;
           canonical_sum_prod_ok r vm t1 s2 }
      aplus (amult (amult c1 (interp_vl r vm l1)) (interp_cs r vm s2))
            (amult (interp_cs r vm t1) (interp_cs r vm s2));
      == { distribute_right r (amult c1 (interp_vl r vm l1))
             (interp_cs r vm t1) (interp_cs r vm s2) }
      amult (aplus (amult c1 (interp_vl r vm l1)) (interp_cs r vm t1))
            (interp_cs r vm s2);
      == { }
      amult (interp_cs r vm s1) (interp_cs r vm s2);
    }
  | Cons_varlist l1 t1 ->
    calc (==) {
      interp_cs r vm (canonical_sum_prod r s1 s2);
      == { }
      interp_cs r vm
        (canonical_sum_merge r (canonical_sum_scalar2 r l1 s2)
                               (canonical_sum_prod r t1 s2));
      == { canonical_sum_merge_ok r vm
             (canonical_sum_scalar2 r l1 s2)
             (canonical_sum_prod r t1 s2) }
      aplus (interp_cs r vm (canonical_sum_scalar2 r l1 s2))
            (interp_cs r vm (canonical_sum_prod r t1 s2));
      == { canonical_sum_scalar2_ok r vm l1 s2;
           canonical_sum_prod_ok r vm t1 s2 }
      aplus (amult (interp_vl r vm l1) (interp_cs r vm s2))
            (amult (interp_cs r vm t1) (interp_cs r vm s2));
      == { distribute_right r (interp_vl r vm l1)
             (interp_cs r vm t1) (interp_cs r vm s2) }
      amult (aplus (interp_vl r vm l1) (interp_cs r vm t1))
            (interp_cs r vm s2);
      == { }
      amult (interp_cs r vm s1) (interp_cs r vm s2);
    }
  | Nil_monom -> ()

val spolynomial_normalize_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:spolynomial a ->
  Lemma (interp_cs r vm (spolynomial_normalize r p) == interp_sp r vm p)
let rec spolynomial_normalize_ok #a r vm p =
  match p with
  | SPvar _ -> ()
  | SPconst _ -> ()
  | SPplus l q ->
    canonical_sum_merge_ok r vm
      (spolynomial_normalize r l) (spolynomial_normalize r q);
    spolynomial_normalize_ok r vm l;
    spolynomial_normalize_ok r vm q
  | SPmult l q ->
    canonical_sum_prod_ok r vm
      (spolynomial_normalize r l) (spolynomial_normalize r q);
    spolynomial_normalize_ok r vm l;
    spolynomial_normalize_ok r vm q

val canonical_sum_simplify_ok: #a:eqtype -> r:cr a -> vm:vmap a -> s:canonical_sum a ->
  Lemma (interp_cs r vm (canonical_sum_simplify r s) == interp_cs r vm s)
let rec canonical_sum_simplify_ok #a r vm s =
  let azero = r.cm_add.unit in
  let aone  = r.cm_mult.unit in
  match s with
  | Cons_monom c _ t -> canonical_sum_simplify_ok r vm t
  | Cons_varlist _ t -> canonical_sum_simplify_ok r vm t
  | Nil_monom -> ()

val spolynomial_simplify_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:spolynomial a ->
  Lemma (interp_cs r vm (spolynomial_simplify r p) == interp_sp r vm p)
let spolynomial_simplify_ok #a r vm p =
  canonical_sum_simplify_ok r vm (spolynomial_normalize r p);
  spolynomial_normalize_ok r vm p


(**
 * This is the type where we first reflect expressions,
 * before eliminating additive inverses
**)
type polynomial a =
  | Pvar   : index -> polynomial a
  | Pconst : a -> polynomial a
  | Pplus  : polynomial a -> polynomial a -> polynomial a
  | Pmult  : polynomial a -> polynomial a -> polynomial a
  | Popp   : polynomial a -> polynomial a

(** Canonize a reflected expression *)
val polynomial_normalize: #a:eqtype -> cr a -> polynomial a -> canonical_sum a

[@@canon_attr]
let rec polynomial_normalize #a r p =
  match p with
  | Pvar i -> Cons_varlist (Cons_var i Nil_var) Nil_monom
  | Pconst c -> Cons_monom c Nil_var Nil_monom
  | Pplus l q ->
    canonical_sum_merge r (polynomial_normalize r l) (polynomial_normalize r q)
  | Pmult l q ->
    canonical_sum_prod r (polynomial_normalize r l) (polynomial_normalize r q)
  | Popp p ->
    canonical_sum_scalar3 r (r.opp r.cm_mult.unit) Nil_var (polynomial_normalize r p)

val polynomial_simplify: #a:eqtype -> cr a -> polynomial a -> canonical_sum a

[@@canon_attr]
let polynomial_simplify #a r p =
  canonical_sum_simplify r
    (polynomial_normalize r p)

(** Translate to a representation without additive inverses *)
val spolynomial_of: #a:eqtype -> cr a -> polynomial a -> spolynomial a

[@@canon_attr]
let rec spolynomial_of #a r p =
  match p with
  | Pvar i -> SPvar i
  | Pconst c -> SPconst c
  | Pplus l q -> SPplus (spolynomial_of r l) (spolynomial_of r q)
  | Pmult l q -> SPmult (spolynomial_of r l) (spolynomial_of r q)
  | Popp p -> SPmult (SPconst (r.opp r.cm_mult.unit)) (spolynomial_of r p)

(** Interpretation of a polynomial *)
[@@canon_attr]
let rec interp_p (#a:Type) (r:cr a) (vm:vmap a) (p:polynomial a) : a =
  let aplus = r.cm_add.mult in
  let amult = r.cm_mult.mult in
  match p with
  | Pconst c -> c
  | Pvar i -> interp_var vm i
  | Pplus p1 p2 -> aplus (interp_p r vm p1) (interp_p r vm p2)
  | Pmult p1 p2 -> amult (interp_p r vm p1) (interp_p r vm p2)
  | Popp p -> r.opp (interp_p r vm p)


val spolynomial_of_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:polynomial a ->
  Lemma (interp_p r vm p == interp_sp r vm (spolynomial_of r p))
let rec spolynomial_of_ok #a r vm p =
  match p with
  | Pconst c -> ()
  | Pvar i -> ()
  | Pplus p1 p2 ->
    spolynomial_of_ok r vm p1;
    spolynomial_of_ok r vm p2
  | Pmult p1 p2 ->
    spolynomial_of_ok r vm p1;
    spolynomial_of_ok r vm p2
  | Popp p ->
    spolynomial_of_ok r vm p;
    let x = interp_sp r vm (spolynomial_of r p) in
    let y = r.cm_mult.mult (r.opp r.cm_mult.unit) x in
    add_mult_opp r x;
    opp_unique r x y


val polynomial_normalize_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:polynomial a ->
  Lemma (interp_cs r vm (polynomial_normalize r p) ==
         interp_cs r vm (spolynomial_normalize r (spolynomial_of r p)))
let rec polynomial_normalize_ok #a r vm p =
  match p with
  | Pvar _ -> ()
  | Pconst _ -> ()
  | Pplus l q ->
    canonical_sum_merge_ok r vm
      (polynomial_normalize r l)
      (polynomial_normalize r q);
    canonical_sum_merge_ok r vm
      (spolynomial_normalize r (spolynomial_of r l))
      (spolynomial_normalize r (spolynomial_of r q));
    polynomial_normalize_ok r vm l;
    polynomial_normalize_ok r vm q

  | Pmult l q ->
    canonical_sum_prod_ok r vm
      (polynomial_normalize r l)
      (polynomial_normalize r q);
    canonical_sum_prod_ok r vm
      (spolynomial_normalize r (spolynomial_of r l))
      (spolynomial_normalize r (spolynomial_of r q));
    polynomial_normalize_ok r vm l;
    polynomial_normalize_ok r vm q

  | Popp p1 ->
    let l = SPconst (r.opp r.cm_mult.unit) in
    polynomial_normalize_ok r vm p1;
    canonical_sum_prod_ok r vm
      (spolynomial_normalize r l)
      (polynomial_normalize r p1);
    canonical_sum_prod_ok r vm
      (spolynomial_normalize r l)
      (spolynomial_normalize r (spolynomial_of r p1))


val polynomial_simplify_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:polynomial a ->
  Lemma (interp_cs r vm (polynomial_simplify r p) == interp_p r vm p)
let polynomial_simplify_ok #a r vm p =
  calc (==) {
    interp_cs r vm (polynomial_simplify r p);
    == { }
    interp_cs r vm (canonical_sum_simplify r (polynomial_normalize r p));
    == { canonical_sum_simplify_ok r vm (polynomial_normalize r p) }
    interp_cs r vm (polynomial_normalize r p);
    == { polynomial_normalize_ok r vm p }
    interp_cs r vm (spolynomial_normalize r (spolynomial_of r p));
    == { spolynomial_normalize_ok r vm (spolynomial_of r p) }
    interp_sp r vm (spolynomial_of r p);
    == { spolynomial_of_ok r vm p }
    interp_p r vm p;
  }


///
/// Tactic definition
///

(* Only dump when debugging is on *)
let ddump m = if debugging () then dump m

(**
 * Finds the position of first occurrence of x in xs.
 * This is specialized to terms and their funny term_eq.
**)
let rec find_aux (n:nat) (x:term) (xs:list term) : Tac (option nat) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else find_aux (n+1) x xs'

let find = find_aux 0

let make_fvar (#a:Type) (t:term) (unquotea:term -> Tac a) (ts:list term)
  (vm:vmap a) : Tac (polynomial a & list term & vmap a) =
  match find t ts with
  | Some v -> (Pvar v, ts, vm)
  | None ->
    let vfresh = length ts in
    let z = unquotea t in
    (Pvar vfresh, ts @ [t], update vfresh z vm)

(** This expects that add, opp, mone mult, and t have already been normalized *)
let rec reification_aux (#a:Type) (unquotea:term -> Tac a) (ts:list term) (vm:vmap a) (add opp mone mult t: term) : Tac (polynomial a & list term & vmap a) =
  // ddump ("term = " ^ term_to_string t ^ "\n");
  let hd, tl = collect_app_ref t in
  match inspect hd, list_unref tl with
  | Tv_FVar fv, [(t1, _) ; (t2, _)] ->
    //ddump ("add = " ^ term_to_string add ^ "
    //     \nmul = " ^ term_to_string mult);
    //ddump ("fv = " ^ term_to_string (pack (Tv_FVar fv)));
    let binop (op:polynomial a -> polynomial a -> polynomial a) : Tac (polynomial a & list term & vmap a) =
      let (e1, ts, vm) = reification_aux unquotea ts vm add opp mone mult t1 in
      let (e2, ts, vm) = reification_aux unquotea ts vm add opp mone mult t2 in
      (op e1 e2, ts, vm)
      in
    if term_eq (pack (Tv_FVar fv)) add then binop Pplus else
    if term_eq (pack (Tv_FVar fv)) mult then binop Pmult else
    make_fvar t unquotea ts vm
  | Tv_FVar fv, [(t1, _)] ->
    let monop (op:polynomial a -> polynomial a) : Tac (polynomial a & list term & vmap a) =
      let (e, ts, vm) = reification_aux unquotea ts vm add opp mone mult t1 in
      (op e, ts, vm)
      in
    if term_eq (pack (Tv_FVar fv)) opp then monop Popp else
    make_fvar t unquotea ts vm
  | Tv_Const _, [] -> Pconst (unquotea t), ts, vm
  | _, _ -> make_fvar t unquotea ts vm

(**
 * How to normalize terms in the tactic.
 * This is carefully tuned to unfold all and no more than required
**)
let steps =
  [
    primops;
    iota;
    zeta;
    delta_attr [`%canon_attr];
    delta_only [
      `%FStar.Mul.op_Star;                        // For integer ring
      `%FStar.Algebra.CommMonoid.int_plus_cm;     // For integer ring
      `%FStar.Algebra.CommMonoid.int_multiply_cm; // For integer ring
      `%FStar.Algebra.CommMonoid.__proj__CM__item__mult;
      `%FStar.Algebra.CommMonoid.__proj__CM__item__unit;
      `%__proj__CR__item__cm_add;
      `%__proj__CR__item__opp;
      `%__proj__CR__item__cm_mult;
      `%FStar.List.Tot.assoc;
      `%FStar.Pervasives.Native.fst;
      `%FStar.Pervasives.Native.snd;
      `%FStar.Pervasives.Native.__proj__Mktuple2__item___1;
      `%FStar.Pervasives.Native.__proj__Mktuple2__item___2;
      `%FStar.List.Tot.op_At;
      `%FStar.List.Tot.append;
    ]
  ]

let canon_norm () : Tac unit = norm steps

let reification (#a:Type)
  (unquotea:term -> Tac a) (quotea:a -> Tac term) (tadd topp tmone tmult:term) (munit:a) (ts:list term) : Tac (list (polynomial a) & vmap a) =
  // Be careful not to normalize operations too much
  // E.g. we don't want to turn ( +% ) into (a + b) % prime
  // or we won't be able to spot ring operations
  let add  = tadd in
  let opp  = topp in
  let mone = tmone in
  let mult = tmult in
  let ts = Tactics.Util.map (norm_term steps) ts in
  //ddump ("add = " ^ term_to_string add ^ "\nmult = " ^ term_to_string mult);
  let (es, _, vm) =
    Tactics.Util.fold_left
      (fun (es, vs, vm) t ->
        let (e, vs, vm) = reification_aux unquotea vs vm add opp mone mult t
        in (e::es, vs, vm))
      ([],[], ([], munit)) ts
  in (List.Tot.Base.rev es, vm)

(* The implicit argument in the application of `Pconst` is crucial *)
let rec quote_polynomial (#a:Type) (ta:term) (quotea:a -> Tac term) (e:polynomial a) : Tac term =
  match e with
  | Pconst c -> mk_app (`Pconst) [(ta, Q_Implicit); (quotea c, Q_Explicit)]
  | Pvar x -> mk_e_app (`Pvar) [pack (Tv_Const (C_Int x))]
  | Pplus e1 e2 ->
    mk_e_app (`Pplus) [quote_polynomial ta quotea e1; quote_polynomial ta quotea e2]
  | Pmult e1 e2 ->
    mk_e_app (`Pmult) [quote_polynomial ta quotea e1; quote_polynomial ta quotea e2]
  | Popp e -> mk_e_app (`Popp) [quote_polynomial ta quotea e]

(* Constructs the 3 main goals of the tactic *)
let semiring_reflect (#a:eqtype) (r:cr a) (vm:vmap a) (e1 e2:polynomial a) (a1 a2:a)
    (_ : squash (
      interp_cs r vm (polynomial_simplify r e1) ==
      interp_cs r vm (polynomial_simplify r e2)))
    (_ : squash (a1 == interp_p r vm e1))
    (_ : squash (a2 == interp_p r vm e2)) :
    squash (a1 == a2)
  =
  polynomial_simplify_ok r vm e1;
  polynomial_simplify_ok r vm e2

(* [@@plugin] *)
let canon_semiring_aux
    (a: Type) (ta: term) (unquotea: term -> Tac a) (quotea: a -> Tac term)
    (tr tadd topp tmone tmult: term)
    (munit: a)
  : Tac unit
=
  focus (fun () ->
  norm []; // Do not normalize anything implicitly
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq (Some t)) t1 t2 ->
    (* First, make sure we have an equality at type ta, since otherwise
    we will fail to apply the reflection Lemma. We can just cut by the equality
    we want, since they should be equiprovable (though not equal). *)
    let b = tcut (`(squash (eq2 #(`#ta) (`#t1) (`#t2)))) in
    (* Try solving it trivially if type was exactly the same, or give to smt.
    It should really be trivial. *)
    begin
      try exact b with | _ -> smt ()
    end;
    begin
    match reification unquotea quotea tadd topp tmone tmult munit [t1; t2] with
    | ([e1; e2], vm) ->
(*
      ddump (term_to_string t1);
      ddump (term_to_string t2);
      let r : cr a = unquote tr in
      ddump ("vm = " ^ term_to_string (quote vm) ^ "\n" ^
             "before = " ^ term_to_string (norm_term steps
                  (quote (interp_p r vm e1 == interp_p r vm e2))));
      dump ("expected after = " ^ term_to_string (norm_term steps
        (quote (
            interp_cs r vm (polynomial_simplify r e1) ==
            interp_cs r vm (polynomial_simplify r e2)))));
*)
      let tvm = quote_vm ta quotea vm in
      let te1 = quote_polynomial ta quotea e1 in
      //ddump ("te1 = " ^ term_to_string te1);
      let te2 = quote_polynomial ta quotea e2 in
      //ddump ("te2 = " ^ term_to_string te2);
      mapply (`(semiring_reflect
        #(`#ta) (`#tr) (`#tvm) (`#te1) (`#te2) (`#t1) (`#t2)));
      //ddump "Before canonization";
      canon_norm ();
      //ddump "After canonization";
      later ();
      //ddump "Before normalizing left-hand side";
      canon_norm ();
      //ddump "After normalizing left-hand side";
      trefl ();
      //ddump "Before normalizing right-hand side";
      canon_norm ();
      //ddump "After normalizing right-hand side";
      trefl ()
    | _ -> fail "Unexpected"
    end
  | _ -> fail "Goal should be an equality")

let canon_semiring (#a:eqtype) (r:cr a) : Tac unit =
  canon_semiring_aux a
    (quote a) (unquote #a) (fun (x:a) -> quote x) (quote r)
    (norm_term steps (quote r.cm_add.mult))
    (norm_term steps (quote r.opp))
    (norm_term steps (quote (r.opp r.cm_mult.unit)))
    (norm_term steps (quote r.cm_mult.mult))
    r.cm_add.unit

///  Ring of integers

[@@canon_attr]
let int_cr : cr int =
  CR int_plus_cm int_multiply_cm op_Minus (fun x -> ()) (fun x y z -> ()) (fun x -> ())

let int_semiring () : Tac unit = canon_semiring int_cr
