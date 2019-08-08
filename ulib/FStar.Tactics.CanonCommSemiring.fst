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

/// A tactic to solve equalities on commutative semirings
///
/// This requires the following properties:
/// - addition is commutative and associative, where zero is the additive identity
/// - multiplication is commutative and associative, where one is the multiplicative identity
/// - multiplication distributes over addition
///
/// Based on the legacy second version of Coq's ring tactic:
///   https://github.com/coq-contribs/legacy-ring/
///
/// In contrast to FStar.Tactics.CanonCommSemiring in master,
/// the tactic defined here canonizes products and additions, gathers duplicate monomials, and eliminates trivial expressions.

open FStar.List
open FStar.Tactics
open FStar.Reflection
open FStar.Classical
open FStar.Algebra.CommMonoid

module CCM = FStar.Tactics.CanonCommMonoid

(* Only dump when debugging is on *)
let ddump m = if debugging () then dump m

irreducible let canon_attr = ()

[@canon_attr]
unfold let cm_op = CM?.mult

(***** Commutative semirings *)

let distribute_left_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  let (+) = cm_op cm_add in
  let ( * ) = cm_op cm_mult in
  x:a -> y:a -> z:a -> Lemma (x * (y + z) == x * y + x * z)

let distribute_right_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  let (+) = cm_op cm_add in
  let ( * ) = cm_op cm_mult in
  x:a -> y:a -> z:a -> Lemma ((x + y) * z == x * z + y * z)

[@canon_attr]
unopteq
type cr (a:Type) =
  | CR :
    cm_add:cm a ->
    cm_mult:cm a ->
    distribute:distribute_left_lemma a cm_add cm_mult ->
    cr a

let distribute_right (#a:Type) (r:cr a) : distribute_right_lemma a r.cm_add r.cm_mult =
  fun x y z ->
    CM?.commutativity r.cm_mult (cm_op r.cm_add x y) z;
    r.distribute z x y;
    CM?.commutativity r.cm_mult x z;
    CM?.commutativity r.cm_mult y z

[@canon_attr]
let int_cr : cr int =
  CR int_plus_cm int_multiply_cm (fun x y z -> ())

(***** Expression syntax *)

let index : eqtype = nat

type varlist : Type =
  | Nil_var : varlist
  | Cons_var : index -> varlist -> varlist

type canonical_sum (a:Type) : Type =
  | Nil_monom : canonical_sum a
  | Cons_monom : a -> varlist -> canonical_sum a -> canonical_sum a
  | Cons_varlist : varlist -> canonical_sum a -> canonical_sum a

(* Order on monoms *)

(* That's the lexicographic order on varlist, extended by :
  - A constant is less than every monom
  - The relation between two varlist is preserved by multiplication by a
  constant.
  Examples :
  3 < x < y
  x*y < x*y*y*z
  2*x*y < x*y*y*z
  x*y < 54*x*y*y*z
  4*x*y < 59*x*y*y*z
*)

[@canon_attr]
let rec varlist_lt (x y:varlist) : bool =
  match x, y with
  | Nil_var, Cons_var _ _ -> true
  | Cons_var i xrest, Cons_var j yrest ->
      if i < j
      then true
      else i = j && varlist_lt xrest yrest
  | _, _ -> false


[@canon_attr]
val varlist_merge: l1:varlist -> l2:varlist -> Tot varlist (decreases %[l1; l2; 0])

[@canon_attr]
val vm_aux: index -> t1:varlist -> l2:varlist -> Tot varlist (decreases %[t1; l2; 1])

(* merges two variables lists *)
[@canon_attr]
let rec varlist_merge l1 l2 =
  match l1, l2 with
  | Cons_var v1 t1, Nil_var -> l1
  | Cons_var v1 t1, Cons_var v2 t2 -> vm_aux v1 t1 l2
  | Nil_var, _ -> l2
and vm_aux v1 t1 l2 =
  match l2 with
  | Cons_var v2 t2 ->
    if v1 < v2
    then Cons_var v1 (varlist_merge t1 l2)
    else Cons_var v2 (vm_aux v1 t1 t2)
 | _ -> Cons_var v1 t1


(* returns the sum of two canonical sums  *)
[@canon_attr]
val canonical_sum_merge : #a:Type0 -> cr a -> s1:canonical_sum a
  -> s2:canonical_sum a -> Tot (canonical_sum a) (decreases %[s1; s2; 0])

[@canon_attr]
val csm_aux: #a:Type0 -> r:cr a -> c1:a -> l1:varlist -> t1:canonical_sum a
  -> s2:canonical_sum a -> Tot (canonical_sum a) (decreases %[t1; s2; 1])

[@canon_attr]
val csm_aux2: #a:Type0 -> r:cr a -> l1:varlist -> t1:canonical_sum a
  -> s2:canonical_sum a -> Tot (canonical_sum a) (decreases %[t1; s2; 1])

[@canon_attr]
let rec canonical_sum_merge #a r s1 s2 =
  let aplus = cm_op r.cm_add in
  let aone = CM?.unit r.cm_mult in
  match s1 with
  | Cons_monom c1 l1 t1 -> csm_aux #a r c1 l1 t1 s2
  | Cons_varlist l1 t1 -> csm_aux2 #a r l1 t1 s2
  | Nil_monom -> s2

and csm_aux #a r c1 l1 t1 s2 =
  let aplus = cm_op r.cm_add in
  let aone = CM?.unit r.cm_mult in
  match s2 with
  | Cons_monom c2 l2 t2 ->
      if l1 = l2
      then Cons_monom (aplus c1 c2) l1 (canonical_sum_merge #a r t1 t2)
      else
       if varlist_lt l1 l2
       then Cons_monom c1 l1 (canonical_sum_merge r t1 s2)
       else Cons_monom c2 l2 (csm_aux #a r c1 l1 t1 t2)
  | Cons_varlist l2 t2 ->
      if l1 = l2
      then Cons_monom (aplus c1 aone) l1 (canonical_sum_merge r t1 t2)
      else
       if varlist_lt l1 l2
       then Cons_monom c1 l1 (canonical_sum_merge r t1 s2)
       else Cons_varlist l2 (csm_aux #a r c1 l1 t1 t2)
  | Nil_monom -> Cons_monom c1 l1 t1

and csm_aux2 #a r l1 t1 s2 =
  let aplus = cm_op r.cm_add in
  let aone = CM?.unit r.cm_mult in
  match s2 with
  | Cons_monom c2 l2 t2 ->
      if l1 = l2
      then Cons_monom (aplus aone c2) l1 (canonical_sum_merge r t1 t2)
      else
       if varlist_lt l1 l2
       then Cons_varlist l1 (canonical_sum_merge r t1 s2)
       else Cons_monom c2 l2 (csm_aux2 #a r l1 t1 t2)
  | Cons_varlist l2 t2 ->
      if l1 = l2
      then Cons_monom (aplus aone aone) l1 (canonical_sum_merge r t1 t2)
      else
       if varlist_lt l1 l2
       then Cons_varlist l1 (canonical_sum_merge r t1 s2)
       else Cons_varlist l2 (csm_aux2 #a r l1 t1 t2)
  | Nil_monom -> Cons_varlist l1 t1


[@canon_attr]
let rec monom_insert (#a:Type) (r:cr a) (c1:a) (l1:varlist) (s2:canonical_sum a) :
 canonical_sum a =
  let aplus = cm_op r.cm_add in
  let aone = CM?.unit r.cm_add in
  match s2 with
  | Cons_monom c2 l2 t2 ->
      if l1 = l2
      then Cons_monom (aplus c1 c2) l1 t2
      else
       if varlist_lt l1 l2
       then Cons_monom c1 l1 s2
       else Cons_monom c2 l2 (monom_insert r c1 l1 t2)
  | Cons_varlist l2 t2 ->
      if l1 = l2
      then Cons_monom (aplus c1 aone) l1 t2
      else
       if varlist_lt l1 l2
       then Cons_monom c1 l1 s2
       else Cons_varlist l2 (monom_insert r c1 l1 t2)
  | Nil_monom -> Cons_monom c1 l1 Nil_monom

[@canon_attr]
let rec varlist_insert (#a:Type) (r:cr a) (l1:varlist) (s2:canonical_sum a) :
 canonical_sum a =
  let aplus = cm_op r.cm_add in
  let aone = CM?.unit r.cm_add in
  match s2 with
  | Cons_monom c2 l2 t2 ->
      if l1 = l2
      then Cons_monom (aplus aone c2) l1 t2
      else
       if varlist_lt l1 l2
       then Cons_varlist l1 s2
       else Cons_monom c2 l2 (varlist_insert r l1 t2)
  | Cons_varlist l2 t2 ->
      if l1 = l2
      then Cons_monom (aplus aone aone) l1 t2
      else
       if varlist_lt l1 l2
       then Cons_varlist l1 s2
       else Cons_varlist l2 (varlist_insert r l1 t2)
  | Nil_monom -> Cons_varlist l1 Nil_monom

[@canon_attr]
let rec canonical_sum_scalar (#a:Type) (r:cr a) (c0:a) (s:canonical_sum a) :
 canonical_sum a =
  let amult = cm_op r.cm_mult in
  match s with
  | Cons_monom c l t -> Cons_monom (amult c0 c) l (canonical_sum_scalar r c0 t)
  | Cons_varlist l t -> Cons_monom c0 l (canonical_sum_scalar r c0 t)
  | Nil_monom -> Nil_monom

(* Computes l0*s  *)
[@canon_attr]
let rec canonical_sum_scalar2 (#a:Type) (r:cr a) (l0:varlist) (s:canonical_sum a) :
 canonical_sum a =
  match s with
  | Cons_monom c l t ->
    monom_insert r c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t)
  | Cons_varlist l t ->
    varlist_insert r (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t)
  | Nil_monom -> Nil_monom

(* Computes c0*l0*s  *)
[@canon_attr]
let rec canonical_sum_scalar3 (#a:Type) (r:cr a) (c0:a) (l0:varlist)
 (s:canonical_sum a) : canonical_sum a =
  let amult = cm_op r.cm_mult in
  match s with
  | Cons_monom c l t ->
     monom_insert r (amult c0 c) (varlist_merge l0 l)
       (canonical_sum_scalar3 r c0 l0 t)
  | Cons_varlist l t ->
     monom_insert r c0 (varlist_merge l0 l) (canonical_sum_scalar3 r c0 l0 t)
  | Nil_monom -> Nil_monom

(* returns the product of two canonical sums *)
[@canon_attr]
let rec canonical_sum_prod (#a:Type) (r:cr a) (s1 s2:canonical_sum a) :
 canonical_sum a =
  match s1 with
  | Cons_monom c1 l1 t1 ->
      canonical_sum_merge r (canonical_sum_scalar3 r c1 l1 s2)
        (canonical_sum_prod r t1 s2)
  | Cons_varlist l1 t1 ->
      canonical_sum_merge r (canonical_sum_scalar2 r l1 s2)
        (canonical_sum_prod r t1 s2)
  | Nil_monom -> Nil_monom

(* The type to represent concrete semi-ring polynomials *)
type spolynomial (a:Type) : Type =
  | SPvar : index -> spolynomial a
  | SPconst : a -> spolynomial a
  | SPplus : spolynomial a -> spolynomial a -> spolynomial a
  | SPmult : spolynomial a -> spolynomial a -> spolynomial a


[@canon_attr]
let rec spolynomial_normalize (#a:Type) (r:cr a) (p:spolynomial a) : canonical_sum a =
  match p with
  | SPvar i -> Cons_varlist (Cons_var i Nil_var) Nil_monom
  | SPconst c -> Cons_monom c Nil_var Nil_monom
  | SPplus l q ->
    canonical_sum_merge r (spolynomial_normalize r l) (spolynomial_normalize r q)
  | SPmult l q ->
    canonical_sum_prod r (spolynomial_normalize r l) (spolynomial_normalize r q)

(* Deletion of useless 0 and 1 in canonical sums *)
[@canon_attr]
let rec canonical_sum_simplify (#a:eqtype) (r:cr a) (s:canonical_sum a) : canonical_sum a =
  let azero = CM?.unit r.cm_add in
  let aone = CM?.unit r.cm_mult in
  match s with
  | Cons_monom c l t ->
      if c = azero
      then canonical_sum_simplify r t
      else
       if c = aone
       then Cons_varlist l (canonical_sum_simplify r t)
       else Cons_monom c l (canonical_sum_simplify r t)
  | Cons_varlist l t -> Cons_varlist l (canonical_sum_simplify r t)
  | Nil_monom -> Nil_monom

[@canon_attr]
let spolynomial_simplify (#a:eqtype) (r:cr a) (x:spolynomial a) =
  canonical_sum_simplify r (spolynomial_normalize r x)

(* End definitions. *)

(* Section interpretation. *)

(* Here a variable map is defined and the interpetation of a spolynom
  acording to a certain variables map. Once again the choosen definition
  is generic and could be changed *)

let vmap (a:Type) = CCM.vmap a unit

(* Interpretation of list of variables
 * [x1; ... ; xn ] is interpreted as (find v x1)* ... *(find v xn)
 * The unbound variables are mapped to 0. Normally this case sould
 * never occur. Since we want only to prove correctness theorems, which form
 * is : for any varmap and any spolynom ... this is a safe and pain-saving
 * choice *)
[@canon_attr]
let interp_var (#a:Type) (vm:vmap a) (i:index) =
  match assoc i (fst vm) with
  | Some (x, _) -> x
  | _ -> fst (snd vm)

[@canon_attr]
private
let rec ivl_aux (#a:Type) (r:cr a) (vm:vmap a) (x:index) (t:varlist)
  : Tot a (decreases t) =
  let amult = cm_op r.cm_mult in
  match t with
  | Nil_var -> interp_var vm x
  | Cons_var x' t' -> amult (interp_var vm x) (ivl_aux r vm x' t')

[@canon_attr]
let interp_vl (#a:Type) (r:cr a) (vm:vmap a) (l:varlist) =
  let aone = CM?.unit r.cm_mult in
  match l with
  | Nil_var -> aone
  | Cons_var x t -> ivl_aux r vm x t

[@canon_attr]
private
let rec interp_m (#a:Type) (r:cr a) (vm:vmap a) (c:a) (l:varlist) =
  let amult = cm_op r.cm_mult in
  match l with
  | Nil_var -> c
  | Cons_var x t -> amult c (ivl_aux r vm x t)

[@canon_attr]
private
let rec ics_aux (#a:Type) (r:cr a) (vm:vmap a) (x:a) (s:canonical_sum a)
  : Tot a (decreases s) =
  let aplus = cm_op r.cm_add in
  match s with
  | Nil_monom -> x
  | Cons_varlist l t -> aplus x (ics_aux r vm (interp_vl r vm l) t)
  | Cons_monom c l t -> aplus x (ics_aux r vm (interp_m r vm c l) t)

(* Interpretation of a canonical sum *)
[@canon_attr]
let interp_cs (#a:Type) (r:cr a) (vm:vmap a) (s:canonical_sum a) : a =
  let azero = CM?.unit r.cm_add in
  match s with
  | Nil_monom -> azero
  | Cons_varlist l t -> ics_aux r vm (interp_vl r vm l) t
  | Cons_monom c l t -> ics_aux r vm (interp_m r vm c l) t

[@canon_attr]
let rec interp_sp (#a:Type) (r:cr a) (vm:vmap a) (p:spolynomial a) : a =
  let aplus = cm_op r.cm_add in
  let amult = cm_op r.cm_mult in
  match p with
  | SPconst c -> c
  | SPvar i -> interp_var vm i
  | SPplus p1 p2 -> aplus (interp_sp r vm p1) (interp_sp r vm p2)
  | SPmult p1 p2 -> amult (interp_sp r vm p1) (interp_sp r vm p2)

(* End interpretation. *)

val ivl_aux_ok (#a:eqtype) (r:cr a) (vm:vmap a) (v:varlist) (i:index) : Lemma
  (ivl_aux r vm i v == cm_op r.cm_mult (interp_var vm i) (interp_vl r vm v))
let ivl_aux_ok #a r vm v i =
  match v with
  | Nil_var ->
    begin
    CM?.commutativity r.cm_mult (CM?.unit r.cm_mult) (interp_var vm i);
    CM?.identity r.cm_mult (interp_var vm i)
    end
  | Cons_var x xs -> ()

val varlist_merge_ok (#a:eqtype) (r:cr a) (vm:vmap a) (x y:varlist) :
  Lemma (interp_vl r vm (varlist_merge x y) ==
         cm_op r.cm_mult (interp_vl r vm x) (interp_vl r vm y))
let rec varlist_merge_ok #a r vm x y =
  let amult = cm_op r.cm_mult in
  match x, y with
  | Cons_var v1 t1, Nil_var ->
    begin
    CM?.identity r.cm_mult (interp_vl r vm x);
    CM?.commutativity r.cm_mult (CM?.unit r.cm_mult) (interp_vl r vm x)
    end
  | Cons_var v1 t1, Cons_var v2 t2 ->
    if v1 < v2
    then
      begin
      varlist_merge_ok r vm t1 y;
      assert (
        interp_vl r vm (varlist_merge x y) ==
        amult (interp_var vm v1) (amult (interp_vl r vm t1) (interp_vl r vm y)));
      CM?.associativity r.cm_mult
        (interp_var vm v1) (interp_vl r vm t1) (interp_vl r vm y)
      end
    else
      begin
      varlist_merge_ok r vm t1 t2;
      assert (
        interp_vl r vm (varlist_merge x y) ==
        amult (interp_var vm v2) (interp_vl r vm (vm_aux v1 t1 t2)));
      ivl_aux_ok r vm t1 v1;
      ivl_aux_ok r vm t2 v2;
      CM?.associativity r.cm_mult
        (interp_var vm v2) (interp_vl r vm t1) (interp_vl r vm t2);
       admit()
      end
  | Nil_var, _ ->
    begin
    CM?.identity r.cm_mult (interp_vl r vm y);
    CM?.commutativity r.cm_mult (CM?.unit r.cm_mult) (interp_vl r vm y)
    end

val ics_aux_ok: #a:Type -> r:cr a -> vm:vmap a -> x:a -> s:canonical_sum a ->
  Lemma (ensures ics_aux r vm x s == cm_op r.cm_add x (interp_cs r vm s))
  (decreases s)
let rec ics_aux_ok #a r vm x s =
  match s with
  | Nil_monom ->
    CM?.identity r.cm_add x;
    CM?.commutativity r.cm_add x (CM?.unit r.cm_add)
  | Cons_varlist l t ->
    ics_aux_ok r vm (interp_vl r vm l) t
  | Cons_monom c l t ->
    ics_aux_ok r vm (interp_m r vm c l) t

val interp_m_ok: #a:Type -> r:cr a -> vm:vmap a -> x:a -> l:varlist ->
  Lemma (interp_m r vm x l == cm_op r.cm_mult x (interp_vl r vm l))
let interp_m_ok #a r vm x l =
  match l with
  | Nil_var ->
    CM?.identity r.cm_mult x;
    CM?.commutativity r.cm_mult x (CM?.unit r.cm_mult)
  | _ -> ()


val aplus_assoc_4: #a:Type -> r:cr a -> w:a -> x:a -> y:a -> z:a -> Lemma
  (let aplus = cm_op r.cm_add in
   aplus (aplus w x) (aplus y z) == aplus (aplus w y) (aplus x z))
let aplus_assoc_4 #a r w x y z =
  let aplus = cm_op r.cm_add in
  let assoc = CM?.associativity r.cm_add in
  let comm = CM?.commutativity r.cm_add in
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

val canonical_sum_merge_ok: #a:Type -> r:cr a -> vm:vmap a -> x:canonical_sum a -> y:canonical_sum a ->
  Lemma (interp_cs r vm (canonical_sum_merge r x y) ==
         cm_op r.cm_add (interp_cs r vm x) (interp_cs r vm y))
let rec canonical_sum_merge_ok #a r vm x y =
  let aplus = cm_op r.cm_add in
  let aone = CM?.unit r.cm_mult in
  let amult = cm_op r.cm_mult in
  match x with
  | Nil_monom ->
    CM?.identity r.cm_add (interp_cs r vm y);
    CM?.commutativity r.cm_add (interp_cs r vm y) (CM?.unit r.cm_add)
  | Cons_monom c1 l1 t1 ->
    begin
    match y with
    | Nil_monom ->
      CM?.identity r.cm_add (interp_cs r vm x);
      CM?.commutativity r.cm_add (interp_cs r vm x) (CM?.unit r.cm_add)

    | Cons_monom c2 l2 t2 ->
      if l1 = l2 then
        begin
        calc (==) {
          interp_cs r vm (canonical_sum_merge r x y);
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
          aplus (interp_cs r vm x)
                (aplus (amult c2 (interp_vl r vm l2)) (interp_cs r vm t2));
          == { ics_aux_ok r vm (amult c2 (interp_vl r vm l2)) t2;
               interp_m_ok r vm c2 l2 }
          aplus (interp_cs r vm x) (interp_cs r vm y);
        }
        end
      else if varlist_lt l1 l2 then
        begin
        calc (==) {
          interp_cs r vm (canonical_sum_merge r x y);
          == { }
          ics_aux r vm (interp_m r vm c1 l1)
                       (canonical_sum_merge r t1 y);
          == { ics_aux_ok r vm (interp_m r vm c1 l1)
                               (canonical_sum_merge r t1 y) }
          aplus (interp_m r vm c1 l1)
                (interp_cs r vm (canonical_sum_merge r t1 y));
          == { interp_m_ok r vm c1 l1 }
          aplus (amult c1 (interp_vl r vm l1))
                (interp_cs r vm (canonical_sum_merge r t1 y));
          == { canonical_sum_merge_ok r vm t1 y }
          aplus (amult c1 (interp_vl r vm l1))
                (aplus (interp_cs r vm t1) (interp_cs r vm y));
          == { admit() }
          aplus (aplus (amult c1 (interp_vl r vm l1))
                       (interp_cs r vm t1))
                (interp_cs r vm y);
          == { ics_aux_ok r vm (amult c1 (interp_vl r vm l1)) t1;
               interp_m_ok r vm c1 l1 }
          aplus (interp_cs r vm x) (interp_cs r vm y);
        }
       end
      else admit()
    | _ -> admit()
    end
  | _ -> admit()

val spolynomial_normalize_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:spolynomial a ->
  Lemma (interp_cs r vm (spolynomial_normalize r p) == interp_sp r vm p)
let spolynomial_normalize_ok #a r vm p =
  admit()

val canonical_sum_simplify_ok: #a:eqtype -> r:cr a -> vm:vmap a -> s:canonical_sum a ->
  Lemma (interp_cs r vm (canonical_sum_simplify r s) == interp_cs r vm s)
let canonical_sum_simplify_ok #a r vm s =
  admit()

val spolynomial_simplify_ok: #a:eqtype -> r:cr a -> vm:vmap a -> p:spolynomial a ->
  Lemma (interp_cs r vm (spolynomial_simplify r p) == interp_sp r vm p)
let spolynomial_simplify_ok #a r vm p =
  canonical_sum_simplify_ok r vm (spolynomial_normalize r p);
  spolynomial_normalize_ok r vm p


/// Tactic

let make_fvar (#a:Type) (t:term) (unquotea:term -> Tac a) (ts:list term) (vm:vmap a) : Tac
    (spolynomial a * list term * vmap a) =
  match CCM.where t ts with
  | Some v -> (SPvar v, ts, vm)
  | None ->
    let vfresh = length ts in
    let z = unquotea t in
    (SPvar vfresh, ts @ [t], CCM.update vfresh z () vm)

// This expects that add, mult, and t have already been normalized
let rec reification_aux (#a:Type) (unquotea:term -> Tac a) (ts:list term) (vm:vmap a) (add mult t: term) : Tac (spolynomial a * list term * vmap a) =
  let hd, tl = collect_app_ref t in
  match inspect hd, list_unref tl with
  | (Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)]) ->
    let binop (op:spolynomial a -> spolynomial a -> spolynomial a) : Tac (spolynomial a * list term * vmap a) =
      let (e1, ts, vm) = reification_aux unquotea ts vm add mult t1 in
      let (e2, ts, vm) = reification_aux unquotea ts vm add mult t2 in
      (op e1 e2, ts, vm)
      in
    if term_eq (pack (Tv_FVar fv)) add then binop SPplus else
    if term_eq (pack (Tv_FVar fv)) mult then binop SPmult else
    make_fvar t unquotea ts vm
  | (_, _) -> make_fvar t unquotea ts vm

let reification (#a:Type)
    (unquotea:term->Tac a) (quotea:a -> Tac term) (tadd tmult:term) (munit:a) (ts:list term) :
    Tac (list (spolynomial a) * vmap a) =
  let add = norm_term [delta] tadd in
  let mult = norm_term [delta] tmult in
  let ts = Tactics.Util.map (norm_term [delta]) ts in
  //ddump ("add = " ^ term_to_string add ^ "; mult = " ^ term_to_string mult);
  let (es, _, vm) =
    Tactics.Util.fold_left
      (fun (es,vs,vm) t ->
        let (e,vs,vm) = reification_aux unquotea vs vm add mult t
        in (e::es,vs,vm))
      ([],[], ([], (munit, ()))) ts
  in (List.rev es,vm)

let canon_norm () : Tac unit =
  norm [
    primops;
    iota;
    zeta;
    delta_attr [`%canon_attr];
    delta_only [
      "FStar.Algebra.CommMonoid.int_plus_cm";
      "FStar.Algebra.CommMonoid.int_multiply_cm";
      "FStar.Algebra.CommMonoid.__proj__CM__item__mult";
      "FStar.Algebra.CommMonoid.__proj__CM__item__unit";
      "FStar.Tactics.CanonCommSemiring.__proj__CR__item__cm_add";
      "FStar.Tactics.CanonCommSemiring.__proj__CR__item__cm_mult";
      "FStar.Tactics.CanonCommMonoid.canon";
      "FStar.Tactics.CanonCommMonoid.xsdenote";
      "FStar.Tactics.CanonCommMonoid.flatten";
      "FStar.Tactics.CanonCommMonoid.select";
      "FStar.Tactics.CanonCommMonoid.select_extra";
      "FStar.Tactics.CanonCommMonoid.const_last";
      "FStar.Tactics.CanonCommMonoid.const_compare";
      "FStar.Tactics.CanonCommMonoid.special_compare";
      "FStar.Tactics.CanonCommMonoid.sortWith_correct";
      "FStar.List.Tot.Base.assoc";
      "FStar.Pervasives.Native.fst";
      "FStar.Pervasives.Native.snd";
      "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
      "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
      "FStar.List.Tot.Base.op_At";
      "FStar.List.Tot.Base.append";
      "FStar.List.Tot.Base.sortWith";
      "FStar.List.Tot.Base.partition";
      "FStar.List.Tot.Base.bool_of_compare";
      "FStar.List.Tot.Base.compare_of_bool";
    ]
  ]


let rec quote_spolynomial (#a:Type) (e:spolynomial a) : Tac term =
  match e with
  | SPconst c -> quote (SPconst c)
  | SPvar x -> mk_e_app (`SPvar) [pack (Tv_Const (C_Int x))]
  | SPplus e1 e2 -> mk_e_app (`SPplus) [quote_spolynomial e1; quote_spolynomial e2]
  | SPmult e1 e2 -> mk_e_app (`SPmult) [quote_spolynomial e1; quote_spolynomial e2]

let semiring_reflect (#a:eqtype) (r:cr a) (vm:vmap a) (e1 e2:spolynomial a) (a1 a2:a)
    (_ : squash (
      interp_cs r vm (spolynomial_simplify r e1) ==
      interp_cs r vm (spolynomial_simplify r e2)))
    (_ : squash (a1 == interp_sp r vm e1))
    (_ : squash (a2 == interp_sp r vm e2)) :
    squash (a1 == a2)
  =
  spolynomial_simplify_ok r vm e1;
  spolynomial_simplify_ok r vm e2

[@plugin]
let canon_semiring_aux
    (a: Type) (ta: term) (unquotea: term -> Tac a) (quotea: a -> Tac term)
    (tr tadd tmult: term) (munit: a) (tb: term)
  : Tac unit =
  focus (fun () ->
  norm [];
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq (Some t)) t1 t2 ->
    (
      //ddump ("t1 = " ^ term_to_string t1 ^ "; t2 = " ^ term_to_string t2);
      if term_eq t ta then
      (
        match reification unquotea quotea tadd tmult munit [t1; t2] with
        | ([e1; e2], vm) ->
          (
(*
            let r : cr a = unquote tr in
            ddump (
              "e1 = " ^ exp_to_string e1 ^
              "; e2 = " ^ exp_to_string e2);
            ddump ("vm = " ^ term_to_string (quote vm));
            ddump ("before = " ^ term_to_string (norm_term [delta; primops]
              (quote (rdenote r vm e1 == rdenote r vm e2))));
            ddump ("expected after = " ^ term_to_string (norm_term [delta; primops]
              (quote (
                cdenote p r vm (exp_to_sum e1) ==
                cdenote p r vm (exp_to_sum e2)))));
*)
            // let q_app0 = quote (semiring_reflect #a #b p pc r vm e1 e2) in
            ddump (term_to_string t1);
            let tvm = CCM.quote_vm ta tb quotea (fun _ -> `()) vm in
            let te1 = quote_spolynomial e1 in
            // ddump (exp_to_string e1);
            // ddump (term_to_string te1);
            let te2 = quote_spolynomial e2 in
            // ddump (term_to_string te2);
            mapply (`(semiring_reflect #(`#ta) (`#tr) (`#tvm) (`#te1) (`#te2) (`#t1) (`#t2)));
            //unfold_def tp;
            canon_norm ();
            later ();
            canon_norm ();
            ddump ("after norm-left");
            trefl ();
            canon_norm ();
            ddump ("after norm-right");
            trefl ();
            (* ddump "done"; *)
            ()
          )
        | _ -> fail "Unexpected"
      )
      else fail "Found equality, but terms do not have the expected type"
    )
  | _ -> fail "Goal should be an equality")


let canon_semiring_with (#a:Type) (r:cr a) : Tac unit =
  canon_semiring_aux a
    (quote a) (unquote #a) (fun (x:a) -> quote x)
    (quote r) (quote (cm_op (r.cm_add))) (quote (cm_op (r.cm_mult))) (CM?.unit (r.cm_add)) (quote unit)

let canon_semiring (#a:Type) (r:cr a) : Tac unit =
  canon_semiring_with r


/// Examples

open FStar.Mul

#set-options "--no_smt"

let poly (a b c:int) =
  assert ( a * b + c + b * b == (b + a) * b + c)
  by (canon_semiring int_cr)

assume
val ring: eqtype

assume
val zero: ring

assume
val one: ring

assume
val ( +. ) : a:ring -> b:ring -> ring

assume
val ( *. ) : a:ring -> b:ring -> ring

assume
val add_identity: a:ring -> Lemma (zero +. a == a)

assume
val add_associativity: a:ring -> b:ring -> c:ring
  -> Lemma (a +. b +. c == a +. (b +. c))

assume
val add_commutativity: a:ring -> b:ring -> Lemma (a +. b == b +. a)

assume
val mul_identity: a:ring -> Lemma (one *. a == a)

assume
val mul_associativity: a:ring -> b:ring -> c:ring
  -> Lemma (a *. b *. c == a *. (b *. c))

assume
val mul_commutativity: a:ring -> b:ring -> Lemma (a *. b == b *. a)

[@canon_attr]
let ring_add_cm : cm ring =
  CM zero ( +. ) add_identity add_associativity add_commutativity

[@canon_attr]
let ring_mul_cm : cm ring =
  CM one ( *. ) mul_identity mul_associativity mul_commutativity

assume
val mul_add_distr: distribute_left_lemma ring ring_add_cm ring_mul_cm

[@canon_attr]
let ring_cr : cr ring = CR ring_add_cm ring_mul_cm mul_add_distr

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 1"

let poly_update_repeat_blocks_multi_lemma2_simplify (a b c w r d:ring) : Lemma
  ((((a *. (r *. r)) +. c) *. (r *. r)) +. ((b *. (r *. r)) +. d) *. r ==
   (((((a *. (r *. r)) +. b *. r) +. c) *. r) +. d) *. r)
=
  assert (
    (((a *. (r *. r)) +. c) *. (r *. r)) +. ((b *. (r *. r)) +. d) *. r ==
    ((a *. (r *. r) +. b *. r +. c) *. r +. d) *. r)
  by (canon_semiring ring_cr)
