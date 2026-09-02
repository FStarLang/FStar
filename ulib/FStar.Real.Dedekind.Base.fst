(*
   Copyright 2008-2026 Microsoft Research

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
module FStar.Real.Dedekind.Base

/// Dedekind cuts of the rationals: the representation underlying
/// [FStar.Real.Dedekind].
///
/// A real number is identified with the set of rationals strictly below it.
/// Such a set is a *cut*: nonempty, not everything, downward closed, and
/// without a greatest element.
///
/// Because a cut is a *restricted* predicate on [Q.rat] (see
/// [FStar.FunctionalExtensionality]), two cuts with the same members are equal
/// for F*'s propositional equality [==]. This uses functional and
/// propositional extensionality, two standard logical axioms already present
/// in F*'s library; classical reasoning uses [FStar.IndefiniteDescription].
/// No property of the real numbers is assumed anywhere in this development.
///
/// Note on proof engineering: [is_cut] is marked [opaque_to_smt]. Its
/// "no greatest element" clause is a `forall a. c a ==> exists b. c b /\ a < b`,
/// which, left visible, makes Z3 loop (each witness produced by the
/// existential re-triggers the quantifier: we measured a 30x slowdown on the
/// simplest lemmas). Access to the four clauses is therefore mediated by the
/// four accessors below.

module Q = FStar.Rational
module F = FStar.FunctionalExtensionality
module PE = FStar.PredicateExtensionality
module ID = FStar.IndefiniteDescription

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(**** Sets of rationals *)

let qset = F.restricted_t Q.rat (fun _ -> prop)

#push-options "--using_facts_from '*'"
let mk (p:Q.rat -> prop) : qset = F.on_dom Q.rat p

let mk_mem (p:Q.rat -> prop) (q:Q.rat)
  : Lemma (mk p q <==> p q)
  = ()

/// Extensionality of sets of rationals: the one place where functional and
/// propositional extensionality are used.
let qset_ext (x y:qset)
  : Lemma (requires forall (q:Q.rat). x q <==> y q) (ensures x == y)
  = PE.predicateExtensionality Q.rat x y;
    assert (F.on_domain Q.rat x == x);
    assert (F.on_domain Q.rat y == y)
#pop-options

(**** Cuts *)

/// The "no greatest element" clause, packaged as an opaque predicate.
///
/// Kept opaque for the reason described at the top of the file, and *also*
/// because the expected postcondition of a definition is pushed into its body:
/// were this clause the transparent conclusion of a lemma, that lemma would be
/// proved with the clause itself in scope, and every witness the existential
/// produces would re-trigger the quantifier. The only way to establish it is
/// [no_greatest_intro], which introduces the [forall] by [Classical.forall_intro]
/// -- so the body's type *is* the postcondition and no SMT goal is raised --
/// and does so with [p] abstract, where the quantifier has nothing to chain on.
[@@"opaque_to_smt"]
let no_greatest (p:Q.rat -> prop) : prop =
  forall (a:Q.rat). p a ==> (exists (b:Q.rat). p b /\ Q.lt a b)

let no_greatest_intro (p:Q.rat -> prop)
    (f: (a:Q.rat -> Lemma (requires p a)
                         (ensures exists (b:Q.rat). p b /\ Q.lt a b)))
  : Lemma (no_greatest p)
  = reveal_opaque (`%no_greatest) no_greatest;
    FStar.Classical.forall_intro
      #Q.rat
      #(fun (a:Q.rat) -> p a ==> (exists (b:Q.rat). p b /\ Q.lt a b))
      (FStar.Classical.move_requires
         #Q.rat
         #(fun (a:Q.rat) -> p a)
         #(fun (a:Q.rat) -> exists (b:Q.rat). p b /\ Q.lt a b)
         f)

[@@"opaque_to_smt"]
let is_cut (c:qset) : prop =
  (exists (q:Q.rat). c q) /\
  (exists (q:Q.rat). ~(c q)) /\
  (forall (a b:Q.rat). (c b /\ Q.lt a b) ==> c a) /\
  no_greatest c

let cut = c:qset{is_cut c}

let ext (x y:cut)
  : Lemma (requires forall (q:Q.rat). x q <==> y q) (ensures x == y)
  = qset_ext x y

/// To build a cut it suffices to check the four conditions pointwise.
let mk_cut (p:Q.rat -> prop)
  : Pure cut
      (requires (exists (q:Q.rat). p q) /\
                (exists (q:Q.rat). ~(p q)) /\
                (forall (a b:Q.rat). (p b /\ Q.lt a b) ==> p a) /\
                no_greatest p)
      (ensures fun c -> forall (q:Q.rat). c q <==> p q)
  = reveal_opaque (`%is_cut) is_cut;
    reveal_opaque (`%no_greatest) no_greatest;
    mk p

(**** The four accessors *)

/// A cut is nonempty.
let cut_mem (c:cut) : Ghost Q.rat (requires True) (ensures fun q -> c q)
  = reveal_opaque (`%is_cut) is_cut;
    ID.indefinite_description_ghost Q.rat (fun q -> c q)

/// A cut is not everything.
let cut_nonmem (c:cut) : Ghost Q.rat (requires True) (ensures fun q -> ~(c q))
  = reveal_opaque (`%is_cut) is_cut;
    ID.indefinite_description_ghost Q.rat (fun q -> ~(c q))

/// A cut is downward closed.
let cut_down (c:cut) (a b:Q.rat)
  : Lemma (requires c b /\ Q.lt a b) (ensures c a)
  = reveal_opaque (`%is_cut) is_cut

/// A cut has no greatest element.
let cut_above (c:cut) (a:Q.rat)
  : Ghost Q.rat (requires c a) (ensures fun b -> c b /\ Q.lt a b)
  = reveal_opaque (`%is_cut) is_cut;
    reveal_opaque (`%no_greatest) no_greatest;
    ID.indefinite_description_ghost Q.rat (fun b -> c b /\ Q.lt a b)

(**** Elementary consequences *)

/// A non-member dominates every member.
let mem_lt_nonmem (c:cut) (a b:Q.rat)
  : Lemma (requires c a /\ ~(c b)) (ensures Q.lt a b)
  = Q.lt_total a b;
    if Q.lt b a then cut_down c b a

/// Anything above a non-member is a non-member.
let above_nonmem (c:cut) (a b:Q.rat)
  : Lemma (requires ~(c a) /\ Q.lt a b) (ensures ~(c b))
  = introduce c b ==> False with cut_down c a b

(**** Order *)

let cle (x y:cut) : prop = forall (q:Q.rat). x q ==> y q
let clt (x y:cut) : prop = cle x y /\ x =!= y

let cle_refl (x:cut) : Lemma (cle x x) = ()

let cle_antisym (x y:cut)
  : Lemma (requires cle x y /\ cle y x) (ensures x == y)
  = ext x y

let cle_trans (x y z:cut)
  : Lemma (requires cle x y /\ cle y z) (ensures cle x z)
  = ()

let clt_irrefl (x:cut) : Lemma (~(clt x x)) = ()

let clt_trans (x y z:cut)
  : Lemma (requires clt x y /\ clt y z) (ensures clt x z)
  = cle_trans x y z;
    introduce x == z ==> False with cle_antisym y z

/// Totality of the order. This is where downward closure pays off.
let cle_total (x y:cut)
  : Lemma (cle x y \/ cle y x)
  = if ID.strong_excluded_middle (cle x y) then ()
    else begin
      eliminate exists (q:Q.rat). x q /\ ~(y q)
      with begin
        introduce forall (p:Q.rat). y p ==> x p
        with introduce _ ==> _
        with begin
          mem_lt_nonmem y p q;
          cut_down x p q
        end
      end
    end

let clt_total (x y:cut)
  : Lemma (clt x y \/ x == y \/ clt y x)
  = cle_total x y

let clt_of_witness (x y:cut) (q:Q.rat)
  : Lemma (requires y q /\ ~(x q)) (ensures clt x y)
  = cle_total x y

let clt_exists (x y:cut)
  : Lemma (requires clt x y) (ensures exists (q:Q.rat). y q /\ ~(x q))
  = if ID.strong_excluded_middle (exists (q:Q.rat). y q /\ ~(x q))
    then ()
    else cle_antisym x y

/// [x < y] is witnessed by a rational in [y] but not in [x].
let clt_witness (x y:cut)
  : Ghost Q.rat (requires clt x y) (ensures fun q -> y q /\ ~(x q))
  = clt_exists x y;
    ID.indefinite_description_ghost Q.rat (fun q -> y q /\ ~(x q))

(**** The rationals inside the reals *)

/// The four cut conditions for [{q | q < r}], each established separately.
/// Proving them in a single goal, or naming the predicate with a local
/// [let p : Q.rat -> prop = ...], is dramatically slower.

let rat_ne (r:Q.rat) : Lemma (exists (q:Q.rat). Q.lt q r)
  = introduce exists (q:Q.rat). Q.lt q r with (Q.below r) and ()

let rat_nf (r:Q.rat) : Lemma (exists (q:Q.rat). ~(Q.lt q r))
  = Q.lt_irrefl r;
    introduce exists (q:Q.rat). ~(Q.lt q r) with r and ()

let rat_dc (r:Q.rat)
  : Lemma (forall (a b:Q.rat). (Q.lt b r /\ Q.lt a b) ==> Q.lt a r)
  = introduce forall (a b:Q.rat). (Q.lt b r /\ Q.lt a b) ==> Q.lt a r
    with introduce _ ==> _ with Q.lt_trans a b r

/// The "no greatest element" clause, for one [a].
let rat_op_aux (a r:Q.rat)
  : Lemma (requires Q.lt a r)
          (ensures exists (b:Q.rat). Q.lt b r /\ Q.lt a b)
  = introduce exists (b:Q.rat). Q.lt b r /\ Q.lt a b
    with (Q.mid a r) and (Q.mid_spec a r)

let rat_op (r:Q.rat) : Lemma (no_greatest (fun q -> b2t (Q.lt q r)))
  = no_greatest_intro (fun q -> b2t (Q.lt q r)) (fun a -> rat_op_aux a r)

let rat_cut (r:Q.rat) : cut =
  rat_ne r; rat_nf r; rat_dc r; rat_op r;
  mk_cut (fun q -> b2t (Q.lt q r))

let rat_cut_mem (r q:Q.rat)
  : Lemma (rat_cut r q <==> Q.lt q r)
  = ()

let rat_cut_inj (r s:Q.rat)
  : Lemma (rat_cut r == rat_cut s <==> r == s)
  = introduce rat_cut r == rat_cut s ==> r == s
    with begin
      Q.lt_irrefl r;
      Q.lt_irrefl s;
      rat_cut_mem r r;
      rat_cut_mem s r;
      rat_cut_mem r s;
      rat_cut_mem s s;
      assert (rat_cut r r == rat_cut s r);
      assert (rat_cut r s == rat_cut s s);
      Q.lt_total r s
    end

let rat_cut_le (r s:Q.rat)
  : Lemma (requires Q.lt r s) (ensures cle (rat_cut r) (rat_cut s))
  = introduce forall (q:Q.rat). rat_cut r q ==> rat_cut s q
    with introduce _ ==> _ with Q.lt_trans q r s

let rat_cut_lt (r s:Q.rat)
  : Lemma (clt (rat_cut r) (rat_cut s) <==> Q.lt r s)
  = rat_cut_inj r s;
    Q.lt_irrefl r;
    Q.lt_irrefl s;
    introduce Q.lt r s ==> clt (rat_cut r) (rat_cut s)
    with rat_cut_le r s;
    introduce clt (rat_cut r) (rat_cut s) ==> Q.lt r s
    with begin
      Q.lt_total r s;
      introduce Q.lt s r ==> Q.lt r s
      with begin
        rat_cut_le s r;
        cle_antisym (rat_cut r) (rat_cut s)
      end
    end

(**** Approximating a cut by a rational interval *)

/// [addn a eps n] is [a + n * eps], defined by iteration so that the
/// search below is structurally recursive.
let rec addn (a eps:Q.rat) (n:nat) : Tot Q.rat (decreases n) =
  if n = 0 then a else addn (Q.add a eps) eps (n - 1)

let ac1 (x y z:Q.rat) : Lemma (Q.add (Q.add x y) z == Q.add x (Q.add z y))
  = Q.add_assoc x y z; Q.add_comm y z

let scale_succ (m:nat) (eps:Q.rat)
  : Lemma (Q.mul (Q.of_int (m + 1)) eps ==
           Q.add (Q.mul (Q.of_int m) eps) eps)
  = Q.of_int_add m 1;
    Q.mul_comm (Q.add (Q.of_int m) Q.one) eps;
    Q.distrib eps (Q.of_int m) Q.one;
    Q.mul_comm eps (Q.of_int m);
    Q.mul_comm eps Q.one;
    Q.mul_one eps

let scale_zero (eps:Q.rat) : Lemma (Q.mul (Q.of_int 0) eps == Q.zero)
  = Q.mul_comm (Q.of_int 0) eps; Q.mul_zero eps

#push-options "--fuel 1"
let rec addn_spec (a eps:Q.rat) (n:nat)
  : Lemma (ensures addn a eps n == Q.add a (Q.mul (Q.of_int n) eps))
          (decreases n)
  = if n = 0 then (scale_zero eps; Q.add_zero a)
    else begin
      addn_spec (Q.add a eps) eps (n - 1);
      scale_succ (n - 1) eps;
      ac1 a eps (Q.mul (Q.of_int (n - 1)) eps)
    end

#pop-options

/// [a + n * eps] eventually exceeds any given rational.
let addn_unbounded (a eps b:Q.rat)
  : Lemma (requires Q.lt Q.zero eps)
          (ensures exists (n:nat). Q.lt b (addn a eps n))
  = let d = Q.sub b a in
    Q.inv_pos eps;
    Q.archimedean (Q.mul d (Q.inv eps));
    eliminate exists (n:nat). Q.lt (Q.mul d (Q.inv eps)) (Q.of_int n)
    with begin
      Q.lt_mul_pos (Q.mul d (Q.inv eps)) (Q.of_int n) eps;
      Q.mul_assoc d (Q.inv eps) eps;
      Q.mul_comm (Q.inv eps) eps;
      Q.lt_irrefl Q.zero;
      Q.inv_num_den eps;
      Q.mul_one d;
      Q.lt_add_r d (Q.mul (Q.of_int n) eps) a;
      Q.add_comm d a;
      Q.add_assoc a b (Q.neg a);
      Q.add_comm b (Q.neg a);
      Q.add_assoc a (Q.neg a) b;
      Q.add_neg a;
      Q.add_comm Q.zero b;
      Q.add_zero b;
      Q.add_comm (Q.mul (Q.of_int n) eps) a;
      addn_spec a eps n;
      introduce exists (n:nat). Q.lt b (addn a eps n) with n and ()
    end

/// The search: walking up from a member in steps of [eps], we must leave the
/// cut, and the step at which we do gives the desired pair.
#push-options "--fuel 1"
let rec approx_aux (c:cut) (a eps:Q.rat) (n:nat)
  : Ghost (Q.rat & Q.rat)
      (requires Q.lt Q.zero eps /\ c a /\ ~(c (addn a eps n)))
      (ensures fun (x, y) -> c x /\ ~(c y) /\ y == Q.add x eps)
      (decreases n)
  = if n = 0 then (a, Q.add a eps)
    else if ID.strong_excluded_middle (c (Q.add a eps))
    then approx_aux c (Q.add a eps) eps (n - 1)
    else (a, Q.add a eps)

#pop-options

/// **Approximation lemma.** However fine a rational tolerance [eps] we are
/// given, a cut is straddled by two rationals exactly [eps] apart: one inside
/// and one outside. This is what makes [add_opp] and multiplication of cuts
/// provable.
let approx (c:cut) (eps:Q.rat)
  : Ghost (Q.rat & Q.rat)
      (requires Q.lt Q.zero eps)
      (ensures fun (x, y) -> c x /\ ~(c y) /\ y == Q.add x eps)
  = let a = cut_mem c in
    let b = cut_nonmem c in
    addn_unbounded a eps b;
    let n = ID.indefinite_description_ghost nat (fun n -> Q.lt b (addn a eps n)) in
    above_nonmem c b (addn a eps n);
    approx_aux c a eps n
