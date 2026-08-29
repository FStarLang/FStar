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
module FStar.Real.Dedekind

/// The implementation of the Dedekind reals.
///
/// A real is (an erased) Dedekind cut of the rationals; every operation and
/// every law is inherited from the four construction modules
/// [FStar.Real.Dedekind.Base], [.Add], [.Mul] and [.Sup].  Nothing here is
/// assumed.

module Q = FStar.Rational
module G = FStar.Ghost
module B = FStar.Real.Dedekind.Base
module A = FStar.Real.Dedekind.Add
module M = FStar.Real.Dedekind.Mul
module S = FStar.Real.Dedekind.Sup

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(**** Representation *)

/// A real is an erased cut.  The erasure is what lets the (necessarily
/// classical, hence ghost) definitions of [mul] and [inv] be presented as
/// total functions.
let real = G.erased B.cut

let of_rat (r:Q.rat) : real = G.hide (B.rat_cut r)

(**** Order *)

let lt (x y:real) : prop = B.clt (G.reveal x) (G.reveal y)

/// [le], as defined in the interface, is exactly inclusion of cuts.
let le_cle (x y:real) : Lemma (le x y <==> B.cle (G.reveal x) (G.reveal y))
  = B.cle_refl (G.reveal x)

(**** Field operations *)

let add (x y:real) : real = G.hide (A.cadd (G.reveal x) (G.reveal y))
let opp (x:real) : real = G.hide (A.copp (G.reveal x))
let mul (x y:real) : real = G.hide (M.cmul (G.reveal x) (G.reveal y))
let inv (x:real) : real = G.hide (M.cinvt (G.reveal x))

(**** Abelian group under addition *)

let zero_cut () : Lemma (G.reveal zero == A.czero) = ()
let one_cut  () : Lemma (G.reveal one == M.cone) = ()

let add_comm (x y:real) : Lemma (add x y == add y x)
  = A.cadd_comm (G.reveal x) (G.reveal y)

let add_assoc (x y z:real) : Lemma (add (add x y) z == add x (add y z))
  = A.cadd_assoc (G.reveal x) (G.reveal y) (G.reveal z)

let add_zero (x:real) : Lemma (add x zero == x)
  = A.cadd_zero (G.reveal x)

let add_opp (x:real) : Lemma (add x (opp x) == zero)
  = A.cadd_opp (G.reveal x)

(**** Commutative monoid under multiplication, and a field *)

let mul_comm (x y:real) : Lemma (mul x y == mul y x)
  = M.cmul_comm (G.reveal x) (G.reveal y)

let mul_assoc (x y z:real) : Lemma (mul (mul x y) z == mul x (mul y z))
  = M.cmul_assoc (G.reveal x) (G.reveal y) (G.reveal z)

let mul_one (x:real) : Lemma (mul x one == x)
  = M.cmul_one (G.reveal x)

let mul_zero (x:real) : Lemma (mul x zero == zero)
  = M.cmul_zero (G.reveal x)

let distrib (x y z:real)
  : Lemma (mul x (add y z) == add (mul x y) (mul x z))
  = M.cmul_distrib (G.reveal x) (G.reveal y) (G.reveal z)

let mul_inv (x:real)
  : Lemma (requires x =!= zero) (ensures mul x (inv x) == one)
  = M.cmul_invt (G.reveal x)

(**** Total order, compatible with the field structure *)

let lt_irrefl (x:real) : Lemma (~(lt x x)) = B.clt_irrefl (G.reveal x)

let lt_trans (x y z:real)
  : Lemma (requires lt x y /\ lt y z) (ensures lt x z)
  = B.clt_trans (G.reveal x) (G.reveal y) (G.reveal z)

let lt_total (x y:real) : Lemma (lt x y \/ x == y \/ lt y x)
  = B.clt_total (G.reveal x) (G.reveal y)

let lt_add_r (x y z:real) : Lemma (lt (add x z) (add y z) <==> lt x y)
  = A.cadd_mono_rev (G.reveal x) (G.reveal y) (G.reveal z)

let lt_mul_pos (x y z:real)
  : Lemma (requires lt zero z) (ensures lt (mul x z) (mul y z) <==> lt x y)
  = M.cmul_mono (G.reveal x) (G.reveal y) (G.reveal z)

(**** The embedding is a morphism of ordered fields *)

let of_rat_add (p q:Q.rat)
  : Lemma (of_rat (Q.add p q) == add (of_rat p) (of_rat q))
  = A.rat_add p q

let of_rat_mul (p q:Q.rat)
  : Lemma (of_rat (Q.mul p q) == mul (of_rat p) (of_rat q))
  = M.rat_mul p q

let of_rat_opp (p:Q.rat) : Lemma (of_rat (Q.neg p) == opp (of_rat p))
  = A.rat_opp p

let of_rat_lt (p q:Q.rat) : Lemma (lt (of_rat p) (of_rat q) <==> Q.lt p q)
  = B.rat_cut_lt p q

let of_rat_inj (p q:Q.rat) : Lemma (of_rat p == of_rat q <==> p == q)
  = B.rat_cut_inj p q

(**** Archimedes *)

let archimedean (x:real) : Lemma (exists (n:nat). lt x (of_int n))
  = let b = B.cut_nonmem (G.reveal x) in
    Q.archimedean b;
    eliminate exists (n:nat). Q.lt b (Q.of_int n)
    with begin
      B.rat_cut_mem (Q.of_int n) b;
      B.clt_of_witness (G.reveal x) (B.rat_cut (Q.of_int n)) b;
      introduce exists (n:nat). lt x (of_int n) with n and ()
    end

(**** Completeness *)

/// A set of reals, seen as a set of cuts.
let cset_of (s:rset) : S.cset = fun (c:B.cut) -> s (G.hide c)

let cset_nonempty (s:rset)
  : Lemma (requires nonempty s) (ensures S.cnonempty (cset_of s))
  = eliminate exists (x:real). s x
    with introduce exists (c:B.cut). cset_of s c with (G.reveal x) and ()

let cset_upper (s:rset) (b:real)
  : Lemma (requires upper_bound s b)
          (ensures  S.cupper (cset_of s) (G.reveal b))
  = introduce forall (c:B.cut). cset_of s c ==> B.cle c (G.reveal b)
    with introduce cset_of s c ==> B.cle c (G.reveal b)
    with le_cle (G.hide c) b

let cset_bounded (s:rset)
  : Lemma (requires bounded_above s) (ensures S.cbounded (cset_of s))
  = eliminate exists (b:real). upper_bound s b
    with begin
      cset_upper s b;
      introduce exists (c:B.cut). S.cupper (cset_of s) c
      with (G.reveal b) and ()
    end

let lub (s:rset)
  : Ghost real
      (requires nonempty s /\ bounded_above s)
      (ensures  fun b -> is_lub s b)
  = cset_nonempty s;
    cset_bounded s;
    let c = S.csup (cset_of s) in
    let b : real = G.hide c in
    S.csup_upper (cset_of s);
    introduce forall (x:real). s x ==> le x b
    with introduce s x ==> le x b
    with (le_cle x b; assert (cset_of s (G.reveal x)));
    introduce forall (d:real). upper_bound s d ==> le b d
    with introduce upper_bound s d ==> le b d
    with begin
      cset_upper s d;
      S.csup_least (cset_of s) (G.reveal d);
      le_cle b d
    end;
    b
