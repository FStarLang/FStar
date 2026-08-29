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
module FStar.Real.Dedekind.Mul

/// Multiplication and inversion of Dedekind cuts.

module Q = FStar.Rational
module B = FStar.Real.Dedekind.Base
module A = FStar.Real.Dedekind.Add
module ID = FStar.IndefiniteDescription

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(**** Rational helpers *)

let qzero_lt_one () : Lemma (Q.lt Q.zero Q.one) = Q.of_int_lt 0 1

let qzero_lt_two () : Lemma (Q.lt Q.zero Q.two) = Q.of_int_lt 0 2

let qtwo_ne_zero () : Lemma (Q.two =!= Q.zero) = Q.of_int_inj 2 0

let qmul_lt2 (a a' b b':Q.rat)
  : Lemma (requires Q.lt Q.zero a /\ Q.lt a a' /\ Q.lt Q.zero b /\ Q.lt b b')
          (ensures  Q.lt (Q.mul a b) (Q.mul a' b'))
  = Q.lt_mul_pos a a' b;
    Q.lt_trans Q.zero a a';
    Q.lt_mul_pos b b' a';
    Q.mul_comm b a'; Q.mul_comm b' a';
    Q.lt_trans (Q.mul a b) (Q.mul a' b) (Q.mul a' b')

let qmul_le_l (a a' b:Q.rat)
  : Lemma (requires Q.lt Q.zero b /\ Q.le a a')
          (ensures  Q.le (Q.mul a b) (Q.mul a' b))
  = Q.lt_mul_pos a a' b

let qhalf (e:Q.rat) : Q.rat = Q.mul e (Q.inv Q.two)

let qhalf_sum (e:Q.rat) : Lemma (Q.add (qhalf e) (qhalf e) == e)
  = qtwo_ne_zero ();
    Q.of_int_add 1 1;
    Q.distrib (Q.inv Q.two) Q.one Q.one;
    Q.mul_one (Q.inv Q.two);
    Q.mul_comm (Q.inv Q.two) Q.two;
    Q.inv_num_den Q.two;
    Q.distrib e (Q.inv Q.two) (Q.inv Q.two);
    Q.mul_one e

let qhalf_pos (e:Q.rat)
  : Lemma (requires Q.lt Q.zero e) (ensures Q.lt Q.zero (qhalf e))
  = qzero_lt_two (); Q.inv_pos Q.two; Q.mul_pos e (Q.inv Q.two)

let qmul_div (q d:Q.rat)
  : Lemma (requires d =!= Q.zero) (ensures Q.mul (Q.div q d) d == q)
  = Q.mul_assoc q (Q.inv d) d;
    Q.mul_comm (Q.inv d) d;
    Q.inv_num_den d;
    Q.mul_one q

let qlt_div (q c d:Q.rat)
  : Lemma (requires Q.lt Q.zero d)
          (ensures  Q.lt q (Q.mul c d) <==> Q.lt (Q.div q d) c)
  = Q.lt_irrefl Q.zero;
    qmul_div q d;
    Q.lt_mul_pos (Q.div q d) c d

(**** Multiplication of cuts, positive part *)

/// [mulp x y] is the set of rationals below some product [a*b] with [a] a
/// positive member of [x] and [b] a positive member of [y], together with all
/// the negative rationals.  It is a cut for *any* pair of cuts, and it is the
/// product exactly when both arguments are nonnegative.
let mulp (x y:B.cut) (q:Q.rat) : prop =
  Q.lt q Q.zero \/
  (exists (a b:Q.rat).
      x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\ Q.lt q (Q.mul a b))

let mul_ne (x y:B.cut) : Lemma (exists (q:Q.rat). mulp x y q)
  = introduce exists (q:Q.rat). mulp x y q with (Q.below Q.zero) and ()

/// A positive rational strictly above every positive member of [c].
let bnd (c:B.cut)
  : Ghost Q.rat
      (requires True)
      (ensures fun m -> Q.lt Q.zero m /\
                     (forall (a:Q.rat). (c a /\ Q.lt Q.zero a) ==> Q.lt a m))
  = let a' = B.cut_nonmem c in
    qzero_lt_one ();
    if Q.lt a' Q.one
    then begin
      introduce forall (a:Q.rat). (c a /\ Q.lt Q.zero a) ==> Q.lt a Q.one
      with introduce _ ==> _
      with (B.mem_lt_nonmem c a a'; Q.lt_trans a a' Q.one);
      Q.one
    end
    else begin
      introduce forall (a:Q.rat). (c a /\ Q.lt Q.zero a) ==> Q.lt a a'
      with introduce _ ==> _ with B.mem_lt_nonmem c a a';
      Q.lt_total a' Q.one;
      introduce Q.lt Q.one a' ==> Q.lt Q.zero a'
      with Q.lt_trans Q.zero Q.one a';
      a'
    end

let mul_nf (x y:B.cut) : Lemma (exists (q:Q.rat). ~(mulp x y q))
  = let mx = bnd x in
    let my = bnd y in
    let m = Q.mul mx my in
    Q.mul_pos mx my;
    Q.lt_asym Q.zero m;
    introduce mulp x y m ==> False
    with eliminate exists (a b:Q.rat).
           x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\ Q.lt m (Q.mul a b)
    with begin
      qmul_lt2 a mx b my;
      Q.lt_asym m (Q.mul a b)
    end;
    introduce exists (q:Q.rat). ~(mulp x y q) with m and ()

let mul_dc (x y:B.cut)
  : Lemma (forall (u v:Q.rat). (mulp x y v /\ Q.lt u v) ==> mulp x y u)
  = introduce forall (u v:Q.rat). (mulp x y v /\ Q.lt u v) ==> mulp x y u
    with introduce (mulp x y v /\ Q.lt u v) ==> mulp x y u
    with begin
      introduce Q.lt v Q.zero ==> mulp x y u
      with Q.lt_trans u v Q.zero;
      introduce (exists (a b:Q.rat).
                   x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
                   Q.lt v (Q.mul a b)) ==> mulp x y u
      with eliminate exists (a b:Q.rat).
             x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\ Q.lt v (Q.mul a b)
      with begin
        Q.lt_trans u v (Q.mul a b);
        introduce exists (a2 b2:Q.rat).
            x a2 /\ y b2 /\ Q.lt Q.zero a2 /\ Q.lt Q.zero b2 /\
            Q.lt u (Q.mul a2 b2)
        with a b and ()
      end
    end

let mul_op (x y:B.cut)
  : Lemma (forall (u:Q.rat). mulp x y u ==>
                        (exists (v:Q.rat). mulp x y v /\ Q.lt u v))
  = introduce forall (u:Q.rat). mulp x y u ==>
                           (exists (v:Q.rat). mulp x y v /\ Q.lt u v)
    with introduce mulp x y u ==> (exists (v:Q.rat). mulp x y v /\ Q.lt u v)
    with begin
      introduce Q.lt u Q.zero ==> (exists (v:Q.rat). mulp x y v /\ Q.lt u v)
      with begin
        Q.mid_spec u Q.zero;
        introduce exists (v:Q.rat). mulp x y v /\ Q.lt u v
        with (Q.mid u Q.zero) and ()
      end;
      introduce (exists (a b:Q.rat).
                   x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
                   Q.lt u (Q.mul a b)) ==>
                (exists (v:Q.rat). mulp x y v /\ Q.lt u v)
      with eliminate exists (a b:Q.rat).
             x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\ Q.lt u (Q.mul a b)
      with begin
        Q.mid_spec u (Q.mul a b);
        introduce exists (a2 b2:Q.rat).
            x a2 /\ y b2 /\ Q.lt Q.zero a2 /\ Q.lt Q.zero b2 /\
            Q.lt (Q.mid u (Q.mul a b)) (Q.mul a2 b2)
        with a b and ();
        introduce exists (v:Q.rat). mulp x y v /\ Q.lt u v
        with (Q.mid u (Q.mul a b)) and ()
      end
    end

let cpmul (x y:B.cut) : c:B.cut{forall (q:Q.rat). c q <==> mulp x y q} =
  mul_ne x y; mul_nf x y; mul_dc x y; mul_op x y;
  B.mk_cut (mulp x y)

(**** The nonnegative cone *)

let czero_mem (q:Q.rat) : Lemma (A.czero q <==> Q.lt q Q.zero)
  = B.rat_cut_mem Q.zero q

let cone : B.cut = B.rat_cut Q.one

let cone_mem (q:Q.rat) : Lemma (cone q <==> Q.lt q Q.one)
  = B.rat_cut_mem Q.one q

let nonneg (x:B.cut) : prop = B.cle A.czero x

let nonneg_neg (x:B.cut) (q:Q.rat)
  : Lemma (requires nonneg x /\ Q.lt q Q.zero) (ensures x q)
  = czero_mem q

let cpmul_nonneg (x y:B.cut) : Lemma (nonneg (cpmul x y))
  = introduce forall (q:Q.rat). A.czero q ==> cpmul x y q
    with introduce A.czero q ==> cpmul x y q
    with czero_mem q

(**** Commutativity *)

let cpmul_comm_le (x y:B.cut) : Lemma (B.cle (cpmul x y) (cpmul y x))
  = introduce forall (q:Q.rat). cpmul x y q ==> cpmul y x q
    with introduce cpmul x y q ==> cpmul y x q
    with introduce (exists (a b:Q.rat).
                      x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
                      Q.lt q (Q.mul a b)) ==> cpmul y x q
         with eliminate exists (a b:Q.rat).
                x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
                Q.lt q (Q.mul a b)
         with begin
           Q.mul_comm a b;
           introduce exists (a2 b2:Q.rat).
               y a2 /\ x b2 /\ Q.lt Q.zero a2 /\ Q.lt Q.zero b2 /\
               Q.lt q (Q.mul a2 b2)
           with b a and ()
         end

let cpmul_comm (x y:B.cut) : Lemma (cpmul x y == cpmul y x)
  = cpmul_comm_le x y;
    cpmul_comm_le y x;
    B.cle_antisym (cpmul x y) (cpmul y x)

(**** Monotonicity *)

let cpmul_mono2 (x y z:B.cut)
  : Lemma (requires B.cle y z) (ensures B.cle (cpmul x y) (cpmul x z))
  = introduce forall (q:Q.rat). cpmul x y q ==> cpmul x z q
    with introduce cpmul x y q ==> cpmul x z q
    with introduce (exists (a b:Q.rat).
                      x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
                      Q.lt q (Q.mul a b)) ==> cpmul x z q
         with eliminate exists (a b:Q.rat).
                x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
                Q.lt q (Q.mul a b)
         with introduce exists (a2 b2:Q.rat).
                  x a2 /\ z b2 /\ Q.lt Q.zero a2 /\ Q.lt Q.zero b2 /\
                  Q.lt q (Q.mul a2 b2)
              with a b and ()

(**** Zero *)

let cpmul_zero (x:B.cut) : Lemma (cpmul x A.czero == A.czero)
  = introduce forall (q:Q.rat). cpmul x A.czero q <==> A.czero q
    with begin
      czero_mem q;
      introduce (exists (a b:Q.rat).
                   x a /\ A.czero b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
                   Q.lt q (Q.mul a b)) ==> Q.lt q Q.zero
      with eliminate exists (a b:Q.rat).
             x a /\ A.czero b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
             Q.lt q (Q.mul a b)
      with (czero_mem b; Q.lt_asym Q.zero b)
    end;
    B.ext (cpmul x A.czero) A.czero

(**** Unit *)

let qdiv_nonneg (a d:Q.rat)
  : Lemma (requires Q.le Q.zero a /\ Q.lt Q.zero d)
          (ensures  Q.le Q.zero (Q.div a d))
  = Q.inv_pos d;
    introduce Q.lt Q.zero a ==> Q.lt Q.zero (Q.div a d)
    with Q.mul_pos a (Q.inv d);
    Q.mul_comm Q.zero (Q.inv d);
    Q.mul_zero (Q.inv d)

let cpmul_one_le (x:B.cut)
  : Lemma (requires nonneg x) (ensures B.cle (cpmul x cone) x)
  = introduce forall (q:Q.rat). cpmul x cone q ==> x q
    with introduce cpmul x cone q ==> x q
    with begin
      introduce Q.lt q Q.zero ==> x q with nonneg_neg x q;
      introduce (exists (a b:Q.rat).
                   x a /\ cone b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
                   Q.lt q (Q.mul a b)) ==> x q
      with eliminate exists (a b:Q.rat).
             x a /\ cone b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
             Q.lt q (Q.mul a b)
      with begin
        cone_mem b;
        Q.lt_mul_pos b Q.one a;
        Q.mul_comm b a;
        Q.mul_comm Q.one a;
        Q.mul_one a;
        Q.lt_trans q (Q.mul a b) a;
        B.cut_down x q a
      end
    end

let cpmul_one_ge (x:B.cut)
  : Lemma (requires nonneg x) (ensures B.cle x (cpmul x cone))
  = introduce forall (a:Q.rat). x a ==> cpmul x cone a
    with introduce x a ==> cpmul x cone a
    with introduce ~(Q.lt a Q.zero) ==> cpmul x cone a
    with begin
      let a2 = B.cut_above x a in
      Q.lt_total a Q.zero;
      introduce Q.lt Q.zero a ==> Q.lt Q.zero a2
      with Q.lt_trans Q.zero a a2;
      let d = Q.div a a2 in
      qdiv_nonneg a a2;
      Q.mul_one a2;
      Q.mul_comm Q.one a2;
      qlt_div a Q.one a2;
      let b = Q.mid d Q.one in
      Q.mid_spec d Q.one;
      introduce Q.lt Q.zero d ==> Q.lt Q.zero b
      with Q.lt_trans Q.zero d b;
      cone_mem b;
      qlt_div a b a2;
      Q.mul_comm b a2;
      introduce exists (a3 b3:Q.rat).
          x a3 /\ cone b3 /\ Q.lt Q.zero a3 /\ Q.lt Q.zero b3 /\
          Q.lt a (Q.mul a3 b3)
      with a2 b and ()
    end

let cpmul_one (x:B.cut)
  : Lemma (requires nonneg x) (ensures cpmul x cone == x)
  = cpmul_one_le x; cpmul_one_ge x; B.cle_antisym (cpmul x cone) x

(**** More rational rearrangements *)

let qshuffle4 (p q r s:Q.rat)
  : Lemma (Q.add (Q.add p q) (Q.add r s) == Q.add (Q.add p r) (Q.add q s))
  = Q.add_assoc p q (Q.add r s);
    Q.add_assoc q r s; Q.add_comm q r; Q.add_assoc r q s;
    Q.add_assoc p r (Q.add q s)

let qsub_pos (u v:Q.rat)
  : Lemma (Q.lt Q.zero (Q.sub v u) <==> Q.lt u v)
  = Q.lt_add_r Q.zero (Q.sub v u) u;
    A.qadd_zero_l u;
    A.qsub_add v u

let qsub_neg (u v:Q.rat)
  : Lemma (Q.lt (Q.sub u v) Q.zero <==> Q.lt u v)
  = Q.lt_add_r (Q.sub u v) Q.zero v;
    A.qadd_zero_l v;
    A.qsub_add u v

let qsub_smaller (a e:Q.rat)
  : Lemma (requires Q.lt Q.zero e) (ensures Q.lt (Q.sub a e) a)
  = A.qneg_lt_zero' e;
    Q.lt_add_r (Q.neg e) Q.zero a;
    A.qadd_zero_l a;
    Q.add_comm (Q.neg e) a

let qsub2 (a b e:Q.rat)
  : Lemma (Q.add (Q.sub a e) (Q.sub b e) == Q.sub (Q.add a b) (Q.add e e))
  = qshuffle4 a (Q.neg e) b (Q.neg e);
    A.qneg_add e e

let qsub_sub (s q:Q.rat) : Lemma (Q.sub s (Q.sub s q) == q)
  = A.qneg_add s (Q.neg q);
    Q.neg_neg q;
    Q.add_assoc s (Q.neg s) q;
    Q.add_neg s;
    A.qadd_zero_l q

let qhalf_neg (q:Q.rat)
  : Lemma (requires Q.lt q Q.zero) (ensures Q.lt (qhalf q) Q.zero)
  = qzero_lt_two ();
    Q.inv_pos Q.two;
    Q.lt_mul_pos q Q.zero (Q.inv Q.two);
    Q.mul_comm Q.zero (Q.inv Q.two);
    Q.mul_zero (Q.inv Q.two)

let qlt_le_trans (p q r:Q.rat)
  : Lemma (requires Q.lt p q /\ Q.le q r) (ensures Q.lt p r)
  = introduce Q.lt q r ==> Q.lt p r with Q.lt_trans p q r

let qle_lt_trans (p q r:Q.rat)
  : Lemma (requires Q.le p q /\ Q.lt q r) (ensures Q.lt p r)
  = introduce Q.lt p q ==> Q.lt p r with Q.lt_trans p q r

let qadd_pos (u v:Q.rat)
  : Lemma (requires Q.lt Q.zero u /\ Q.lt Q.zero v)
          (ensures  Q.lt Q.zero (Q.add u v))
  = Q.lt_add_r Q.zero u v;
    A.qadd_zero_l v;
    Q.lt_trans Q.zero v (Q.add u v)

let qlt_add_neg (u v:Q.rat)
  : Lemma (requires Q.lt u Q.zero) (ensures Q.lt (Q.add u v) v)
  = Q.lt_add_r u Q.zero v;
    A.qadd_zero_l v

/// The larger of two positive members of a cut, still a member.
let qmax_in (c:B.cut) (a1 a2:Q.rat)
  : Ghost Q.rat
      (requires c a1 /\ c a2 /\ Q.lt Q.zero a1 /\ Q.lt Q.zero a2)
      (ensures fun a -> c a /\ Q.lt Q.zero a /\ Q.le a1 a /\ Q.le a2 a)
  = Q.lt_total a1 a2;
    if Q.lt a1 a2 then a2 else a1

let mulpos_rev (a b:Q.rat)
  : Lemma (requires Q.lt Q.zero a /\ Q.lt Q.zero (Q.mul a b))
          (ensures  Q.lt Q.zero b)
  = Q.lt_total b Q.zero;
    Q.lt_irrefl Q.zero;
    Q.mul_zero a;
    introduce Q.lt b Q.zero ==> Q.lt Q.zero b
    with begin
      Q.lt_mul_pos b Q.zero a;
      Q.mul_comm Q.zero a;
      Q.mul_zero a;
      Q.mul_comm b a;
      Q.lt_asym Q.zero (Q.mul a b)
    end

/// Membership in [cpmul] from a single pair of witnesses, with the positivity
/// of the second one deduced rather than assumed.
let mem1 (x y:B.cut) (a b u:Q.rat)
  : Lemma (requires x a /\ y b /\ Q.lt Q.zero a /\ Q.lt u (Q.mul a b))
          (ensures  cpmul x y u)
  = introduce ~(Q.lt u Q.zero) ==> cpmul x y u
    with begin
      Q.lt_total u Q.zero;
      introduce Q.lt Q.zero u ==> Q.lt Q.zero (Q.mul a b)
      with Q.lt_trans Q.zero u (Q.mul a b);
      assert (Q.lt Q.zero (Q.mul a b));
      mulpos_rev a b;
      introduce exists (a2 b2:Q.rat).
          x a2 /\ y b2 /\ Q.lt Q.zero a2 /\ Q.lt Q.zero b2 /\
          Q.lt u (Q.mul a2 b2)
      with a b and ()
    end

(**** Associativity on the cone *)

let cpmul_assoc_le (x y z:B.cut)
  : Lemma (B.cle (cpmul (cpmul x y) z) (cpmul x (cpmul y z)))
  = introduce forall (q:Q.rat).
        cpmul (cpmul x y) z q ==> cpmul x (cpmul y z) q
    with introduce cpmul (cpmul x y) z q ==> cpmul x (cpmul y z) q
    with introduce ~(Q.lt q Q.zero) ==> cpmul x (cpmul y z) q
    with eliminate exists (c d:Q.rat).
           (cpmul x y) c /\ z d /\ Q.lt Q.zero c /\ Q.lt Q.zero d /\
           Q.lt q (Q.mul c d)
    with begin
      Q.lt_asym Q.zero c;
      eliminate exists (a b:Q.rat).
        x a /\ y b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\ Q.lt c (Q.mul a b)
      with begin
        Q.lt_mul_pos c (Q.mul a b) d;
        Q.mul_assoc a b d;
        Q.lt_trans q (Q.mul c d) (Q.mul (Q.mul a b) d);
        Q.mul_comm (Q.mul b d) a;
        qlt_div q (Q.mul b d) a;
        Q.mul_pos b d;
        let e = Q.mid (Q.div q a) (Q.mul b d) in
        Q.mid_spec (Q.div q a) (Q.mul b d);
        Q.lt_total q Q.zero;
        qdiv_nonneg q a;
        introduce Q.lt Q.zero (Q.div q a) ==> Q.lt Q.zero e
        with Q.lt_trans Q.zero (Q.div q a) e;
        introduce exists (b2 c2:Q.rat).
            y b2 /\ z c2 /\ Q.lt Q.zero b2 /\ Q.lt Q.zero c2 /\
            Q.lt e (Q.mul b2 c2)
        with b d and ();
        qlt_div q e a;
        Q.mul_comm e a;
        introduce exists (a2 e2:Q.rat).
            x a2 /\ (cpmul y z) e2 /\ Q.lt Q.zero a2 /\ Q.lt Q.zero e2 /\
            Q.lt q (Q.mul a2 e2)
        with a e and ()
      end
    end

let cpmul_assoc (x y z:B.cut)
  : Lemma (cpmul (cpmul x y) z == cpmul x (cpmul y z))
  = cpmul_assoc_le x y z;
    cpmul_assoc_le z y x;
    cpmul_comm z y;
    cpmul_comm y x;
    cpmul_comm (cpmul y z) x;
    cpmul_comm z (cpmul x y);
    B.cle_antisym (cpmul (cpmul x y) z) (cpmul x (cpmul y z))

(**** Distributivity on the cone *)

let cadd_upper (y z:B.cut)
  : Lemma (requires nonneg y) (ensures B.cle z (A.cadd y z))
  = introduce forall (b:Q.rat). z b ==> A.cadd y z b
    with introduce z b ==> A.cadd y z b
    with begin
      let b' = B.cut_above z b in
      qsub_neg b b';
      nonneg_neg y (Q.sub b b');
      A.qsub_add b b';
      introduce exists (u v:Q.rat). y u /\ z v /\ b == Q.add u v
      with (Q.sub b b') b' and ()
    end

let cadd_upper_l (y z:B.cut)
  : Lemma (requires nonneg z) (ensures B.cle y (A.cadd y z))
  = cadd_upper z y; A.cadd_comm z y

let cpmul_distrib_le (x y z:B.cut)
  : Lemma (B.cle (cpmul x (A.cadd y z)) (A.cadd (cpmul x y) (cpmul x z)))
  = introduce forall (q:Q.rat).
        cpmul x (A.cadd y z) q ==> A.cadd (cpmul x y) (cpmul x z) q
    with introduce cpmul x (A.cadd y z) q ==>
                   A.cadd (cpmul x y) (cpmul x z) q
    with begin
      introduce Q.lt q Q.zero ==> A.cadd (cpmul x y) (cpmul x z) q
      with begin
        qhalf_sum q; qhalf_neg q;
        introduce exists (u v:Q.rat).
            (cpmul x y) u /\ (cpmul x z) v /\ q == Q.add u v
        with (qhalf q) (qhalf q) and ()
      end;
      introduce (exists (a c:Q.rat).
                   x a /\ (A.cadd y z) c /\ Q.lt Q.zero a /\ Q.lt Q.zero c /\
                   Q.lt q (Q.mul a c)) ==> A.cadd (cpmul x y) (cpmul x z) q
      with eliminate exists (a c:Q.rat).
             x a /\ (A.cadd y z) c /\ Q.lt Q.zero a /\ Q.lt Q.zero c /\
             Q.lt q (Q.mul a c)
      with eliminate exists (b1 b2:Q.rat). y b1 /\ z b2 /\ c == Q.add b1 b2
      with begin
        let s = Q.mul a c in
        Q.distrib a b1 b2;
        qsub_pos q s;
        let e = qhalf (Q.sub s q) in
        qhalf_pos (Q.sub s q);
        qhalf_sum (Q.sub s q);
        let q1 = Q.sub (Q.mul a b1) e in
        let q2 = Q.sub (Q.mul a b2) e in
        qsub2 (Q.mul a b1) (Q.mul a b2) e;
        qsub_sub s q;
        qsub_smaller (Q.mul a b1) e;
        qsub_smaller (Q.mul a b2) e;
        mem1 x y a b1 q1;
        mem1 x z a b2 q2;
        introduce exists (u v:Q.rat).
            (cpmul x y) u /\ (cpmul x z) v /\ q == Q.add u v
        with q1 q2 and ()
      end
    end

let cpmul_distrib_ge (x y z:B.cut)
  : Lemma (requires nonneg y /\ nonneg z)
          (ensures B.cle (A.cadd (cpmul x y) (cpmul x z)) (cpmul x (A.cadd y z)))
  = cadd_upper y z;
    cadd_upper_l y z;
    cpmul_mono2 x z (A.cadd y z);
    cpmul_mono2 x y (A.cadd y z);
    introduce forall (q:Q.rat).
        A.cadd (cpmul x y) (cpmul x z) q ==> cpmul x (A.cadd y z) q
    with introduce A.cadd (cpmul x y) (cpmul x z) q ==>
                   cpmul x (A.cadd y z) q
    with eliminate exists (q1 q2:Q.rat).
           (cpmul x y) q1 /\ (cpmul x z) q2 /\ q == Q.add q1 q2
    with begin
      introduce Q.lt q1 Q.zero ==> cpmul x (A.cadd y z) q
      with begin
        qlt_add_neg q1 q2;
        B.cut_down (cpmul x (A.cadd y z)) q q2
      end;
      introduce Q.lt q2 Q.zero ==> cpmul x (A.cadd y z) q
      with begin
        Q.add_comm q1 q2;
        qlt_add_neg q2 q1;
        B.cut_down (cpmul x (A.cadd y z)) q q1
      end;
      introduce (~(Q.lt q1 Q.zero) /\ ~(Q.lt q2 Q.zero)) ==>
                cpmul x (A.cadd y z) q
      with eliminate exists (a1 b1:Q.rat).
             x a1 /\ y b1 /\ Q.lt Q.zero a1 /\ Q.lt Q.zero b1 /\
             Q.lt q1 (Q.mul a1 b1)
      with eliminate exists (a2 b2:Q.rat).
             x a2 /\ z b2 /\ Q.lt Q.zero a2 /\ Q.lt Q.zero b2 /\
             Q.lt q2 (Q.mul a2 b2)
      with begin
        let a = qmax_in x a1 a2 in
        qmul_le_l a1 a b1;
        qmul_le_l a2 a b2;
        qlt_le_trans q1 (Q.mul a1 b1) (Q.mul a b1);
        qlt_le_trans q2 (Q.mul a2 b2) (Q.mul a b2);
        A.qlt_add2 q1 (Q.mul a b1) q2 (Q.mul a b2);
        Q.distrib a b1 b2;
        qadd_pos b1 b2;
        introduce exists (u v:Q.rat). y u /\ z v /\ Q.add b1 b2 == Q.add u v
        with b1 b2 and ();
        introduce exists (a3 c3:Q.rat).
            x a3 /\ (A.cadd y z) c3 /\ Q.lt Q.zero a3 /\ Q.lt Q.zero c3 /\
            Q.lt q (Q.mul a3 c3)
        with a (Q.add b1 b2) and ()
      end
    end

let cpmul_distrib (x y z:B.cut)
  : Lemma (requires nonneg y /\ nonneg z)
          (ensures cpmul x (A.cadd y z) == A.cadd (cpmul x y) (cpmul x z))
  = cpmul_distrib_le x y z;
    cpmul_distrib_ge x y z;
    B.cle_antisym (cpmul x (A.cadd y z)) (A.cadd (cpmul x y) (cpmul x z))

(**** Group facts about negation, needed for the sign analysis *)

#push-options "--z3rlimit 60"

let cadd_zero_l (x:B.cut) : Lemma (A.cadd A.czero x == x)
  = A.cadd_comm A.czero x; A.cadd_zero x

let cadd_opp_l (x:B.cut) : Lemma (A.cadd (A.copp x) x == A.czero)
  = A.cadd_comm (A.copp x) x; A.cadd_opp x

let cadd_cancel_fwd (x y z:B.cut)
  : Lemma (requires A.cadd x z == A.cadd y z) (ensures x == y)
  = A.cadd_assoc x z (A.copp z); A.cadd_assoc y z (A.copp z);
    A.cadd_opp z; A.cadd_zero x; A.cadd_zero y

let cadd_cancel (x y z:B.cut)
  : Lemma (A.cadd x z == A.cadd y z <==> x == y)
  = introduce A.cadd x z == A.cadd y z ==> x == y with cadd_cancel_fwd x y z

let copp_copp (x:B.cut) : Lemma (A.copp (A.copp x) == x)
  = A.cadd_opp (A.copp x);
    A.cadd_comm (A.copp x) (A.copp (A.copp x));
    A.cadd_opp x;
    cadd_cancel (A.copp (A.copp x)) x (A.copp x)

let copp_inj (x y:B.cut)
  : Lemma (requires A.copp x == A.copp y) (ensures x == y)
  = copp_copp x; copp_copp y

let copp_czero () : Lemma (A.copp A.czero == A.czero)
  = A.cadd_opp A.czero; cadd_zero_l (A.copp A.czero)

let cshuffle4 (a b c d:B.cut)
  : Lemma (A.cadd (A.cadd a b) (A.cadd c d) ==
           A.cadd (A.cadd a c) (A.cadd b d))
  = A.cadd_assoc a b (A.cadd c d);
    A.cadd_assoc b c d; A.cadd_comm b c; A.cadd_assoc c b d;
    A.cadd_assoc a c (A.cadd b d)

let copp_cadd (x y:B.cut)
  : Lemma (A.copp (A.cadd x y) == A.cadd (A.copp x) (A.copp y))
  = cshuffle4 (A.copp x) (A.copp y) x y;
    cadd_opp_l x; cadd_opp_l y; A.cadd_zero A.czero;
    cadd_opp_l (A.cadd x y);
    cadd_cancel (A.cadd (A.copp x) (A.copp y)) (A.copp (A.cadd x y))
                (A.cadd x y)

let clt_copp (x y:B.cut)
  : Lemma (B.clt (A.copp y) (A.copp x) <==> B.clt x y)
  = A.cadd_mono_rev (A.copp y) (A.copp x) (A.cadd x y);
    A.cadd_comm (A.copp y) (A.cadd x y);
    A.cadd_assoc x y (A.copp y); A.cadd_opp y; A.cadd_zero x;
    A.cadd_assoc (A.copp x) x y; cadd_opp_l x; cadd_zero_l y

let cle_copp (x y:B.cut)
  : Lemma (B.cle x y <==> B.cle (A.copp y) (A.copp x))
  = clt_copp x y;
    introduce A.copp y == A.copp x ==> x == y with copp_inj y x

(**** The sign of a cut *)

let nonneg_or (x:B.cut) : Lemma (nonneg x \/ nonneg (A.copp x))
  = B.cle_total A.czero x;
    cle_copp x A.czero;
    copp_czero ()

let nonneg_both (x:B.cut)
  : Lemma (requires nonneg x /\ nonneg (A.copp x)) (ensures x == A.czero)
  = cle_copp A.czero x;
    copp_czero ();
    B.cle_antisym (A.copp x) A.czero;
    copp_copp x

let nonneg_cone () : Lemma (nonneg cone)
  = introduce forall (q:Q.rat). A.czero q ==> cone q
    with introduce A.czero q ==> cone q
    with begin
      czero_mem q; cone_mem q; qzero_lt_one ();
      Q.lt_trans q Q.zero Q.one
    end

let cadd_nonneg (y z:B.cut)
  : Lemma (requires nonneg y /\ nonneg z) (ensures nonneg (A.cadd y z))
  = cadd_upper y z;
    B.cle_trans A.czero z (A.cadd y z)

(**** Multiplication, all signs *)


let cmul (x y:B.cut) : GTot B.cut =
  if ID.strong_excluded_middle (nonneg x)
  then (if ID.strong_excluded_middle (nonneg y)
        then cpmul x y
        else A.copp (cpmul x (A.copp y)))
  else (if ID.strong_excluded_middle (nonneg y)
        then A.copp (cpmul (A.copp x) y)
        else cpmul (A.copp x) (A.copp y))

let cmul_pp (x y:B.cut)
  : Lemma (requires nonneg x /\ nonneg y) (ensures cmul x y == cpmul x y) = ()

let cmul_pn (x y:B.cut)
  : Lemma (requires nonneg x /\ ~(nonneg y))
          (ensures cmul x y == A.copp (cpmul x (A.copp y))) = ()

let cmul_np (x y:B.cut)
  : Lemma (requires ~(nonneg x) /\ nonneg y)
          (ensures cmul x y == A.copp (cpmul (A.copp x) y)) = ()

let cmul_nn (x y:B.cut)
  : Lemma (requires ~(nonneg x) /\ ~(nonneg y))
          (ensures cmul x y == cpmul (A.copp x) (A.copp y)) = ()

let cmul_comm (x y:B.cut) : Lemma (cmul x y == cmul y x)
  = cpmul_comm x y;
    cpmul_comm x (A.copp y);
    cpmul_comm (A.copp x) y;
    cpmul_comm (A.copp x) (A.copp y)

let cpmul_zero_l (y:B.cut) : Lemma (cpmul A.czero y == A.czero)
  = cpmul_comm A.czero y; cpmul_zero y

let cmul_czero_l (y:B.cut) : Lemma (cmul A.czero y == A.czero)
  = copp_czero (); cpmul_zero_l y; cpmul_zero_l (A.copp y)

/// The four sign cases of [cmul (copp x) y == copp (cmul x y)], each with the
/// branch of [cmul] it lands in already resolved.

let cmul_copp_l0 (x y:B.cut)
  : Lemma (requires nonneg x /\ nonneg (A.copp x))
          (ensures  cmul (A.copp x) y == A.copp (cmul x y))
  = nonneg_both x; copp_czero (); cmul_czero_l y

let cmul_copp_l1 (x y:B.cut)
  : Lemma (requires nonneg x /\ ~(nonneg (A.copp x)) /\ nonneg y)
          (ensures  cmul (A.copp x) y == A.copp (cmul x y))
  = cmul_np (A.copp x) y; copp_copp x; cmul_pp x y

let cmul_copp_l2 (x y:B.cut)
  : Lemma (requires nonneg x /\ ~(nonneg (A.copp x)) /\ ~(nonneg y))
          (ensures  cmul (A.copp x) y == A.copp (cmul x y))
  = cmul_nn (A.copp x) y; copp_copp x; cmul_pn x y;
    copp_copp (cpmul x (A.copp y))

let cmul_copp_l3 (x y:B.cut)
  : Lemma (requires ~(nonneg x) /\ nonneg y)
          (ensures  cmul (A.copp x) y == A.copp (cmul x y))
  = nonneg_or x; cmul_pp (A.copp x) y; cmul_np x y;
    copp_copp (cpmul (A.copp x) y)

let cmul_copp_l4 (x y:B.cut)
  : Lemma (requires ~(nonneg x) /\ ~(nonneg y))
          (ensures  cmul (A.copp x) y == A.copp (cmul x y))
  = nonneg_or x; cmul_pn (A.copp x) y; cmul_nn x y

let cmul_copp_l (x y:B.cut)
  : Lemma (cmul (A.copp x) y == A.copp (cmul x y))
  = introduce (nonneg x /\ nonneg (A.copp x)) ==>
              cmul (A.copp x) y == A.copp (cmul x y)
    with cmul_copp_l0 x y;
    introduce (nonneg x /\ ~(nonneg (A.copp x)) /\ nonneg y) ==>
              cmul (A.copp x) y == A.copp (cmul x y)
    with cmul_copp_l1 x y;
    introduce (nonneg x /\ ~(nonneg (A.copp x)) /\ ~(nonneg y)) ==>
              cmul (A.copp x) y == A.copp (cmul x y)
    with cmul_copp_l2 x y;
    introduce (~(nonneg x) /\ nonneg y) ==>
              cmul (A.copp x) y == A.copp (cmul x y)
    with cmul_copp_l3 x y;
    introduce (~(nonneg x) /\ ~(nonneg y)) ==>
              cmul (A.copp x) y == A.copp (cmul x y)
    with cmul_copp_l4 x y

let cmul_copp_r (x y:B.cut)
  : Lemma (cmul x (A.copp y) == A.copp (cmul x y))
  = cmul_comm x (A.copp y); cmul_copp_l y x; cmul_comm y x

let cmul_zero (x:B.cut) : Lemma (cmul x A.czero == A.czero)
  = nonneg_or x;
    copp_czero ();
    cpmul_zero x;
    cpmul_zero (A.copp x)

let cmul_one (x:B.cut) : Lemma (cmul x cone == x)
  = nonneg_cone ();
    nonneg_or x;
    copp_copp x;
    introduce nonneg x ==> cpmul x cone == x with cpmul_one x;
    introduce nonneg (A.copp x) ==> cpmul (A.copp x) cone == A.copp x
    with cpmul_one (A.copp x)


(**** Associativity, all signs *)

let cmul_assoc_ppp (x y z:B.cut)
  : Lemma (requires nonneg x /\ nonneg y /\ nonneg z)
          (ensures  cmul (cmul x y) z == cmul x (cmul y z))
  = cmul_pp x y; cmul_pp y z;
    cpmul_nonneg x y; cpmul_nonneg y z;
    cmul_pp (cpmul x y) z; cmul_pp x (cpmul y z);
    cpmul_assoc x y z

/// Reduction steps: it is enough to prove associativity when each argument in
/// turn has been replaced by its negation.

let cmul_assoc_z (x y z:B.cut)
  : Lemma (requires cmul (cmul x y) (A.copp z) == cmul x (cmul y (A.copp z)))
          (ensures  cmul (cmul x y) z == cmul x (cmul y z))
  = cmul_copp_r (cmul x y) z;
    cmul_copp_r y z;
    cmul_copp_r x (cmul y z);
    copp_inj (cmul (cmul x y) z) (cmul x (cmul y z))

let cmul_assoc_y (x y z:B.cut)
  : Lemma (requires cmul (cmul x (A.copp y)) z == cmul x (cmul (A.copp y) z))
          (ensures  cmul (cmul x y) z == cmul x (cmul y z))
  = cmul_copp_r x y;
    cmul_copp_l (cmul x y) z;
    cmul_copp_l y z;
    cmul_copp_r x (cmul y z);
    copp_inj (cmul (cmul x y) z) (cmul x (cmul y z))

let cmul_assoc_x (x y z:B.cut)
  : Lemma (requires cmul (cmul (A.copp x) y) z == cmul (A.copp x) (cmul y z))
          (ensures  cmul (cmul x y) z == cmul x (cmul y z))
  = cmul_copp_l x y;
    cmul_copp_l (cmul x y) z;
    cmul_copp_l x (cmul y z);
    copp_inj (cmul (cmul x y) z) (cmul x (cmul y z))

let cmul_assoc_pp (x y z:B.cut)
  : Lemma (requires nonneg x /\ nonneg y)
          (ensures  cmul (cmul x y) z == cmul x (cmul y z))
  = nonneg_or z;
    introduce nonneg z ==> cmul (cmul x y) z == cmul x (cmul y z)
    with cmul_assoc_ppp x y z;
    introduce nonneg (A.copp z) ==> cmul (cmul x y) z == cmul x (cmul y z)
    with (cmul_assoc_ppp x y (A.copp z); cmul_assoc_z x y z)

let cmul_assoc_p (x y z:B.cut)
  : Lemma (requires nonneg x)
          (ensures  cmul (cmul x y) z == cmul x (cmul y z))
  = nonneg_or y;
    introduce nonneg y ==> cmul (cmul x y) z == cmul x (cmul y z)
    with cmul_assoc_pp x y z;
    introduce nonneg (A.copp y) ==> cmul (cmul x y) z == cmul x (cmul y z)
    with (cmul_assoc_pp x (A.copp y) z; cmul_assoc_y x y z)

let cmul_assoc (x y z:B.cut)
  : Lemma (cmul (cmul x y) z == cmul x (cmul y z))
  = nonneg_or x;
    introduce nonneg x ==> cmul (cmul x y) z == cmul x (cmul y z)
    with cmul_assoc_p x y z;
    introduce nonneg (A.copp x) ==> cmul (cmul x y) z == cmul x (cmul y z)
    with (cmul_assoc_p (A.copp x) y z; cmul_assoc_x x y z)

(**** Distributivity, all signs *)

let cdistrib_ppp (x y z:B.cut)
  : Lemma (requires nonneg x /\ nonneg y /\ nonneg z)
          (ensures  cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z))
  = cadd_nonneg y z;
    cmul_pp x y; cmul_pp x z; cmul_pp x (A.cadd y z);
    cpmul_distrib x y z

let group_solve1 (p q w:B.cut)
  : Lemma (requires p == A.cadd w (A.copp q)) (ensures A.cadd p q == w)
  = A.cadd_assoc w (A.copp q) q; cadd_opp_l q; A.cadd_zero w

let group_solve2 (p q w:B.cut)
  : Lemma (requires A.copp q == A.cadd p (A.copp w)) (ensures A.cadd p q == w)
  = copp_copp q; copp_cadd p (A.copp w); copp_copp w;
    A.cadd_assoc p (A.copp p) w; A.cadd_opp p; cadd_zero_l w

let cdistrib_b1 (x y z:B.cut)
  : Lemma (requires nonneg x /\ nonneg y /\ ~(nonneg z) /\ nonneg (A.cadd y z))
          (ensures  cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z))
  = nonneg_or z;
    A.cadd_assoc y z (A.copp z); A.cadd_opp z; A.cadd_zero y;
    cdistrib_ppp x (A.cadd y z) (A.copp z);
    cmul_copp_r x z;
    group_solve1 (cmul x y) (cmul x z) (cmul x (A.cadd y z))

let cdistrib_b2 (x y z:B.cut)
  : Lemma (requires nonneg x /\ nonneg y /\ ~(nonneg z) /\
                    ~(nonneg (A.cadd y z)))
          (ensures  cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z))
  = nonneg_or z; nonneg_or (A.cadd y z);
    copp_cadd y z;
    A.cadd_assoc y (A.copp y) (A.copp z); A.cadd_opp y;
    cadd_zero_l (A.copp z);
    cdistrib_ppp x y (A.copp (A.cadd y z));
    cmul_copp_r x z;
    cmul_copp_r x (A.cadd y z);
    group_solve2 (cmul x y) (cmul x z) (cmul x (A.cadd y z))

let cdistrib_pp (x y z:B.cut)
  : Lemma (requires nonneg x /\ nonneg y)
          (ensures  cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z))
  = nonneg_or z;
    introduce nonneg z ==>
              cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z)
    with cdistrib_ppp x y z;
    introduce (~(nonneg z) /\ nonneg (A.cadd y z)) ==>
              cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z)
    with cdistrib_b1 x y z;
    introduce (~(nonneg z) /\ ~(nonneg (A.cadd y z))) ==>
              cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z)
    with cdistrib_b2 x y z

let cdistrib_np (x y z:B.cut)
  : Lemma (requires nonneg x /\ ~(nonneg y) /\ nonneg z)
          (ensures  cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z))
  = cdistrib_pp x z y;
    A.cadd_comm y z;
    A.cadd_comm (cmul x z) (cmul x y)

let cdistrib_nn (x y z:B.cut)
  : Lemma (requires nonneg x /\ ~(nonneg y) /\ ~(nonneg z))
          (ensures  cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z))
  = nonneg_or y; nonneg_or z;
    copp_copp y; copp_copp z;
    copp_cadd (A.copp y) (A.copp z);
    cdistrib_ppp x (A.copp y) (A.copp z);
    cmul_copp_r x (A.cadd (A.copp y) (A.copp z));
    cmul_copp_r x (A.copp y);
    cmul_copp_r x (A.copp z);
    copp_cadd (cmul x (A.copp y)) (cmul x (A.copp z))

let cdistrib_p (x y z:B.cut)
  : Lemma (requires nonneg x)
          (ensures  cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z))
  = nonneg_or y; nonneg_or z;
    introduce nonneg y ==>
              cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z)
    with cdistrib_pp x y z;
    introduce (~(nonneg y) /\ nonneg z) ==>
              cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z)
    with cdistrib_np x y z;
    introduce (~(nonneg y) /\ ~(nonneg z)) ==>
              cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z)
    with cdistrib_nn x y z

let cdistrib_x (x y z:B.cut)
  : Lemma (requires cmul (A.copp x) (A.cadd y z) ==
                    A.cadd (cmul (A.copp x) y) (cmul (A.copp x) z))
          (ensures  cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z))
  = cmul_copp_l x (A.cadd y z);
    cmul_copp_l x y; cmul_copp_l x z;
    copp_cadd (cmul x y) (cmul x z);
    copp_inj (cmul x (A.cadd y z)) (A.cadd (cmul x y) (cmul x z))

let cmul_distrib (x y z:B.cut)
  : Lemma (cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z))
  = nonneg_or x;
    introduce nonneg x ==>
              cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z)
    with cdistrib_p x y z;
    introduce nonneg (A.copp x) ==>
              cmul x (A.cadd y z) == A.cadd (cmul x y) (cmul x z)
    with (cdistrib_p (A.copp x) y z; cdistrib_x x y z)


(**** Compatibility with the order *)

let cpos_copp (u:B.cut)
  : Lemma (B.clt A.czero u <==> B.clt (A.copp u) A.czero)
  = clt_copp A.czero u; copp_czero ()

let cpos_nonneg (u:B.cut)
  : Lemma (requires B.clt A.czero u) (ensures nonneg u) = ()

/// A cut strictly above zero contains a strictly positive rational.
let cpos_witness (u:B.cut)
  : Ghost Q.rat (requires B.clt A.czero u)
                (ensures fun a -> u a /\ Q.lt Q.zero a)
  = let a = B.clt_witness A.czero u in
    czero_mem a;
    Q.lt_total a Q.zero;
    let a2 = B.cut_above u a in
    introduce Q.lt Q.zero a ==> Q.lt Q.zero a2
    with Q.lt_trans Q.zero a a2;
    a2

let cmul_pos (u z:B.cut)
  : Lemma (requires B.clt A.czero u /\ B.clt A.czero z)
          (ensures  B.clt A.czero (cmul u z))
  = let a = cpos_witness u in
    let b = cpos_witness z in
    Q.mul_pos a b;
    cmul_pp u z;
    cpmul_nonneg u z;
    czero_mem Q.zero;
    Q.lt_irrefl Q.zero;
    introduce exists (a2 b2:Q.rat).
        u a2 /\ z b2 /\ Q.lt Q.zero a2 /\ Q.lt Q.zero b2 /\
        Q.lt Q.zero (Q.mul a2 b2)
    with a b and ();
    B.clt_of_witness A.czero (cmul u z) Q.zero

let cneg_copp (u:B.cut)
  : Lemma (B.clt u A.czero <==> B.clt A.czero (A.copp u))
  = cpos_copp (A.copp u); copp_copp u

let cmul_neg (u z:B.cut)
  : Lemma (requires B.clt A.czero z /\ B.clt u A.czero)
          (ensures  B.clt (cmul u z) A.czero)
  = cneg_copp u;
    cmul_pos (A.copp u) z;
    cmul_copp_l u z;
    cneg_copp (cmul u z)

let cmul_pos_rev (u z:B.cut)
  : Lemma (requires B.clt A.czero z /\ B.clt A.czero (cmul u z))
          (ensures  B.clt A.czero u)
  = B.clt_total A.czero u;
    B.clt_irrefl A.czero;
    introduce u == A.czero ==> B.clt A.czero u
    with cmul_czero_l z;
    introduce B.clt u A.czero ==> B.clt A.czero u
    with begin
      cmul_neg u z;
      B.clt_trans A.czero (cmul u z) A.czero
    end

/// [x < y] iff [0 < y - x].
let clt_sub (x y:B.cut)
  : Lemma (B.clt x y <==> B.clt A.czero (A.cadd y (A.copp x)))
  = A.cadd_mono_rev A.czero (A.cadd y (A.copp x)) x;
    cadd_zero_l x;
    A.cadd_assoc y (A.copp x) x;
    cadd_opp_l x;
    A.cadd_zero y

let cmul_sub (x y z:B.cut)
  : Lemma (cmul (A.cadd y (A.copp x)) z ==
           A.cadd (cmul y z) (A.copp (cmul x z)))
  = cmul_comm (A.cadd y (A.copp x)) z;
    cmul_distrib z y (A.copp x);
    cmul_comm z y;
    cmul_comm z (A.copp x);
    cmul_copp_l x z

let cmul_mono (x y z:B.cut)
  : Lemma (requires B.clt A.czero z)
          (ensures  B.clt (cmul x z) (cmul y z) <==> B.clt x y)
  = clt_sub x y;
    clt_sub (cmul x z) (cmul y z);
    cmul_sub x y z;
    introduce B.clt A.czero (A.cadd y (A.copp x)) ==>
              B.clt A.czero (cmul (A.cadd y (A.copp x)) z)
    with cmul_pos (A.cadd y (A.copp x)) z;
    introduce B.clt A.czero (cmul (A.cadd y (A.copp x)) z) ==>
              B.clt A.czero (A.cadd y (A.copp x))
    with cmul_pos_rev (A.cadd y (A.copp x)) z

(**** The embedding of the rationals is multiplicative *)

let rat_mul_pp1 (p q:Q.rat)
  : Lemma (requires Q.lt Q.zero p /\ Q.lt Q.zero q)
          (ensures  B.cle (cpmul (B.rat_cut p) (B.rat_cut q))
                          (B.rat_cut (Q.mul p q)))
  = Q.mul_pos p q;
    introduce forall (t:Q.rat).
        cpmul (B.rat_cut p) (B.rat_cut q) t ==> B.rat_cut (Q.mul p q) t
    with introduce cpmul (B.rat_cut p) (B.rat_cut q) t ==> B.rat_cut (Q.mul p q) t
    with begin
      B.rat_cut_mem (Q.mul p q) t;
      introduce Q.lt t Q.zero ==> Q.lt t (Q.mul p q)
      with Q.lt_trans t Q.zero (Q.mul p q);
      introduce (exists (a b:Q.rat).
                   B.rat_cut p a /\ B.rat_cut q b /\
                   Q.lt Q.zero a /\ Q.lt Q.zero b /\ Q.lt t (Q.mul a b))
                ==> Q.lt t (Q.mul p q)
      with eliminate exists (a b:Q.rat).
             B.rat_cut p a /\ B.rat_cut q b /\
             Q.lt Q.zero a /\ Q.lt Q.zero b /\ Q.lt t (Q.mul a b)
      with begin
        B.rat_cut_mem p a; B.rat_cut_mem q b;
        qmul_lt2 a p b q;
        Q.lt_trans t (Q.mul a b) (Q.mul p q)
      end
    end

/// Given [0 <= t < p*q] with [p,q > 0], split [t] as a product of a member of
/// [rat_cut p] and a member of [rat_cut q].
let rat_mul_split (p q t:Q.rat)
  : Lemma (requires Q.lt Q.zero p /\ Q.lt Q.zero q /\
                    Q.le Q.zero t /\ Q.lt t (Q.mul p q))
          (ensures  cpmul (B.rat_cut p) (B.rat_cut q) t)
  = qlt_div t p q;
    let a = Q.mid (Q.div t q) p in
    Q.mid_spec (Q.div t q) p;
    qdiv_nonneg t q;
    qle_lt_trans Q.zero (Q.div t q) a;
    qlt_div t a q;
    Q.mul_comm a q;
    qlt_div t q a;
    let b = Q.mid (Q.div t a) q in
    Q.mid_spec (Q.div t a) q;
    qdiv_nonneg t a;
    qle_lt_trans Q.zero (Q.div t a) b;
    qlt_div t b a;
    Q.mul_comm b a;
    B.rat_cut_mem p a;
    B.rat_cut_mem q b;
    mem1 (B.rat_cut p) (B.rat_cut q) a b t

let rat_mul_pp2 (p q:Q.rat)
  : Lemma (requires Q.lt Q.zero p /\ Q.lt Q.zero q)
          (ensures  B.cle (B.rat_cut (Q.mul p q))
                          (cpmul (B.rat_cut p) (B.rat_cut q)))
  = introduce forall (t:Q.rat).
        B.rat_cut (Q.mul p q) t ==> cpmul (B.rat_cut p) (B.rat_cut q) t
    with introduce B.rat_cut (Q.mul p q) t ==> cpmul (B.rat_cut p) (B.rat_cut q) t
    with begin
      B.rat_cut_mem (Q.mul p q) t;
      Q.lt_total t Q.zero;
      introduce ~(Q.lt t Q.zero) ==> cpmul (B.rat_cut p) (B.rat_cut q) t
      with rat_mul_split p q t
    end

let rat_mul_pp (p q:Q.rat)
  : Lemma (requires Q.lt Q.zero p /\ Q.lt Q.zero q)
          (ensures  B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q))
  = B.rat_cut_lt Q.zero p; B.rat_cut_lt Q.zero q;
    cmul_pp (B.rat_cut p) (B.rat_cut q);
    rat_mul_pp1 p q; rat_mul_pp2 p q;
    B.cle_antisym (B.rat_cut (Q.mul p q)) (cpmul (B.rat_cut p) (B.rat_cut q))

let qmul_neg_r (p q:Q.rat) : Lemma (Q.mul p (Q.neg q) == Q.neg (Q.mul p q))
  = Q.mul_comm p (Q.neg q); Q.mul_neg q p; Q.mul_comm q p

let qneg_pos (p:Q.rat)
  : Lemma (Q.lt p Q.zero <==> Q.lt Q.zero (Q.neg p))
  = A.qneg_lt_zero p

let rat_mul_np (p q:Q.rat)
  : Lemma (requires Q.lt p Q.zero /\ Q.lt Q.zero q)
          (ensures  B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q))
  = qneg_pos p;
    rat_mul_pp (Q.neg p) q;
    A.rat_opp p;
    cmul_copp_l (B.rat_cut p) (B.rat_cut q);
    Q.mul_neg p q;
    A.rat_opp (Q.mul p q);
    copp_inj (B.rat_cut (Q.mul p q)) (cmul (B.rat_cut p) (B.rat_cut q))

let rat_mul_pn (p q:Q.rat)
  : Lemma (requires Q.lt Q.zero p /\ Q.lt q Q.zero)
          (ensures  B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q))
  = rat_mul_np q p;
    Q.mul_comm q p;
    cmul_comm (B.rat_cut q) (B.rat_cut p)

let rat_mul_nn (p q:Q.rat)
  : Lemma (requires Q.lt p Q.zero /\ Q.lt q Q.zero)
          (ensures  B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q))
  = qneg_pos p; qneg_pos q;
    rat_mul_pp (Q.neg p) (Q.neg q);
    A.rat_opp p; A.rat_opp q;
    cmul_copp_l (B.rat_cut p) (A.copp (B.rat_cut q));
    cmul_copp_r (B.rat_cut p) (B.rat_cut q);
    copp_copp (cmul (B.rat_cut p) (B.rat_cut q));
    Q.mul_neg p (Q.neg q);
    qmul_neg_r p q;
    Q.neg_neg (Q.mul p q)

let rat_mul_z (q:Q.rat)
  : Lemma (B.rat_cut (Q.mul Q.zero q) == cmul (B.rat_cut Q.zero) (B.rat_cut q))
  = Q.mul_comm Q.zero q; Q.mul_zero q;
    cmul_czero_l (B.rat_cut q)

let rat_mul (p q:Q.rat)
  : Lemma (B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q))
  = Q.lt_total p Q.zero;
    Q.lt_total q Q.zero;
    introduce p == Q.zero ==> B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q)
    with rat_mul_z q;
    introduce q == Q.zero ==> B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q)
    with begin
      rat_mul_z p;
      Q.mul_comm p q;
      cmul_comm (B.rat_cut p) (B.rat_cut q)
    end;
    introduce (Q.lt Q.zero p /\ Q.lt Q.zero q) ==> B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q)
    with rat_mul_pp p q;
    introduce (Q.lt p Q.zero /\ Q.lt Q.zero q) ==> B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q)
    with rat_mul_np p q;
    introduce (Q.lt Q.zero p /\ Q.lt q Q.zero) ==> B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q)
    with rat_mul_pn p q;
    introduce (Q.lt p Q.zero /\ Q.lt q Q.zero) ==> B.rat_cut (Q.mul p q) == cmul (B.rat_cut p) (B.rat_cut q)
    with rat_mul_nn p q

(**** Multiplicative approximation *)

let qle_trans (p q r:Q.rat)
  : Lemma (requires Q.le p q /\ Q.le q r) (ensures Q.le p r)
  = introduce (Q.lt p q /\ Q.lt q r) ==> Q.lt p r with Q.lt_trans p q r

let qadd_le_r (u v c:Q.rat)
  : Lemma (requires Q.le u v) (ensures Q.le (Q.add u c) (Q.add v c))
  = Q.lt_add_r u v c

let qmul_le_nonneg (u v c:Q.rat)
  : Lemma (requires Q.le u v /\ Q.le Q.zero c)
          (ensures  Q.le (Q.mul u c) (Q.mul v c))
  = introduce Q.lt Q.zero c ==> Q.le (Q.mul u c) (Q.mul v c)
    with Q.lt_mul_pos u v c;
    introduce Q.zero == c ==> Q.le (Q.mul u c) (Q.mul v c)
    with (Q.mul_zero u; Q.mul_zero v)

/// [(1-s)(1+s) == 1 - s^2].
let qsq_ident (s:Q.rat)
  : Lemma (Q.mul (Q.sub Q.one s) (Q.add Q.one s) == Q.sub Q.one (Q.mul s s))
  = let t = Q.sub Q.one s in
    Q.distrib t Q.one s;
    Q.mul_one t;
    Q.mul_comm t s;
    Q.distrib s Q.one (Q.neg s);
    Q.mul_one s;
    qmul_neg_r s s;
    Q.add_assoc t s (Q.neg (Q.mul s s));
    Q.add_assoc Q.one (Q.neg s) s;
    Q.add_comm (Q.neg s) s;
    Q.add_neg s;
    Q.add_zero Q.one

let qsq_lt_one (s:Q.rat)
  : Lemma (requires Q.lt Q.zero s)
          (ensures  Q.lt (Q.sub Q.one (Q.mul s s)) Q.one)
  = Q.mul_pos s s;
    A.qneg_lt_zero' (Q.mul s s);
    qlt_add_neg (Q.neg (Q.mul s s)) Q.one;
    Q.add_comm (Q.neg (Q.mul s s)) Q.one

/// The arithmetic core of the multiplicative approximation lemma.
let mapprox_arith (t a eps r:Q.rat)
  : Lemma (requires Q.le Q.zero t /\ Q.lt t Q.one /\ Q.lt Q.zero a /\
                    Q.le r (Q.add a eps) /\
                    Q.le eps (Q.mul (Q.sub Q.one t) a))
          (ensures  Q.lt (Q.mul t r) a)
  = let s = Q.sub Q.one t in
    qsub_pos t Q.one;
    (* r <= a + s*a = a*(1+s) *)
    qadd_le_r eps (Q.mul s a) a;
    Q.add_comm a eps;
    Q.add_comm a (Q.mul s a);
    qle_trans r (Q.add a eps) (Q.add (Q.mul s a) a);
    Q.distrib a Q.one s;
    Q.mul_one a;
    Q.mul_comm a s;
    Q.add_comm (Q.mul s a) a;
    (* t*r <= t*(a*(1+s)) *)
    qmul_le_nonneg r (Q.mul a (Q.add Q.one s)) t;
    Q.mul_comm r t;
    Q.mul_comm (Q.mul a (Q.add Q.one s)) t;
    (* t*(a*(1+s)) == a*((1-s')...) : rearrange to a * ((1-s)(1+s)) *)
    Q.mul_assoc a (Q.add Q.one s) t;
    Q.mul_comm (Q.add Q.one s) t;
    qsub_sub Q.one t;
    qsq_ident s;
    (* a * (1 - s^2) < a *)
    qsq_lt_one s;
    Q.lt_mul_pos (Q.sub Q.one (Q.mul s s)) Q.one a;
    Q.mul_comm (Q.sub Q.one (Q.mul s s)) a;
    Q.mul_comm Q.one a;
    Q.mul_one a;
    qle_lt_trans (Q.mul t r) (Q.mul a (Q.sub Q.one (Q.mul s s))) a

/// The larger of two members of a cut, one of which is known positive.
let qmax_in' (c:B.cut) (a1 a0:Q.rat)
  : Ghost Q.rat
      (requires c a1 /\ c a0 /\ Q.lt Q.zero a0)
      (ensures fun a -> c a /\ Q.lt Q.zero a /\ Q.le a1 a /\ Q.le a0 a)
  = Q.lt_total a1 a0;
    introduce Q.lt a0 a1 ==> Q.lt Q.zero a1 with Q.lt_trans Q.zero a0 a1;
    if Q.lt a1 a0 then a0 else a1

/// **Multiplicative approximation lemma.** For a cut [c] strictly above zero
/// and a rational [0 <= t < 1], there are a positive member [a] of [c] and a
/// positive non-member [r] with [t*r < a].  Equivalently, the ratio [a/r] can
/// be pushed arbitrarily close to 1 from below.
let mapprox (c:B.cut) (t:Q.rat)
  : Ghost (Q.rat & Q.rat)
      (requires B.clt A.czero c /\ Q.le Q.zero t /\ Q.lt t Q.one)
      (ensures fun (a, r) -> c a /\ ~(c r) /\ Q.lt Q.zero a /\ Q.lt Q.zero r /\
                          Q.lt (Q.mul t r) a)
  = let a0 = cpos_witness c in
    qsub_pos t Q.one;
    let eps = Q.mul (Q.sub Q.one t) a0 in
    Q.mul_pos (Q.sub Q.one t) a0;
    let (a1, r) = B.approx c eps in
    let a = qmax_in' c a1 a0 in
    B.mem_lt_nonmem c a r;
    Q.lt_trans Q.zero a r;
    qadd_le_r a1 a eps;
    qmul_le_nonneg a0 a (Q.sub Q.one t);
    Q.mul_comm a0 (Q.sub Q.one t);
    Q.mul_comm a (Q.sub Q.one t);
    mapprox_arith t a eps r;
    (a, r)

(**** Multiplicative inverse *)

let qpos_ne_zero (r:Q.rat) : Lemma (requires Q.lt Q.zero r) (ensures r =!= Q.zero)
  = Q.lt_irrefl Q.zero

let qmul_inv_l (r:Q.rat)
  : Lemma (requires Q.lt Q.zero r) (ensures Q.mul (Q.inv r) r == Q.one)
  = qpos_ne_zero r; Q.inv_num_den r; Q.mul_comm r (Q.inv r)

let qinv_lt (r r':Q.rat)
  : Lemma (requires Q.lt Q.zero r /\ Q.lt r r')
          (ensures  Q.lt (Q.inv r') (Q.inv r))
  = Q.lt_trans Q.zero r r';
    qpos_ne_zero r; qpos_ne_zero r';
    Q.inv_pos r; Q.inv_pos r';
    Q.mul_pos (Q.inv r) (Q.inv r');
    Q.lt_mul_pos r r' (Q.mul (Q.inv r) (Q.inv r'));
    Q.mul_assoc r (Q.inv r) (Q.inv r');
    Q.inv_num_den r;
    Q.mul_comm Q.one (Q.inv r');
    Q.mul_one (Q.inv r');
    Q.mul_comm (Q.inv r) (Q.inv r');
    Q.mul_assoc r' (Q.inv r') (Q.inv r);
    Q.inv_num_den r';
    Q.mul_comm Q.one (Q.inv r);
    Q.mul_one (Q.inv r)

/// The reciprocal cut of a strictly positive cut.
let invp (x:B.cut) (q:Q.rat) : prop =
  Q.lt q Q.zero \/
  (exists (r:Q.rat). Q.lt Q.zero r /\ ~(x r) /\ Q.lt q (Q.inv r))

let inv_ne (x:B.cut) : Lemma (exists (q:Q.rat). invp x q)
  = introduce exists (q:Q.rat). invp x q with (Q.below Q.zero) and ()

let inv_nf (x:B.cut)
  : Lemma (requires B.clt A.czero x) (ensures exists (q:Q.rat). ~(invp x q))
  = let a0 = cpos_witness x in
    qpos_ne_zero a0;
    Q.inv_pos a0;
    Q.lt_asym Q.zero (Q.inv a0);
    introduce invp x (Q.inv a0) ==> False
    with eliminate exists (r:Q.rat).
           Q.lt Q.zero r /\ ~(x r) /\ Q.lt (Q.inv a0) (Q.inv r)
    with begin
      B.mem_lt_nonmem x a0 r;
      qinv_lt a0 r;
      Q.lt_asym (Q.inv a0) (Q.inv r)
    end;
    introduce exists (q:Q.rat). ~(invp x q) with (Q.inv a0) and ()

let inv_dc (x:B.cut)
  : Lemma (forall (u v:Q.rat). (invp x v /\ Q.lt u v) ==> invp x u)
  = introduce forall (u v:Q.rat). (invp x v /\ Q.lt u v) ==> invp x u
    with introduce (invp x v /\ Q.lt u v) ==> invp x u
    with begin
      introduce Q.lt v Q.zero ==> invp x u with Q.lt_trans u v Q.zero;
      introduce (exists (r:Q.rat). Q.lt Q.zero r /\ ~(x r) /\ Q.lt v (Q.inv r))
                ==> invp x u
      with eliminate exists (r:Q.rat).
             Q.lt Q.zero r /\ ~(x r) /\ Q.lt v (Q.inv r)
      with begin
        Q.lt_trans u v (Q.inv r);
        introduce exists (r2:Q.rat).
            Q.lt Q.zero r2 /\ ~(x r2) /\ Q.lt u (Q.inv r2)
        with r and ()
      end
    end

let inv_op (x:B.cut)
  : Lemma (forall (u:Q.rat). invp x u ==> (exists (v:Q.rat). invp x v /\ Q.lt u v))
  = introduce forall (u:Q.rat).
        invp x u ==> (exists (v:Q.rat). invp x v /\ Q.lt u v)
    with introduce invp x u ==> (exists (v:Q.rat). invp x v /\ Q.lt u v)
    with begin
      introduce Q.lt u Q.zero ==> (exists (v:Q.rat). invp x v /\ Q.lt u v)
      with begin
        Q.mid_spec u Q.zero;
        introduce exists (v:Q.rat). invp x v /\ Q.lt u v
        with (Q.mid u Q.zero) and ()
      end;
      introduce (exists (r:Q.rat). Q.lt Q.zero r /\ ~(x r) /\ Q.lt u (Q.inv r))
                ==> (exists (v:Q.rat). invp x v /\ Q.lt u v)
      with eliminate exists (r:Q.rat).
             Q.lt Q.zero r /\ ~(x r) /\ Q.lt u (Q.inv r)
      with begin
        Q.mid_spec u (Q.inv r);
        introduce exists (r2:Q.rat).
            Q.lt Q.zero r2 /\ ~(x r2) /\ Q.lt (Q.mid u (Q.inv r)) (Q.inv r2)
        with r and ();
        introduce exists (v:Q.rat). invp x v /\ Q.lt u v
        with (Q.mid u (Q.inv r)) and ()
      end
    end

let cinv (x:B.cut{B.clt A.czero x})
  : c:B.cut{forall (q:Q.rat). c q <==> invp x q}
  = inv_ne x; inv_nf x; inv_dc x; inv_op x;
    B.mk_cut (invp x)

let cinv_pos (x:B.cut{B.clt A.czero x})
  : Lemma (B.clt A.czero (cinv x))
  = let r = B.cut_nonmem x in
    let a0 = cpos_witness x in
    B.mem_lt_nonmem x a0 r;
    Q.lt_trans Q.zero a0 r;
    Q.inv_pos r;
    introduce exists (r2:Q.rat). Q.lt Q.zero r2 /\ ~(x r2) /\ Q.lt Q.zero (Q.inv r2)
    with r and ();
    introduce forall (q:Q.rat). A.czero q ==> cinv x q
    with introduce A.czero q ==> cinv x q
    with czero_mem q;
    czero_mem Q.zero;
    Q.lt_irrefl Q.zero;
    B.clt_of_witness A.czero (cinv x) Q.zero

let cinv_le1 (x:B.cut{B.clt A.czero x})
  : Lemma (B.cle (cpmul x (cinv x)) cone)
  = qzero_lt_one ();
    introduce forall (t:Q.rat). cpmul x (cinv x) t ==> cone t
    with introduce cpmul x (cinv x) t ==> cone t
    with begin
      cone_mem t;
      introduce Q.lt t Q.zero ==> Q.lt t Q.one
      with Q.lt_trans t Q.zero Q.one;
      introduce (exists (a b:Q.rat).
                   x a /\ cinv x b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
                   Q.lt t (Q.mul a b)) ==> Q.lt t Q.one
      with eliminate exists (a b:Q.rat).
             x a /\ cinv x b /\ Q.lt Q.zero a /\ Q.lt Q.zero b /\
             Q.lt t (Q.mul a b)
      with begin
        Q.lt_asym Q.zero b;
        eliminate exists (r:Q.rat). Q.lt Q.zero r /\ ~(x r) /\ Q.lt b (Q.inv r)
        with begin
          B.mem_lt_nonmem x a r;
          qmul_lt2 a r b (Q.inv r);
          qpos_ne_zero r;
          Q.inv_num_den r;
          Q.lt_trans t (Q.mul a b) Q.one
        end
      end
    end

/// From [t*r < a] with [a,r > 0] conclude [t < a/r].
let cinv_shift (t a r:Q.rat)
  : Lemma (requires Q.lt Q.zero a /\ Q.lt Q.zero r /\ Q.lt (Q.mul t r) a)
          (ensures  Q.lt t (Q.mul a (Q.inv r)))
  = Q.inv_pos r;
    Q.lt_mul_pos (Q.mul t r) a (Q.inv r);
    Q.mul_assoc t r (Q.inv r);
    qpos_ne_zero r;
    Q.inv_num_den r;
    Q.mul_one t

let cinv_le2 (x:B.cut{B.clt A.czero x})
  : Lemma (B.cle cone (cpmul x (cinv x)))
  = introduce forall (t:Q.rat). cone t ==> cpmul x (cinv x) t
    with introduce cone t ==> cpmul x (cinv x) t
    with begin
      cone_mem t;
      Q.lt_total t Q.zero;
      introduce ~(Q.lt t Q.zero) ==> cpmul x (cinv x) t
      with begin
        let (a, r) = mapprox x t in
        cinv_shift t a r;
        Q.mul_comm a (Q.inv r);
        qlt_div t (Q.inv r) a;
        let b = Q.mid (Q.div t a) (Q.inv r) in
        Q.mid_spec (Q.div t a) (Q.inv r);
        qdiv_nonneg t a;
        qle_lt_trans Q.zero (Q.div t a) b;
        qlt_div t b a;
        Q.mul_comm b a;
        introduce exists (r2:Q.rat).
            Q.lt Q.zero r2 /\ ~(x r2) /\ Q.lt b (Q.inv r2)
        with r and ();
        mem1 x (cinv x) a b t
      end
    end

/// **The reciprocal is a multiplicative inverse.**
let cmul_inv (x:B.cut)
  : Lemma (requires B.clt A.czero x)
          (ensures  cmul x (cinv x) == cone)
  = cinv_pos x;
    cmul_pp x (cinv x);
    cinv_le1 x; cinv_le2 x;
    B.cle_antisym (cpmul x (cinv x)) cone

#push-options "--z3rlimit 100"

let cinv0 (x:B.cut) : GTot B.cut =
  if ID.strong_excluded_middle (B.clt A.czero x) then cinv x else A.czero

let cinv0_pos (x:B.cut)
  : Lemma (requires B.clt A.czero x) (ensures cinv0 x == cinv x)
  = ()

/// The total reciprocal: [cinvt czero == czero].
let cinvt (x:B.cut) : GTot B.cut =
  if ID.strong_excluded_middle (B.clt A.czero x)
  then cinv x
  else A.copp (cinv0 (A.copp x))

let cinvt_pos (x:B.cut)
  : Lemma (requires B.clt A.czero x) (ensures cinvt x == cinv x)
  = ()

let cnotpos (x:B.cut)
  : Lemma (requires B.clt x A.czero) (ensures ~(B.clt A.czero x))
  = introduce B.clt A.czero x ==> False
    with (B.clt_trans A.czero x A.czero; B.clt_irrefl A.czero)

let cinvt_neg (x:B.cut)
  : Lemma (requires B.clt x A.czero)
          (ensures  cinvt x == A.copp (cinv0 (A.copp x)))
  = cnotpos x

let cmul_inv_neg (x:B.cut)
  : Lemma (requires B.clt x A.czero)
          (ensures  cmul x (cinvt x) == cone)
  = cneg_copp x;
    cinvt_neg x;
    cinv0_pos (A.copp x);
    let u = cinv (A.copp x) in
    cmul_inv (A.copp x);
    cmul_copp_l x u;
    copp_copp (cmul x u);
    copp_copp cone;
    cmul_copp_r x u

let cmul_invt (x:B.cut)
  : Lemma (requires x =!= A.czero) (ensures cmul x (cinvt x) == cone)
  = B.clt_total A.czero x;
    introduce B.clt A.czero x ==> cmul x (cinvt x) == cone
    with (cinvt_pos x; cmul_inv x);
    introduce B.clt x A.czero ==> cmul x (cinvt x) == cone
    with cmul_inv_neg x

let cinvt_zero () : Lemma (cinvt A.czero == A.czero)
  = B.clt_irrefl A.czero;
    copp_czero ()

#pop-options
#pop-options
