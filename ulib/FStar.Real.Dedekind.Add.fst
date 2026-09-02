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
module FStar.Real.Dedekind.Add

/// The additive group of Dedekind cuts.
///
///   x + y  =  { a + b       | a in x, b in y }
///     - x  =  { q | exists r > 0. -q - r not in x }
///
/// The offset [r] in the definition of negation is what stops [-x] from having
/// a greatest element when [x] is the cut of a rational.
///
/// Nothing is assumed here; see [FStar.Real.Dedekind.Base] for the (purely
/// logical) axioms the development rests on.

module Q = FStar.Rational
module B = FStar.Real.Dedekind.Base
module ID = FStar.IndefiniteDescription

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(**** Rational helpers *)

/// Each of these is stated on its own: batching them, or reasoning about them
/// inside a larger proof, is markedly slower.

let qlt_add2 (a a' b b':Q.rat)
  : Lemma (requires Q.lt a a' /\ Q.lt b b')
          (ensures Q.lt (Q.add a b) (Q.add a' b'))
  = Q.lt_add_r a a' b;
    Q.lt_add_r b b' a';
    Q.add_comm b a'; Q.add_comm b' a';
    Q.lt_trans (Q.add a b) (Q.add a' b) (Q.add a' b')

let qlt_add_l (a a' b:Q.rat)
  : Lemma (Q.lt (Q.add b a) (Q.add b a') <==> Q.lt a a')
  = Q.lt_add_r a a' b; Q.add_comm b a; Q.add_comm b a'

let qadd_zero_l (q:Q.rat) : Lemma (Q.add Q.zero q == q)
  = Q.add_comm Q.zero q; Q.add_zero q

let qsub_add (q b:Q.rat) : Lemma (Q.add (Q.sub q b) b == q)
  = Q.add_assoc q (Q.neg b) b;
    Q.add_comm (Q.neg b) b;
    Q.add_neg b;
    Q.add_comm b (Q.neg b);
    Q.add_zero q

let qadd_sub (b q:Q.rat) : Lemma (Q.add b (Q.sub q b) == q)
  = qsub_add q b; Q.add_comm b (Q.sub q b)

let qadd_sub_cancel (a b:Q.rat) : Lemma (Q.sub (Q.add a b) b == a)
  = Q.add_assoc a b (Q.neg b); Q.add_neg b; Q.add_zero a

let qsub_lt (q q' b:Q.rat)
  : Lemma (Q.lt (Q.sub q' b) (Q.sub q b) <==> Q.lt q' q)
  = Q.lt_add_r q' q (Q.neg b)

let qneg_add (a b:Q.rat) : Lemma (Q.neg (Q.add a b) == Q.add (Q.neg a) (Q.neg b))
  = Q.mul_neg Q.one (Q.add a b);
    Q.mul_comm Q.one (Q.add a b); Q.mul_one (Q.add a b);
    Q.distrib (Q.neg Q.one) a b;
    Q.mul_comm (Q.neg Q.one) a; Q.mul_neg Q.one a;
    Q.mul_comm Q.one a; Q.mul_one a;
    Q.mul_comm (Q.neg Q.one) b; Q.mul_neg Q.one b;
    Q.mul_comm Q.one b; Q.mul_one b

let qneg_zero () : Lemma (Q.neg Q.zero == Q.zero)
  = Q.add_neg Q.zero; qadd_zero_l (Q.neg Q.zero)

let qneg_lt_zero (q:Q.rat) : Lemma (Q.lt Q.zero (Q.neg q) <==> Q.lt q Q.zero)
  = qneg_zero (); Q.lt_neg q Q.zero

(**** Addition *)

let addp (x y:B.cut) (q:Q.rat) : prop =
  exists (a b:Q.rat). x a /\ y b /\ q == Q.add a b

let add_ne (x y:B.cut) : Lemma (exists (q:Q.rat). addp x y q)
  = let a = B.cut_mem x in
    let b = B.cut_mem y in
    introduce exists (q:Q.rat). addp x y q with (Q.add a b) and ()

let add_nf (x y:B.cut) : Lemma (exists (q:Q.rat). ~(addp x y q))
  = let a' = B.cut_nonmem x in
    let b' = B.cut_nonmem y in
    introduce addp x y (Q.add a' b') ==> False
    with eliminate exists (a b:Q.rat). x a /\ y b /\ Q.add a' b' == Q.add a b
      with begin
        B.mem_lt_nonmem x a a';
        B.mem_lt_nonmem y b b';
        qlt_add2 a a' b b';
        Q.lt_irrefl (Q.add a b)
      end;
    introduce exists (q:Q.rat). ~(addp x y q) with (Q.add a' b') and ()

let add_dc (x y:B.cut)
  : Lemma (forall (u v:Q.rat). (addp x y v /\ Q.lt u v) ==> addp x y u)
  = introduce forall (u v:Q.rat). (addp x y v /\ Q.lt u v) ==> addp x y u
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat). x a /\ y b /\ v == Q.add a b
      with begin
        qsub_add u b;
        qadd_sub_cancel a b;
        qsub_lt v u b;
        B.cut_down x (Q.sub u b) a;
        introduce exists (a2 b2:Q.rat). x a2 /\ y b2 /\ u == Q.add a2 b2
        with (Q.sub u b) b and ()
      end

let add_op_aux (x y:B.cut) (u:Q.rat)
  : Lemma (requires addp x y u)
          (ensures exists (v:Q.rat). addp x y v /\ Q.lt u v)
  = eliminate exists (a b:Q.rat). x a /\ y b /\ u == Q.add a b
    with begin
      let a2 = B.cut_above x a in
      Q.lt_add_r a a2 b;
      introduce exists (v:Q.rat). addp x y v /\ Q.lt u v
      with (Q.add a2 b) and ()
    end

let add_op (x y:B.cut) : Lemma (B.no_greatest (addp x y))
  = B.no_greatest_intro (addp x y) (add_op_aux x y)

let cadd (x y:B.cut) : c:B.cut{forall (q:Q.rat). c q <==> addp x y q} =
  add_ne x y; add_nf x y; add_dc x y; add_op x y;
  B.mk_cut (addp x y)

(**** Negation *)

let oppp (x:B.cut) (q:Q.rat) : prop =
  exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add q r)))

let opp_ne (x:B.cut) : Lemma (exists (q:Q.rat). oppp x q)
  = let b = B.cut_nonmem x in
    let q = Q.neg (Q.add b Q.one) in
    Q.of_int_lt 0 1;
    qneg_add b Q.one;
    Q.neg_neg b; Q.neg_neg Q.one;
    Q.add_assoc (Q.neg b) (Q.neg Q.one) Q.one;
    Q.add_comm (Q.neg Q.one) Q.one;
    Q.add_neg Q.one;
    Q.add_comm Q.one (Q.neg Q.one);
    Q.add_zero (Q.neg b);
    qneg_add (Q.neg b) (Q.neg Q.one);
    introduce exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add q r)))
    with Q.one and ();
    introduce exists (q:Q.rat). oppp x q with q and ()

let opp_nf (x:B.cut) : Lemma (exists (q:Q.rat). ~(oppp x q))
  = let a = B.cut_mem x in
    introduce oppp x (Q.neg a) ==> False
    with eliminate exists (r:Q.rat). Q.lt Q.zero r /\
                             ~(x (Q.neg (Q.add (Q.neg a) r)))
      with begin
        qneg_add (Q.neg a) r;
        Q.neg_neg a;
        Q.lt_add_r Q.zero r (Q.neg r);
        Q.add_neg r;
        qadd_zero_l (Q.neg r);
        qlt_add_l (Q.neg r) Q.zero a;
        Q.add_zero a;
        B.cut_down x (Q.add a (Q.neg r)) a
      end;
    introduce exists (q:Q.rat). ~(oppp x q) with (Q.neg a) and ()

let opp_dc (x:B.cut)
  : Lemma (forall (u v:Q.rat). (oppp x v /\ Q.lt u v) ==> oppp x u)
  = introduce forall (u v:Q.rat). (oppp x v /\ Q.lt u v) ==> oppp x u
    with introduce _ ==> _ with
      eliminate exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add v r)))
      with begin
        let s = Q.add r (Q.sub v u) in
        qsub_lt v u u;
        Q.add_neg u;
        qlt_add_l Q.zero (Q.sub v u) r;
        Q.add_zero r;
        Q.lt_trans Q.zero r s;
        Q.add_assoc u r (Q.sub v u);
        Q.add_comm r (Q.sub v u);
        Q.add_assoc u (Q.sub v u) r;
        qadd_sub u v;
        introduce exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add u r)))
        with s and ()
      end

let opp_op_aux (x:B.cut) (u:Q.rat)
  : Lemma (requires oppp x u)
          (ensures exists (v:Q.rat). oppp x v /\ Q.lt u v)
  = eliminate exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add u r)))
    with begin
      let s = Q.mid Q.zero r in
      Q.mid_spec Q.zero r;
      let v = Q.add u (Q.sub r s) in
      qsub_lt r s s;
      Q.add_neg s;
      qlt_add_l Q.zero (Q.sub r s) u;
      Q.add_zero u;
      Q.add_assoc u (Q.sub r s) s;
      qsub_add r s;
      introduce exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add v r)))
      with s and ();
      introduce exists (v:Q.rat). oppp x v /\ Q.lt u v with v and ()
    end

let opp_op (x:B.cut) : Lemma (B.no_greatest (oppp x))
  = B.no_greatest_intro (oppp x) (opp_op_aux x)

let copp (x:B.cut) : c:B.cut{forall (q:Q.rat). c q <==> oppp x q} =
  opp_ne x; opp_nf x; opp_dc x; opp_op x;
  B.mk_cut (oppp x)

(**** More rational rearrangements *)

let ac_shuffle (p q r:Q.rat)
  : Lemma (Q.add (Q.add p q) r == Q.add (Q.add p r) q)
  = Q.add_assoc p q r; Q.add_comm q r; Q.add_assoc p r q

let qadd_neg_l (b:Q.rat) : Lemma (Q.add (Q.neg b) b == Q.zero)
  = Q.add_neg b; Q.add_comm b (Q.neg b)

/// [(-(b+r)) + b == -r]
let qcancel2 (b r:Q.rat)
  : Lemma (Q.add (Q.neg (Q.add b r)) b == Q.neg r)
  = qneg_add b r;
    ac_shuffle (Q.neg b) (Q.neg r) b;
    qadd_neg_l b;
    qadd_zero_l (Q.neg r)

/// [-((-(a+r)) + r) == a]
let qcancel1 (a r:Q.rat)
  : Lemma (Q.neg (Q.add (Q.neg (Q.add a r)) r) == a)
  = qneg_add a r;
    Q.add_assoc (Q.neg a) (Q.neg r) r;
    qadd_neg_l r;
    Q.add_zero (Q.neg a);
    Q.neg_neg a

/// [a + (-((a+e)+r)) == -(e+r)]
let qcancel3 (a e r:Q.rat)
  : Lemma (Q.add a (Q.neg (Q.add (Q.add a e) r)) == Q.neg (Q.add e r))
  = Q.add_assoc a e r;
    qneg_add a (Q.add e r);
    Q.add_assoc a (Q.neg a) (Q.neg (Q.add e r));
    Q.add_neg a;
    qadd_zero_l (Q.neg (Q.add e r))

let qneg_lt_zero' (r:Q.rat) : Lemma (Q.lt (Q.neg r) Q.zero <==> Q.lt Q.zero r)
  = qneg_zero (); Q.lt_neg Q.zero r

(**** Commutativity *)

let cadd_comm_sub (x y:B.cut) : Lemma (B.cle (cadd x y) (cadd y x))
  = introduce forall (q:Q.rat). cadd x y q ==> cadd y x q
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat). x a /\ y b /\ q == Q.add a b
      with begin
        Q.add_comm a b;
        introduce exists (a2 b2:Q.rat). y a2 /\ x b2 /\ q == Q.add a2 b2
        with b a and ()
      end

let cadd_comm (x y:B.cut) : Lemma (cadd x y == cadd y x)
  = cadd_comm_sub x y; cadd_comm_sub y x;
    B.cle_antisym (cadd x y) (cadd y x)

(**** Associativity *)

let cadd_assoc_sub (x y z:B.cut)
  : Lemma (B.cle (cadd (cadd x y) z) (cadd x (cadd y z)))
  = introduce forall (q:Q.rat). cadd (cadd x y) z q ==> cadd x (cadd y z) q
    with introduce _ ==> _ with
      eliminate exists (u c:Q.rat). cadd x y u /\ z c /\ q == Q.add u c
      with eliminate exists (a b:Q.rat). x a /\ y b /\ u == Q.add a b
      with begin
        Q.add_assoc a b c;
        introduce exists (b2 c2:Q.rat). y b2 /\ z c2 /\ Q.add b c == Q.add b2 c2
        with b c and ();
        introduce exists (a2 u2:Q.rat). x a2 /\ cadd y z u2 /\ q == Q.add a2 u2
        with a (Q.add b c) and ()
      end

let cadd_assoc_sub' (x y z:B.cut)
  : Lemma (B.cle (cadd x (cadd y z)) (cadd (cadd x y) z))
  = introduce forall (q:Q.rat). cadd x (cadd y z) q ==> cadd (cadd x y) z q
    with introduce _ ==> _ with
      eliminate exists (a u:Q.rat). x a /\ cadd y z u /\ q == Q.add a u
      with eliminate exists (b c:Q.rat). y b /\ z c /\ u == Q.add b c
      with begin
        Q.add_assoc a b c;
        introduce exists (a2 b2:Q.rat). x a2 /\ y b2 /\ Q.add a b == Q.add a2 b2
        with a b and ();
        introduce exists (u2 c2:Q.rat). cadd x y u2 /\ z c2 /\ q == Q.add u2 c2
        with (Q.add a b) c and ()
      end

let cadd_assoc (x y z:B.cut)
  : Lemma (cadd (cadd x y) z == cadd x (cadd y z))
  = cadd_assoc_sub x y z; cadd_assoc_sub' x y z;
    B.cle_antisym (cadd (cadd x y) z) (cadd x (cadd y z))

(**** Zero *)

let czero : B.cut = B.rat_cut Q.zero

let cadd_zero_sub (x:B.cut) : Lemma (B.cle (cadd x czero) x)
  = introduce forall (q:Q.rat). cadd x czero q ==> x q
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat). x a /\ czero b /\ q == Q.add a b
      with begin
        B.rat_cut_mem Q.zero b;
        qlt_add_l b Q.zero a;
        Q.add_zero a;
        B.cut_down x q a
      end

let cadd_zero_sub' (x:B.cut) : Lemma (B.cle x (cadd x czero))
  = introduce forall (q:Q.rat). x q ==> cadd x czero q
    with introduce _ ==> _ with begin
      let a = B.cut_above x q in
      qsub_lt a q a;
      Q.add_neg a;
      B.rat_cut_mem Q.zero (Q.sub q a);
      qadd_sub a q;
      introduce exists (a2 b2:Q.rat). x a2 /\ czero b2 /\ q == Q.add a2 b2
      with a (Q.sub q a) and ()
    end

let cadd_zero (x:B.cut) : Lemma (cadd x czero == x)
  = cadd_zero_sub x; cadd_zero_sub' x;
    B.cle_antisym (cadd x czero) x

(**** Inverses *)

let cadd_opp_sub (x:B.cut) : Lemma (B.cle (cadd x (copp x)) czero)
  = introduce forall (q:Q.rat). cadd x (copp x) q ==> czero q
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat). x a /\ copp x b /\ q == Q.add a b
      with eliminate exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add b r)))
      with begin
        B.mem_lt_nonmem x a (Q.neg (Q.add b r));
        Q.lt_add_r a (Q.neg (Q.add b r)) b;
        qcancel2 b r;
        qneg_lt_zero' r;
        Q.lt_trans q (Q.neg r) Q.zero;
        B.rat_cut_mem Q.zero q
      end

let cadd_opp_sub' (x:B.cut) : Lemma (B.cle czero (cadd x (copp x)))
  = introduce forall (q:Q.rat). czero q ==> cadd x (copp x) q
    with introduce _ ==> _ with begin
      B.rat_cut_mem Q.zero q;
      qneg_lt_zero q;
      let e = Q.mid Q.zero (Q.neg q) in
      Q.mid_spec Q.zero (Q.neg q);
      let r = Q.sub (Q.neg q) e in
      qsub_lt (Q.neg q) e e;
      Q.add_neg e;
      let ab = B.approx x e in
      let a = fst ab in
      let a' = snd ab in
      let b = Q.neg (Q.add a' r) in
      qcancel1 a' r;
      introduce exists (r2:Q.rat). Q.lt Q.zero r2 /\ ~(x (Q.neg (Q.add b r2)))
      with r and ();
      qcancel3 a e r;
      qadd_sub e (Q.neg q);
      Q.neg_neg q;
      introduce exists (a2 b2:Q.rat). x a2 /\ copp x b2 /\ q == Q.add a2 b2
      with a b and ()
    end

let cadd_opp (x:B.cut) : Lemma (cadd x (copp x) == czero)
  = cadd_opp_sub x; cadd_opp_sub' x;
    B.cle_antisym (cadd x (copp x)) czero

(**** Compatibility of addition with the order *)

let qshift (q q2 c:Q.rat)
  : Lemma (Q.add q (Q.add c (Q.sub q2 q)) == Q.add q2 c)
  = Q.add_comm c (Q.sub q2 q);
    Q.add_assoc q (Q.sub q2 q) c;
    qadd_sub q q2

let cadd_mono (x y z:B.cut)
  : Lemma (requires B.clt x y) (ensures B.clt (cadd x z) (cadd y z))
  = let q = B.clt_witness x y in
    let q2 = B.cut_above y q in
    let e = Q.sub q2 q in
    qsub_lt q2 q q;
    Q.add_neg q;
    let cc = B.approx z e in
    let c = fst cc in
    let c' = snd cc in
    let w = Q.add q2 c in
    introduce exists (a2 b2:Q.rat). y a2 /\ z b2 /\ w == Q.add a2 b2
    with q2 c and ();
    introduce cadd x z w ==> False
    with eliminate exists (a b:Q.rat). x a /\ z b /\ w == Q.add a b
    with begin
      B.mem_lt_nonmem x a q;
      B.mem_lt_nonmem z b c';
      qlt_add2 a q b c';
      qshift q q2 c;
      Q.lt_irrefl w
    end;
    B.clt_of_witness (cadd x z) (cadd y z) w

let cadd_mono_rev (x y z:B.cut)
  : Lemma (B.clt (cadd x z) (cadd y z) <==> B.clt x y)
  = introduce B.clt x y ==> B.clt (cadd x z) (cadd y z)
    with cadd_mono x y z;
    introduce B.clt (cadd x z) (cadd y z) ==> B.clt x y
    with begin
      B.clt_total x y;
      B.clt_irrefl (cadd x z);
      introduce B.clt y x ==> B.clt x y
      with begin
        cadd_mono y x z;
        B.clt_trans (cadd x z) (cadd y z) (cadd x z);
        B.clt_irrefl (cadd x z)
      end
    end

(**** The embedding is additive *)

let qsub_flip (t a q:Q.rat)
  : Lemma (Q.lt (Q.sub t a) q <==> Q.lt (Q.sub t q) a)
  = Q.lt_add_r (Q.sub t a) q (Q.sub a q);
    qadd_sub q a;
    Q.add_assoc (Q.sub t a) a (Q.neg q);
    qsub_add t a

let rat_add_sub (p q:Q.rat)
  : Lemma (B.cle (B.rat_cut (Q.add p q)) (cadd (B.rat_cut p) (B.rat_cut q)))
  = introduce forall (t:Q.rat).
        B.rat_cut (Q.add p q) t ==> cadd (B.rat_cut p) (B.rat_cut q) t
    with introduce _ ==> _ with begin
      B.rat_cut_mem (Q.add p q) t;
      qsub_add t q;
      Q.lt_add_r (Q.sub t q) p q;
      let a = Q.mid (Q.sub t q) p in
      Q.mid_spec (Q.sub t q) p;
      let b = Q.sub t a in
      qsub_flip t a q;
      qadd_sub a t;
      B.rat_cut_mem p a;
      B.rat_cut_mem q b;
      introduce exists (a2 b2:Q.rat).
          B.rat_cut p a2 /\ B.rat_cut q b2 /\ t == Q.add a2 b2
      with a b and ()
    end

let rat_add_sub' (p q:Q.rat)
  : Lemma (B.cle (cadd (B.rat_cut p) (B.rat_cut q)) (B.rat_cut (Q.add p q)))
  = introduce forall (t:Q.rat).
        cadd (B.rat_cut p) (B.rat_cut q) t ==> B.rat_cut (Q.add p q) t
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat).
          B.rat_cut p a /\ B.rat_cut q b /\ t == Q.add a b
      with begin
        B.rat_cut_mem p a;
        B.rat_cut_mem q b;
        qlt_add2 a p b q;
        B.rat_cut_mem (Q.add p q) t
      end

let rat_add (p q:Q.rat)
  : Lemma (B.rat_cut (Q.add p q) == cadd (B.rat_cut p) (B.rat_cut q))
  = rat_add_sub p q; rat_add_sub' p q;
    B.cle_antisym (B.rat_cut (Q.add p q)) (cadd (B.rat_cut p) (B.rat_cut q))

(**** The embedding respects negation *)

let qneg_lt (t p:Q.rat) : Lemma (Q.lt t (Q.neg p) <==> Q.lt p (Q.neg t))
  = Q.lt_neg t (Q.neg p); Q.neg_neg p;
    Q.lt_neg p (Q.neg t); Q.neg_neg t

let rat_opp_sub (p:Q.rat)
  : Lemma (B.cle (B.rat_cut (Q.neg p)) (copp (B.rat_cut p)))
  = introduce forall (t:Q.rat). B.rat_cut (Q.neg p) t ==> copp (B.rat_cut p) t
    with introduce _ ==> _ with begin
      B.rat_cut_mem (Q.neg p) t;
      qneg_lt t p;
      let r = Q.mid Q.zero (Q.sub (Q.neg t) p) in
      qsub_lt (Q.neg t) p p;
      Q.add_neg p;
      Q.mid_spec Q.zero (Q.sub (Q.neg t) p);
      qsub_add (Q.neg t) p;
      Q.lt_add_r r (Q.sub (Q.neg t) p) p;
      Q.add_comm r p;
      Q.lt_add_r (Q.add p r) (Q.neg t) (Q.neg r);
      Q.add_assoc p r (Q.neg r);
      Q.add_neg r;
      Q.add_zero p;
      qneg_add t r;
      B.rat_cut_mem p (Q.neg (Q.add t r));
      Q.lt_asym p (Q.neg (Q.add t r));
      introduce exists (r2:Q.rat).
          Q.lt Q.zero r2 /\ ~(B.rat_cut p (Q.neg (Q.add t r2)))
      with r and ()
    end

let rat_opp_sub' (p:Q.rat)
  : Lemma (B.cle (copp (B.rat_cut p)) (B.rat_cut (Q.neg p)))
  = introduce forall (t:Q.rat). copp (B.rat_cut p) t ==> B.rat_cut (Q.neg p) t
    with introduce _ ==> _ with
      eliminate exists (r:Q.rat).
          Q.lt Q.zero r /\ ~(B.rat_cut p (Q.neg (Q.add t r)))
      with begin
        B.rat_cut_mem p (Q.neg (Q.add t r));
        qneg_add t r;
        qneg_lt_zero' r;
        Q.lt_add_r (Q.neg r) Q.zero (Q.neg t);
        qadd_zero_l (Q.neg t);
        Q.add_comm (Q.neg t) (Q.neg r);
        Q.lt_total p (Q.neg (Q.add t r));
        introduce Q.lt p (Q.neg (Q.add t r)) ==> Q.lt p (Q.neg t)
        with Q.lt_trans p (Q.neg (Q.add t r)) (Q.neg t);
        qneg_lt t p;
        B.rat_cut_mem (Q.neg p) t
      end

let rat_opp (p:Q.rat)
  : Lemma (B.rat_cut (Q.neg p) == copp (B.rat_cut p))
  = rat_opp_sub p; rat_opp_sub' p;
    B.cle_antisym (B.rat_cut (Q.neg p)) (copp (B.rat_cut p))
