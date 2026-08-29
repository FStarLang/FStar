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
module FStar.Rational

open FStar.Rational.Gcd

module L = FStar.Math.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

let pmul a b = L.pos_times_pos_is_pos a b; a * b

type frac = { n : int; d : pos }

let rat = q:frac{ reduced q.n q.d }

let num q = q.n
let den q = q.d

let mk (n:int) (d:pos) : rat =
  reduce_ok n d;
  let g = gcd n d in
  { n = n / g; d = d / g }

let frac_eta (q:frac) : Lemma ({ n = q.n; d = q.d } == q) =
  match q with | { n = _; d = _ } -> ()

(**** Representation lemmas *)

let rearr_cross (a g b:int) : Lemma (a * (g * b) == (g * a) * b) = ()

let mk_num_den (q:rat) : Lemma (mk (num q) (den q) == q) =
  let g = gcd q.n q.d in
  assert (g == 1);   // reduced q.n q.d
  frac_eta q

let num_den_reduced (q:rat) : Lemma (num q == 0 ==> den q == 1) =
  introduce num q == 0 ==> den q == 1
  with gcd_zero q.d

let eq_cross (p q:rat)
  : Lemma (p == q <==> num p * den q == num q * den p)
  = introduce num p * den q == num q * den p ==> p == q
    with begin
      den_eq p.n p.d q.n q.d;             // p.d == q.d
      L.lemma_cancel_mul p.n q.n p.d;     // p.n == q.n
      frac_eta p;
      frac_eta q
    end

let mk_cross (n:int) (d:pos)
  : Lemma (num (mk n d) * d == n * den (mk n d))
  = reduce_ok n d;
    let g = gcd n d in
    let a = n / g in
    let b = d / g in
    // num (mk n d) = a, den (mk n d) = b; n = g*a, d = g*b
    rearr_cross a g b;   // a * (g * b) == (g * a) * b
    assert (a * d == a * (g * b));
    assert (n * b == (g * a) * b)

let r1 (a b d1 d2:int) : Lemma ((a*b)*(d1*d2) == (a*d1)*(b*d2)) = ()
let r2 (a b d1 d2:int) : Lemma ((a*b)*(d1*d2) == (a*d2)*(b*d1)) = ()
let r3 (n b1 b2 d2:int) : Lemma ((n*b1)*(b2*d2) == (n*d2)*(b1*b2)) = ()
let r4 (n b2 b1 d1:int) : Lemma ((n*b2)*(b1*d1) == (n*d1)*(b1*b2)) = ()

let mk_eq_int (n1 d1 n2 d2 a1 b1 a2 b2:int)
  : Lemma (requires d1>0 /\ d2>0 /\ b1>0 /\ b2>0 /\ a1*d1==n1*b1 /\ a2*d2==n2*b2)
          (ensures (a1*b2==a2*b1) <==> (n1*d2==n2*d1))
  = L.pos_times_pos_is_pos d1 d2;
    L.pos_times_pos_is_pos b1 b2;
    let x : pos = d1*d2 in
    let y : pos = b1*b2 in
    r1 a1 b2 d1 d2;
    r3 n1 b1 b2 d2;
    assert ((a1*b2)*x == (n1*d2)*y);
    r2 a2 b1 d1 d2;
    r4 n2 b2 b1 d1;
    assert ((a2*b1)*x == (n2*d1)*y);
    introduce a1*b2==a2*b1 ==> n1*d2==n2*d1
    with L.lemma_cancel_mul (n1*d2) (n2*d1) y;
    introduce n1*d2==n2*d1 ==> a1*b2==a2*b1
    with L.lemma_cancel_mul (a1*b2) (a2*b1) x

let mk_eq (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (mk n1 d1 == mk n2 d2 <==> n1 * d2 == n2 * d1)
  = let p = mk n1 d1 in
    let q = mk n2 d2 in
    mk_cross n1 d1;
    mk_cross n2 d2;
    eq_cross p q;
    mk_eq_int n1 d1 n2 d2 (num p) (den p) (num q) (den q)

(**** Embedding of the integers *)

let of_int (n:int) : rat = mk n 1

let of_int_num_den (n:int) : Lemma (num (of_int n) == n /\ den (of_int n) == 1) =
  reduced_den_one n   // gcd n 1 == 1, so n/1 == n and 1/1 == 1

let of_int_mk (n:int) : Lemma (of_int n == mk n 1) = ()

(**** Field operations *)

let add p q = mk (num p * den q + num q * den p) (pmul (den p) (den q))
let neg p = mk (- num p) (den p)
let mul p q = mk (num p * num q) (pmul (den p) (den q))

let inv p =
  if num p = 0 then zero
  else if num p > 0 then mk (den p) (num p)
  else mk (- (den p)) (- (num p))

(**** Order *)

let lt p q = num p * den q < num q * den p

(**** The mk congruences *)

let dist_l (u v w:int) : Lemma ((u+v)*w == u*w + v*w) = ()

let cross_step (a b d1 d2 n c:int)
  : Lemma (requires a*d1 == n*c)
          (ensures (a*b)*(d1*d2) == (n*d2)*(c*b))
  = r1 a b d1 d2;    // (a*b)*(d1*d2) == (a*d1)*(b*d2)
    r3 n c b d2      // (n*c)*(b*d2) == (n*d2)*(c*b)

let cross_step2 (a b d1 d2 n c:int)
  : Lemma (requires a*d2 == n*c)
          (ensures (a*b)*(d1*d2) == (n*d1)*(b*c))
  = r2 a b d1 d2;    // (a*b)*(d1*d2) == (a*d2)*(b*d1)
    r4 n c b d1      // (n*c)*(b*d1) == (n*d1)*(b*c)

let add_int (n1 d1 n2 d2 a1 b1 a2 b2:int)
  : Lemma (requires a1*d1==n1*b1 /\ a2*d2==n2*b2)
          (ensures (a1*b2+a2*b1)*(d1*d2) == (n1*d2+n2*d1)*(b1*b2))
  = cross_step a1 b2 d1 d2 n1 b1;    // (a1*b2)*(d1*d2) == (n1*d2)*(b1*b2)
    cross_step2 a2 b1 d1 d2 n2 b2;   // (a2*b1)*(d1*d2) == (n2*d1)*(b1*b2)
    dist_l (a1*b2) (a2*b1) (d1*d2);
    dist_l (n1*d2) (n2*d1) (b1*b2)

let mk_add (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (add (mk n1 d1) (mk n2 d2) == mk (n1 * d2 + n2 * d1) (pmul d1 d2))
  = let p = mk n1 d1 in
    let q = mk n2 d2 in
    mk_cross n1 d1;
    mk_cross n2 d2;
    add_int n1 d1 n2 d2 (num p) (den p) (num q) (den q);
    mk_eq (num p * den q + num q * den p) (pmul (den p) (den q))
          (n1 * d2 + n2 * d1) (pmul d1 d2)

let neg_int (a d n b:int)
  : Lemma (requires a*d==n*b) (ensures (-a)*d == (-n)*b)
  = L.neg_mul_left a d;
    L.neg_mul_left n b

let mk_neg (n:int) (d:pos)
  : Lemma (neg (mk n d) == mk (-n) d)
  = let p = mk n d in
    mk_cross n d;
    neg_int (num p) d n (den p);
    mk_eq (- num p) (den p) (-n) d

let rm1 (a1 a2 d1 d2:int) : Lemma ((a1*a2)*(d1*d2) == (a1*d1)*(a2*d2)) = ()
let rm2 (n1 b1 n2 b2:int) : Lemma ((n1*b1)*(n2*b2) == (n1*n2)*(b1*b2)) = ()

let mul_int (n1 d1 n2 d2 a1 b1 a2 b2:int)
  : Lemma (requires a1*d1==n1*b1 /\ a2*d2==n2*b2)
          (ensures (a1*a2)*(d1*d2) == (n1*n2)*(b1*b2))
  = rm1 a1 a2 d1 d2;
    rm2 n1 b1 n2 b2

let mk_mul (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (mul (mk n1 d1) (mk n2 d2) == mk (n1 * n2) (pmul d1 d2))
  = let p = mk n1 d1 in
    let q = mk n2 d2 in
    mk_cross n1 d1;
    mk_cross n2 d2;
    mul_int n1 d1 n2 d2 (num p) (den p) (num q) (den q);
    mk_eq (num p * num q) (pmul (den p) (den q)) (n1 * n2) (pmul d1 d2)

let lt_mul_pos_iff (a:pos) (b c:int)
  : Lemma (b*a < c*a <==> b < c)
  = introduce b < c ==> b*a < c*a
    with L.lemma_mult_lt_right a b c;
    introduce b*a < c*a ==> b < c
    with (if b < c then () else L.lemma_mult_le_right a c b)

let mk_lt_int (n1 d1 n2 d2 a1 b1 a2 b2:int)
  : Lemma (requires d1>0 /\ d2>0 /\ b1>0 /\ b2>0 /\ a1*d1==n1*b1 /\ a2*d2==n2*b2)
          (ensures (a1*b2 < a2*b1) <==> (n1*d2 < n2*d1))
  = L.pos_times_pos_is_pos d1 d2;
    L.pos_times_pos_is_pos b1 b2;
    let x : pos = d1*d2 in
    let y : pos = b1*b2 in
    r1 a1 b2 d1 d2;
    r3 n1 b1 b2 d2;
    assert ((a1*b2)*x == (n1*d2)*y);
    r2 a2 b1 d1 d2;
    r4 n2 b2 b1 d1;
    assert ((a2*b1)*x == (n2*d1)*y);
    lt_mul_pos_iff x (a1*b2) (a2*b1);
    lt_mul_pos_iff y (n1*d2) (n2*d1)

let mk_lt (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (lt (mk n1 d1) (mk n2 d2) <==> n1 * d2 < n2 * d1)
  = let p = mk n1 d1 in
    let q = mk n2 d2 in
    mk_cross n1 d1;
    mk_cross n2 d2;
    mk_lt_int n1 d1 n2 d2 (num p) (den p) (num q) (den q)

(**** Inverse *)

let inv_num_den (q:rat)
  : Lemma (requires q =!= zero) (ensures mul q (inv q) == one)
  = mk_num_den q;
    of_int_num_den 0;
    frac_eta zero;
    if num q = 0 then begin
      num_den_reduced q;
      frac_eta q  // q == {n=0;d=1} == zero, contradicting precondition
    end
    else if num q > 0 then begin
      assert (inv q == mk (den q) (num q));
      mk_mul (num q) (den q) (den q) (num q);
      of_int_mk 1;
      mk_eq (num q * den q) (pmul (den q) (num q)) 1 1
    end
    else begin
      assert (inv q == mk (- (den q)) (- (num q)));
      mk_mul (num q) (den q) (- (den q)) (- (num q));
      of_int_mk 1;
      mk_eq (num q * (- (den q))) (pmul (den q) (- (num q))) 1 1
    end

(**** Additive laws *)

let add_comm (p q:rat) : Lemma (add p q == add q p) =
  mk_num_den p; mk_num_den q;
  mk_add (num p) (den p) (num q) (den q);
  mk_add (num q) (den q) (num p) (den p);
  mk_eq (num p * den q + num q * den p) (pmul (den p) (den q))
        (num q * den p + num p * den q) (pmul (den q) (den p))

let t1 (a e g:int) : Lemma ((a*e)*g == a*(e*g)) = ()
let t2 (c b g:int) : Lemma ((c*b)*g == (c*g)*b) = ()
let t3 (f b e:int) : Lemma (f*(b*e) == (f*e)*b) = ()
let assoc_num (a b c e f g:int)
  : Lemma ((a*e+c*b)*g + f*(b*e) == a*(e*g) + (c*g+f*e)*b)
  = dist_l (a*e) (c*b) g;
    dist_l (c*g) (f*e) b;
    t1 a e g; t2 c b g; t3 f b e
let assoc_den (b e g:int) : Lemma ((b*e)*g == b*(e*g)) = ()

let add_assoc (p q r:rat) : Lemma (add (add p q) r == add p (add q r)) =
  let a = num p in let b = den p in
  let c = num q in let e = den q in
  let f = num r in let g = den r in
  mk_num_den p; mk_num_den q; mk_num_den r;
  mk_add a b c e;                       // add p q == mk (a*e+c*b) (b*e)
  mk_add c e f g;                       // add q r == mk (c*g+f*e) (e*g)
  mk_add (a*e+c*b) (pmul b e) f g;
  mk_add a b (c*g+f*e) (pmul e g);
  assoc_num a b c e f g;
  assoc_den b e g;
  mk_eq ((a*e+c*b)*g + f*(pmul b e)) (pmul (pmul b e) g)
        (a*(pmul e g) + (c*g+f*e)*b) (pmul b (pmul e g))

let add_zero (p:rat) : Lemma (add p zero == p) =
  mk_num_den p;
  of_int_mk 0;                          // zero == mk 0 1
  mk_add (num p) (den p) 0 1;
  mk_eq (num p * 1 + 0 * den p) (pmul (den p) 1) (num p) (den p)

let add_neg (p:rat) : Lemma (add p (neg p) == zero) =
  mk_num_den p;
  mk_neg (num p) (den p);               // neg p == mk (-(num p)) (den p)
  mk_add (num p) (den p) (- num p) (den p);
  of_int_mk 0;
  L.neg_mul_left (num p) (den p);
  mk_eq (num p * den p + (- num p) * den p) (pmul (den p) (den p)) 0 1

let neg_neg (p:rat) : Lemma (neg (neg p) == p) =
  mk_num_den p;
  mk_neg (num p) (den p);               // neg p == mk (-(num p)) (den p)
  mk_neg (- num p) (den p);             // neg (neg p) == mk (- - num p) (den p)
  mk_eq (- (- num p)) (den p) (num p) (den p)

(**** Multiplicative laws *)

let mul_comm (p q:rat) : Lemma (mul p q == mul q p) =
  mk_num_den p; mk_num_den q;
  mk_mul (num p) (den p) (num q) (den q);
  mk_mul (num q) (den q) (num p) (den p);
  mk_eq (num p * num q) (pmul (den p) (den q))
        (num q * num p) (pmul (den q) (den p))

let mul_assoc (p q r:rat) : Lemma (mul (mul p q) r == mul p (mul q r)) =
  let a = num p in let b = den p in
  let c = num q in let e = den q in
  let f = num r in let g = den r in
  mk_num_den p; mk_num_den q; mk_num_den r;
  mk_mul a b c e;
  mk_mul c e f g;
  mk_mul (a*c) (pmul b e) f g;
  mk_mul a b (c*f) (pmul e g);
  t1 a c f;                            // (a*c)*f == a*(c*f)
  assoc_den b e g;                     // (b*e)*g == b*(e*g)
  mk_eq ((a*c)*f) (pmul (pmul b e) g) (a*(c*f)) (pmul b (pmul e g))

let mul_one (p:rat) : Lemma (mul p one == p) =
  mk_num_den p;
  of_int_mk 1;
  mk_mul (num p) (den p) 1 1;
  mk_eq (num p * 1) (pmul (den p) 1) (num p) (den p)

let mul_zero (p:rat) : Lemma (mul p zero == zero) =
  mk_num_den p;
  of_int_mk 0;
  mk_mul (num p) (den p) 0 1;
  mk_eq (num p * 0) (pmul (den p) 1) 0 1

let mul_neg (p q:rat) : Lemma (mul (neg p) q == neg (mul p q)) =
  mk_num_den p; mk_num_den q;
  mk_neg (num p) (den p);
  mk_mul (- num p) (den p) (num q) (den q);
  mk_mul (num p) (den p) (num q) (den q);
  mk_neg (num p * num q) (pmul (den p) (den q));
  L.neg_mul_left (num p) (num q);
  mk_eq ((- num p) * num q) (pmul (den p) (den q))
        (- (num p * num q)) (pmul (den p) (den q))

(**** Distributivity *)

let scale_cross (k n d:int) : Lemma ((k*n)*d == n*(k*d)) = ()

let mk_scale (k:pos) (n:int) (d:pos)
  : Lemma (mk (k*n) (pmul k d) == mk n d)
  = scale_cross k n d;
    mk_eq (k*n) (pmul k d) n d

let dist_r (w u v:int) : Lemma (w*(u+v) == w*u + w*v) = ()
let m4 (a b c g:int) : Lemma ((a*c)*(b*g) == b*(a*(c*g))) = ()
let rd4 (b e g:int) : Lemma ((b*e)*(b*g) == b*(b*(e*g))) = ()

let dist_rn (a b c e f g:int)
  : Lemma ((a*c)*(b*g) + (a*f)*(b*e) == b*(a*(c*g+f*e)))
  = m4 a b c g;                 // (a*c)*(b*g) == b*(a*(c*g))
    m4 a b f e;                 // (a*f)*(b*e) == b*(a*(f*e))
    dist_r a (c*g) (f*e);       // a*(c*g+f*e) == a*(c*g) + a*(f*e)
    dist_r b (a*(c*g)) (a*(f*e))// b*(x+y) == b*x + b*y

let distrib (p q r:rat) : Lemma (mul p (add q r) == add (mul p q) (mul p r)) =
  let a = num p in let b = den p in
  let c = num q in let e = den q in
  let f = num r in let g = den r in
  mk_num_den p; mk_num_den q; mk_num_den r;
  mk_add c e f g;                          // add q r == mk (c*g+f*e) (e*g)
  mk_mul a b (c*g+f*e) (pmul e g);         // LHS == mk (a*(c*g+f*e)) (b*(e*g))
  mk_mul a b c e;                          // mul p q == mk (a*c) (b*e)
  mk_mul a b f g;                          // mul p r == mk (a*f) (b*g)
  mk_add (a*c) (pmul b e) (a*f) (pmul b g);// RHS == mk ((a*c)*(b*g)+(a*f)*(b*e)) ((b*e)*(b*g))
  let nd : pos = pmul b (pmul e g) in      // = b*(e*g), the LHS denominator
  dist_rn a b c e f g;                     // RHSnum == b*(a*(c*g+f*e))
  rd4 b e g;                               // RHSden == b*nd
  mk_scale b (a*(c*g+f*e)) nd              // mk (b*N) (pmul b nd) == mk N nd

let mul_eq_zero (p q:rat)
  : Lemma (mul p q == zero <==> (p == zero \/ q == zero))
  = mk_num_den p; mk_num_den q;
    mk_mul (num p) (den p) (num q) (den q);
    of_int_mk 0;
    mk_eq (num p * num q) (pmul (den p) (den q)) 0 1;
    mk_eq (num p) (den p) 0 1;
    mk_eq (num q) (den q) 0 1

(**** Order laws *)

let swp (x y z:int) : Lemma ((x*y)*z == (x*z)*y) = ()

let lt_irrefl (p:rat) : Lemma (~(lt p p)) = ()

let lt_trans_int (a b c e f g:int)
  : Lemma (requires b>0 /\ e>0 /\ g>0 /\ a*e<c*b /\ c*g<f*e)
          (ensures  a*g<f*b)
  = L.lemma_mult_lt_right g (a*e) (c*b);   // (a*e)*g < (c*b)*g
    L.lemma_mult_lt_right b (c*g) (f*e);   // (c*g)*b < (f*e)*b
    t2 c b g;                              // (c*b)*g == (c*g)*b
    swp a e g;                             // (a*e)*g == (a*g)*e
    swp f e b;                             // (f*e)*b == (f*b)*e
    lt_mul_pos_iff e (a*g) (f*b)

let lt_trans (p q r:rat) : Lemma (requires lt p q /\ lt q r) (ensures lt p r) =
  lt_trans_int (num p) (den p) (num q) (den q) (num r) (den r)

let lt_total (p q:rat) : Lemma (lt p q \/ p == q \/ lt q p) =
  eq_cross p q

let lt_asym (p q:rat) : Lemma (requires lt p q) (ensures ~(lt q p)) = ()

let mm1 (a g e:int) : Lemma ((a*g)*(e*g) == (a*e)*(g*g)) = ()
let mm2 (c g b:int) : Lemma ((c*g)*(b*g) == (c*b)*(g*g)) = ()
let seq (f e b g:int) : Lemma ((f*e)*(b*g) == (f*b)*(e*g)) = ()

let lt_add_r_int (a b c e f g:int)
  : Lemma (requires b>0 /\ e>0 /\ g>0)
          (ensures ((a*g+f*b)*(e*g) < (c*g+f*e)*(b*g)) <==> (a*e < c*b))
  = L.pos_times_pos_is_pos g g;
    let gg : pos = g*g in
    dist_l (a*g) (f*b) (e*g);   // (a*g+f*b)*(e*g) == (a*g)*(e*g)+(f*b)*(e*g)
    dist_l (c*g) (f*e) (b*g);   // (c*g+f*e)*(b*g) == (c*g)*(b*g)+(f*e)*(b*g)
    mm1 a g e;                  // (a*g)*(e*g) == (a*e)*gg
    mm2 c g b;                  // (c*g)*(b*g) == (c*b)*gg
    seq f e b g;                // (f*e)*(b*g) == (f*b)*(e*g)
    lt_mul_pos_iff gg (a*e) (c*b)

let lt_add_r (p q r:rat) : Lemma (lt (add p r) (add q r) <==> lt p q) =
  mk_lt (num p * den r + num r * den p) (pmul (den p) (den r))
        (num q * den r + num r * den q) (pmul (den q) (den r));
  lt_add_r_int (num p) (den p) (num q) (den q) (num r) (den r)

let lt_neg (p q:rat) : Lemma (lt (neg q) (neg p) <==> lt p q) =
  mk_num_den p; mk_num_den q;
  mk_neg (num p) (den p);
  mk_neg (num q) (den q);
  mk_lt (- num q) (den q) (- num p) (den p);
  L.neg_mul_left (num q) (den p);
  L.neg_mul_left (num p) (den q)

let hkm (x h y k:int) : Lemma ((x*h)*(y*k) == (x*y)*(h*k)) = ()

let lt_mul_pos_int (a b c e h k:int)
  : Lemma (requires b>0 /\ e>0 /\ h>0 /\ k>0)
          (ensures ((a*h)*(e*k) < (c*h)*(b*k)) <==> (a*e < c*b))
  = L.pos_times_pos_is_pos h k;
    let hk : pos = h*k in
    hkm a h e k;                 // (a*h)*(e*k) == (a*e)*hk
    hkm c h b k;                 // (c*h)*(b*k) == (c*b)*hk
    lt_mul_pos_iff hk (a*e) (c*b)

let lt_mul_pos (p q r:rat)
  : Lemma (requires lt zero r) (ensures lt (mul p r) (mul q r) <==> lt p q)
  = of_int_num_den 0;
    mk_lt (num p * num r) (pmul (den p) (den r))
          (num q * num r) (pmul (den q) (den r));
    lt_mul_pos_int (num p) (den p) (num q) (den q) (num r) (den r)

let mul_pos (p q:rat)
  : Lemma (requires lt zero p /\ lt zero q) (ensures lt zero (mul p q))
  = of_int_num_den 0;
    of_int_mk 0;
    mk_mul (num p) (den p) (num q) (den q);
    mk_lt 0 1 (num p * num q) (pmul (den p) (den q))

let inv_pos (p:rat)
  : Lemma (requires lt zero p) (ensures lt zero (inv p))
  = of_int_num_den 0;
    assert (inv p == mk (den p) (num p));
    of_int_mk 0;
    mk_lt 0 1 (den p) (num p)

(**** Integers, floor, Archimedes, density *)

let of_int_add (m n:int) : Lemma (of_int (m + n) == add (of_int m) (of_int n)) =
  of_int_mk m; of_int_mk n; of_int_mk (m+n);
  mk_add m 1 n 1;
  mk_eq (m*1 + n*1) (pmul 1 1) (m+n) 1

let of_int_mul (m n:int) : Lemma (of_int (m * n) == mul (of_int m) (of_int n)) =
  of_int_mk m; of_int_mk n; of_int_mk (m*n);
  mk_mul m 1 n 1;
  mk_eq (m*n) (pmul 1 1) (m*n) 1

let of_int_lt (m n:int) : Lemma (lt (of_int m) (of_int n) <==> m < n) =
  of_int_mk m; of_int_mk n;
  mk_lt m 1 n 1

let of_int_inj (m n:int) : Lemma (of_int m == of_int n <==> m == n) =
  of_int_mk m; of_int_mk n;
  mk_eq m 1 n 1

let floor (q:rat) : int = num q / den q

let floor_spec (q:rat)
  : Lemma (le (of_int (floor q)) q /\ lt q (of_int (floor q + 1)))
  = let a = num q in let b = den q in
    mk_num_den q;
    of_int_mk (floor q);
    of_int_mk (floor q + 1);
    L.lemma_div_mod a b;      // a == b*(a/b) + a%b
    L.lemma_mod_lt a b;       // 0 <= a%b < b
    mk_lt (floor q) 1 a b;    // lt (of_int (floor q)) q <==> (floor q)*b < a
    mk_eq (floor q) 1 a b;    // of_int (floor q) == q <==> (floor q)*b == a
    mk_lt a b (floor q + 1) 1 // lt q (of_int (floor q + 1)) <==> a < (floor q + 1)*b

let archimedean (q:rat) : Lemma (exists (n:nat). lt q (of_int n)) =
  let a = num q in let b = den q in
  mk_num_den q;
  let m : nat = if a <= 0 then 1 else a + 1 in
  of_int_mk m;
  mk_lt a b m 1;                    // lt q (of_int m) <==> a < m*b
  L.lemma_mult_le_left m 1 b;       // m*1 <= m*b  (since 1 <= b)
  introduce exists (n:nat). lt q (of_int n) with m and ()

let small_inv (eps:rat)
  : Lemma (requires lt zero eps) (ensures exists (n:pos). lt (mk 1 n) eps)
  = let a = num eps in let b = den eps in
    mk_num_den eps;
    of_int_num_den 0;               // 0 < a
    let m : pos = b + 1 in
    mk_lt 1 m a b;                  // lt (mk 1 m) eps <==> b < a*m
    L.lemma_mult_le_right m 1 a;    // 1*m <= a*m  (since 1 <= a)
    introduce exists (n:pos). lt (mk 1 n) eps with m and ()

let mid (p q:rat) : rat =
  mk (num p * den q + num q * den p) (pmul (pmul (den p) (den q)) 2)

let q1 (a b e:int) : Lemma (a*((b*e)*2) == (a*e)*b + (a*e)*b) = ()
let q2 (c b e:int) : Lemma (c*((b*e)*2) == (c*b)*e + (c*b)*e) = ()

let mid_lo (a b c e:int)
  : Lemma (requires b>0 /\ e>0)
          (ensures (a*((b*e)*2) < (a*e+c*b)*b) <==> (a*e < c*b))
  = q1 a b e;
    dist_l (a*e) (c*b) b;
    lt_mul_pos_iff b (a*e) (c*b)

let mid_hi (a b c e:int)
  : Lemma (requires b>0 /\ e>0)
          (ensures ((a*e+c*b)*e < c*((b*e)*2)) <==> (a*e < c*b))
  = dist_l (a*e) (c*b) e;
    q2 c b e;
    lt_mul_pos_iff e (a*e) (c*b)

let mid_spec (p q:rat)
  : Lemma (requires lt p q) (ensures lt p (mid p q) /\ lt (mid p q) q)
  = let a = num p in let b = den p in
    let c = num q in let e = den q in
    mk_num_den p; mk_num_den q;
    mk_lt a b (a*e+c*b) (pmul (pmul b e) 2);
    mk_lt (a*e+c*b) (pmul (pmul b e) 2) c e;
    mid_lo a b c e;
    mid_hi a b c e

let below (q:rat) : r:rat{lt r q} =
  let a = num q in let b = den q in
  mk_num_den q;
  mk_lt (a - b) b a b;
  lt_mul_pos_iff b (a - b) a;
  mk (a - b) b

let above (q:rat) : r:rat{lt q r} =
  let a = num q in let b = den q in
  mk_num_den q;
  mk_lt a b (a + b) b;
  lt_mul_pos_iff b a (a + b);
  mk (a + b) b
