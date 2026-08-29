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
module FStar.Real.Ordered

open FStar.Real.Dedekind

module Q = FStar.Rational
module ID = FStar.IndefiniteDescription

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(**** Order *)

let lt_asym (x y:real) : Lemma (requires lt x y) (ensures ~(lt y x))
  = lt_irrefl x;
    introduce lt y x ==> False with lt_trans x y x

let not_lt (x y:real) : Lemma (~(lt x y) <==> le y x)
  = lt_irrefl x; lt_irrefl y; lt_total x y;
    introduce lt y x ==> ~(lt x y) with lt_asym y x;
    introduce lt x y ==> ~(le y x) with lt_asym x y

let le_refl (x:real) : Lemma (le x x) = ()

let le_trans (x y z:real)
  : Lemma (requires le x y /\ le y z) (ensures le x z)
  = introduce (lt x y /\ lt y z) ==> lt x z with lt_trans x y z

let lt_le_trans (x y z:real)
  : Lemma (requires lt x y /\ le y z) (ensures lt x z)
  = introduce lt y z ==> lt x z with lt_trans x y z

let le_lt_trans (x y z:real)
  : Lemma (requires le x y /\ lt y z) (ensures lt x z)
  = introduce lt x y ==> lt x z with lt_trans x y z

let le_antisym (x y:real)
  : Lemma (requires le x y /\ le y x) (ensures x == y)
  = introduce (lt x y /\ lt y x) ==> x == y with lt_asym x y

(**** Additive group *)

let add_zero_l (x:real) : Lemma (add zero x == x)
  = add_comm zero x; add_zero x

let add_opp_l (x:real) : Lemma (add (opp x) x == zero)
  = add_comm (opp x) x; add_opp x

let add_cancel (x y z:real) : Lemma (add x z == add y z <==> x == y)
  = add_assoc x z (opp z); add_assoc y z (opp z);
    add_opp z; add_zero x; add_zero y

let opp_opp (x:real) : Lemma (opp (opp x) == x)
  = add_opp (opp x);
    add_comm (opp x) (opp (opp x));
    add_opp x;
    add_cancel (opp (opp x)) x (opp x)

let opp_zero () : Lemma (opp zero == zero)
  = add_opp zero; add_zero_l (opp zero)

/// [(a+b) + (c+d) == (a+c) + (b+d)]
let shuffle4 (a b c d:real)
  : Lemma (add (add a b) (add c d) == add (add a c) (add b d))
  = add_assoc a b (add c d);
    add_assoc b c d; add_comm b c; add_assoc c b d;
    add_assoc a c (add b d)

let opp_add (x y:real) : Lemma (opp (add x y) == add (opp x) (opp y))
  = shuffle4 (opp x) (opp y) x y;
    add_opp_l x; add_opp_l y; add_zero zero;
    add_opp_l (add x y);
    add_cancel (add (opp x) (opp y)) (opp (add x y)) (add x y)

let sub_self (x:real) : Lemma (sub x x == zero) = add_opp x

let sub_add (x y:real) : Lemma (add (sub x y) y == x)
  = add_assoc x (opp y) y; add_opp_l y; add_zero x

let add_sub (x y:real) : Lemma (sub (add x y) y == x)
  = add_assoc x y (opp y); add_opp y; add_zero x

let lt_add_l (x y z:real) : Lemma (lt (add z x) (add z y) <==> lt x y)
  = lt_add_r x y z; add_comm z x; add_comm z y

let le_add_r (x y z:real) : Lemma (le (add x z) (add y z) <==> le x y)
  = lt_add_r x y z; add_cancel x y z

let lt_sub (x y:real) : Lemma (lt x y <==> lt zero (sub y x))
  = lt_add_r zero (sub y x) x; add_zero_l x; sub_add y x

let le_sub (x y:real) : Lemma (le x y <==> le zero (sub y x))
  = le_add_r zero (sub y x) x; add_zero_l x; sub_add y x

let lt_opp (x y:real) : Lemma (lt (opp y) (opp x) <==> lt x y)
  = lt_add_r (opp y) (opp x) (add x y);
    add_comm (opp y) (add x y);
    add_assoc x y (opp y); add_opp y; add_zero x;
    add_assoc (opp x) x y; add_opp_l x; add_zero_l y

let lt_add_compat (a b c d:real)
  : Lemma (requires lt a b /\ le c d) (ensures lt (add a c) (add b d))
  = lt_add_r a b c;
    le_add_r c d b; add_comm c b; add_comm d b;
    lt_le_trans (add a c) (add b c) (add b d)

(**** Multiplication *)

let mul_zero_l (x:real) : Lemma (mul zero x == zero)
  = mul_comm zero x; mul_zero x

let mul_one_l (x:real) : Lemma (mul one x == x)
  = mul_comm one x; mul_one x

let distrib_r (x y z:real) : Lemma (mul (add x y) z == add (mul x z) (mul y z))
  = mul_comm (add x y) z; distrib z x y; mul_comm z x; mul_comm z y

let mul_opp (x y:real) : Lemma (mul (opp x) y == opp (mul x y))
  = distrib_r (opp x) x y; add_opp_l x; mul_zero_l y;
    add_opp_l (mul x y);
    add_cancel (mul (opp x) y) (opp (mul x y)) (mul x y)

let mul_opp_r (x y:real) : Lemma (mul x (opp y) == opp (mul x y))
  = mul_comm x (opp y); mul_opp y x; mul_comm y x

let mul_sub (x y z:real) : Lemma (mul x (sub y z) == sub (mul x y) (mul x z))
  = distrib x y (opp z); mul_opp_r x z

let mul_sub_r (x y z:real) : Lemma (mul (sub x y) z == sub (mul x z) (mul y z))
  = distrib_r x (opp y) z; mul_opp y z

let mul_pos (x y:real)
  : Lemma (requires lt zero x /\ lt zero y) (ensures lt zero (mul x y))
  = lt_mul_pos zero x y; mul_zero_l y

let mul_nonneg (x y:real)
  : Lemma (requires le zero x /\ le zero y) (ensures le zero (mul x y))
  = mul_zero_l y; mul_zero x;
    introduce (lt zero x /\ lt zero y) ==> lt zero (mul x y)
    with mul_pos x y

let le_mul_pos (x y z:real)
  : Lemma (requires lt zero z) (ensures le (mul x z) (mul y z) <==> le x y)
  = lt_mul_pos x y z; lt_mul_pos y x z; lt_total x y;
    lt_irrefl (mul x z); lt_irrefl (mul y z)

let mul_lt_compat (a b c d:real)
  : Lemma (requires le zero a /\ lt a b /\ le zero c /\ lt c d)
          (ensures  lt (mul a c) (mul b d))
  = le_lt_trans zero a b;
    le_lt_trans zero c d;
    lt_mul_pos c d b; mul_comm c b; mul_comm d b;
    mul_zero a; mul_zero b; le_refl zero;
    introduce lt zero c ==> le (mul a c) (mul b c)
    with le_mul_pos a b c;
    le_lt_trans (mul a c) (mul b c) (mul b d)

let mul_le_compat (a b c d:real)
  : Lemma (requires le zero a /\ le a b /\ le zero c /\ le c d)
          (ensures  le (mul a c) (mul b d))
  = le_trans zero a b;
    mul_zero a; mul_zero b; mul_zero_l c; mul_zero_l d;
    le_refl zero; le_refl (mul b c);
    introduce lt zero c ==> le (mul a c) (mul b c)
    with le_mul_pos a b c;
    introduce lt zero b ==> le (mul c b) (mul d b)
    with le_mul_pos c d b;
    mul_comm c b; mul_comm d b;
    le_trans (mul a c) (mul b c) (mul b d)

(**** Squares *)

let sq_nonneg (x:real)
  : Lemma (requires le zero x) (ensures le zero (mul x x))
  = mul_nonneg x x

let sq_mono (x y:real)
  : Lemma (requires le zero x /\ lt x y) (ensures lt (mul x x) (mul y y))
  = mul_lt_compat x y x y

let sq_mono_rev (x y:real)
  : Lemma (requires le zero x /\ le zero y /\ lt (mul x x) (mul y y))
          (ensures  lt x y)
  = not_lt x y;
    introduce le y x ==> False
    with begin
      mul_le_compat y x y x;
      not_lt (mul x x) (mul y y)
    end

let sq_inj (x y:real)
  : Lemma (requires le zero x /\ le zero y /\ mul x x == mul y y)
          (ensures  x == y)
  = lt_total x y; lt_irrefl (mul x x);
    introduce lt x y ==> False with sq_mono x y;
    introduce lt y x ==> False with sq_mono y x

/// [two == one + one], needed before its own [val] appears in the interface.
let two_eq_aux () : Lemma (two == add one one)
  = Q.of_int_add 1 1; of_rat_add (Q.of_int 1) (Q.of_int 1)

let two_mul (a:real) : Lemma (mul two a == add a a)
  = two_eq_aux (); distrib_r one one a; mul_one_l a

let square_add (x y:real)
  : Lemma (mul (add x y) (add x y) ==
           add (add (mul x x) (mul two (mul x y))) (mul y y))
  = distrib_r x y (add x y);
    distrib x x y; distrib y x y;
    mul_comm y x;
    two_mul (mul x y);
    add_assoc (mul x x) (mul x y) (add (mul x y) (mul y y));
    add_assoc (mul x y) (mul x y) (mul y y);
    add_assoc (mul x x) (add (mul x y) (mul x y)) (mul y y)

let square_sub (x y:real)
  : Lemma (mul (sub x y) (sub x y) ==
           add (sub (mul x x) (mul two (mul x y))) (mul y y))
  = square_add x (opp y);
    mul_opp_r x y;
    mul_opp_r two (mul x y);
    mul_opp y (opp y);
    mul_opp_r y y;
    opp_opp (mul y y)

(**** Constants and inverses *)

let zero_lt_one () : Lemma (lt zero one)
  = Q.of_int_lt 0 1; of_rat_lt (Q.of_int 0) (Q.of_int 1)

let zero_lt_two () : Lemma (lt zero two)
  = Q.of_int_lt 0 2; of_rat_lt (Q.of_int 0) (Q.of_int 2)

let two_eq () : Lemma (two == add one one) = two_eq_aux ()

let one_ne_zero () : Lemma (one =!= zero)
  = Q.of_int_inj 1 0; of_rat_inj (Q.of_int 1) (Q.of_int 0)

let inv_pos (x:real)
  : Lemma (requires lt zero x) (ensures lt zero (inv x))
  = lt_irrefl zero; zero_lt_one (); one_ne_zero ();
    mul_inv x;
    lt_total zero (inv x);
    mul_zero x;
    lt_mul_pos (inv x) zero x; mul_zero_l x; mul_comm (inv x) x;
    lt_asym zero one

let inv_antitone (x y:real)
  : Lemma (requires lt zero x /\ lt x y) (ensures lt (inv y) (inv x))
  = lt_trans zero x y;
    inv_pos x; inv_pos y;
    mul_pos (inv x) (inv y);
    lt_mul_pos x y (mul (inv x) (inv y));
    lt_irrefl zero;
    mul_inv x; mul_inv y;
    mul_assoc x (inv x) (inv y);
    mul_comm (inv x) (inv y);
    mul_assoc y (inv y) (inv x);
    mul_one_l (inv y); mul_one_l (inv x)

let div_pos (x y:real)
  : Lemma (requires lt zero x /\ lt zero y) (ensures lt zero (div x y))
  = inv_pos y; mul_pos x (inv y)

let mul_div (x y:real)
  : Lemma (requires y =!= zero) (ensures mul (div x y) y == x)
  = mul_assoc x (inv y) y; mul_comm (inv y) y; mul_inv y; mul_one x

let div_lt_iff (x y z:real)
  : Lemma (requires lt zero z) (ensures lt (div x z) y <==> lt x (mul y z))
  = lt_irrefl zero; mul_div x z; lt_mul_pos (div x z) y z

let of_rat_inv (q:Q.rat)
  : Lemma (requires q =!= Q.zero) (ensures inv (of_rat q) == of_rat (Q.inv q))
  = Q.inv_num_den q;
    of_rat_inj q Q.zero;
    of_rat_mul q (Q.inv q);
    mul_inv (of_rat q);
    mul_one (of_rat (Q.inv q));
    mul_assoc (of_rat (Q.inv q)) (of_rat q) (inv (of_rat q));
    mul_comm (of_rat (Q.inv q)) (of_rat q);
    mul_one_l (inv (of_rat q))

(**** Density of the rationals; smallness *)

/// [1/(1/x) == x]
let inv_inv (x:real)
  : Lemma (requires x =!= zero /\ inv x =!= zero)
          (ensures inv (inv x) == x)
  = mul_inv x; mul_inv (inv x);
    mul_one x;
    mul_assoc x (inv x) (inv (inv x));
    mul_one_l (inv (inv x))

let small_rat (u:real)
  : Ghost Q.rat (requires lt zero u)
                (ensures fun q -> Q.lt Q.zero q /\ lt zero (of_rat q) /\
                               lt (of_rat q) u)
  = inv_pos u;
    lt_irrefl zero;
    archimedean (inv u);
    let n = ID.indefinite_description_ghost nat
              (fun n -> lt (inv u) (of_int n)) in
    (* n > 0, since 0 < 1/u < n *)
    lt_trans zero (inv u) (of_int n);
    of_rat_lt (Q.of_int 0) (Q.of_int n);
    Q.of_int_lt 0 n;
    (* 1/n < 1/(1/u) == u *)
    inv_antitone (inv u) (of_int n);
    inv_inv u;
    Q.inv_pos (Q.of_int n);
    Q.of_int_lt 0 n;
    Q.lt_irrefl Q.zero;
    of_rat_inj (Q.of_int n) Q.zero;
    Q.of_int_inj n 0;
    of_rat_inv (Q.of_int n);
    of_rat_lt Q.zero (Q.inv (Q.of_int n));
    Q.inv (Q.of_int n)

let small_pos (u:real)
  : Ghost real (requires lt zero u) (ensures fun e -> lt zero e /\ lt e u)
  = of_rat (small_rat u)

let small_pos2 (u v:real)
  : Ghost real (requires lt zero u /\ lt zero v)
               (ensures fun e -> lt zero e /\ lt e u /\ lt e v)
  = let e1 = small_pos u in
    let e2 = small_pos v in
    if ID.strong_excluded_middle (lt e1 e2)
    then (lt_trans e1 e2 v; e1)
    else (not_lt e1 e2; le_lt_trans e2 e1 u; e2)
