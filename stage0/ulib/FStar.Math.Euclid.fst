module FStar.Math.Euclid

open FStar.Mul
open FStar.Math.Lemmas

///
/// Auxiliary lemmas
///

val eq_mult_left (a b:int) : Lemma (requires a = b * a) (ensures a = 0 \/ b = 1)
let eq_mult_left a b = ()

val eq_mult_one (a b:int) : Lemma
  (requires a * b = 1)
  (ensures (a = 1 /\ b = 1) \/ (a = -1 /\ b = -1))
let eq_mult_one a b = ()

val opp_idempotent (a:int) : Lemma (-(-a) == a)
let opp_idempotent a = ()

val add_sub_l (a b:int) : Lemma (a - b + b = a)
let add_sub_l a b = ()

val add_sub_r (a b:int) : Lemma (a + b - b = a)
let add_sub_r a b = ()

///
/// Divides relation
///

let divides_reflexive a =
  Classical.exists_intro (fun q -> a = q * a) 1

let divides_transitive a b c =
  eliminate exists q1. b == q1 * a
  returns a `divides` c
  with _pf. 
    eliminate exists q2. c == q2 * b
    returns _
    with _pf2.
         introduce exists q. c == q * a
	 with (q1 * q2)
	 and ()


let divide_antisym a b =
  if a <> 0 then
    Classical.exists_elim (a = b \/ a = -b) (Squash.get_proof (exists q1. b = q1 * a))
      (fun q1 ->
        Classical.exists_elim (a = b \/ a = -b) (Squash.get_proof (exists q2. a = q2 * b))
          (fun q2 ->
            assert (b = q1 * a);
            assert (a = q2 * b);
            assert (b = q1 * (q2 * b));
            paren_mul_right q1 q2 b;
            eq_mult_left b (q1 * q2);
            eq_mult_one q1 q2))

let divides_0 a =
  Classical.exists_intro (fun q -> 0 = q * a) 0

let divides_1 a = ()

let divides_minus a b =
  Classical.exists_elim (a `divides` (-b))
    (Squash.get_proof (a `divides` b))
    (fun q -> Classical.exists_intro (fun q' -> -b = q' * a) (-q))

let divides_opp a b =
  Classical.exists_elim ((-a) `divides` b)
    (Squash.get_proof (a `divides` b))
    (fun q -> Classical.exists_intro (fun q' -> b = q' * (-a)) (-q))

let divides_plus a b d =
  Classical.exists_elim (d `divides` (a + b)) (Squash.get_proof (exists q1. a = q1 * d))
    (fun q1 ->
      Classical.exists_elim (d `divides` (a + b)) (Squash.get_proof (exists q2. b = q2 * d))
        (fun q2 ->
          assert (a + b = q1 * d + q2 * d);
          distributivity_add_left q1 q2 d;
          Classical.exists_intro (fun q -> a + b = q * d) (q1 + q2)))

let divides_sub a b d =
  Classical.forall_intro_2 (Classical.move_requires_2 divides_minus);
  divides_plus a (-b) d

let divides_mult_right a b d =
  Classical.exists_elim (d `divides` (a * b)) (Squash.get_proof (d `divides` b))
    (fun q ->
      paren_mul_right a q d;
      Classical.exists_intro (fun r -> a * b = r * d) (a * q))

///
/// GCD
///

let mod_divides a b =
  Classical.exists_intro (fun q -> a = q * b) (a / b)

let divides_mod a b =
  Classical.exists_elim (a % b = 0) (Squash.get_proof (b `divides` a))
    (fun q -> cancel_mul_div q b)

let is_gcd_unique a b c d =
  divide_antisym c d

let is_gcd_reflexive a = ()

let is_gcd_symmetric a b d = ()

let is_gcd_0 a = ()

let is_gcd_1 a = ()

let is_gcd_minus a b d =
  Classical.forall_intro_2 (Classical.move_requires_2 divides_minus);
  opp_idempotent b

let is_gcd_opp a b d =
  Classical.forall_intro_2 (Classical.move_requires_2 divides_minus);
  divides_opp d a;
  divides_opp d b

let is_gcd_plus a b q d =
  add_sub_r b (q * a);
  Classical.forall_intro_3 (Classical.move_requires_3 divides_plus);
  Classical.forall_intro_3 (Classical.move_requires_3 divides_mult_right);
  Classical.forall_intro_3 (Classical.move_requires_3 divides_sub)

///
/// Extended Euclidean algorithm
///

val is_gcd_for_euclid (a b q d:int) : Lemma
  (requires is_gcd b (a - q * b) d)
  (ensures  is_gcd a b d)
let is_gcd_for_euclid a b q d =
  add_sub_l a (q * b);
  is_gcd_plus b (a - q * b) q d

val egcd (a b u1 u2 u3 v1 v2 v3:int) : Pure (int & int & int)
  (requires v3 >= 0 /\
            u1 * a + u2 * b = u3 /\
            v1 * a + v2 * b = v3 /\
            (forall d. is_gcd u3 v3 d ==> is_gcd a b d))
  (ensures (fun (u, v, d) -> u * a + v * b = d /\ is_gcd a b d))
  (decreases v3)

let rec egcd a b u1 u2 u3 v1 v2 v3 =
  if v3 = 0 then
    begin
    divides_0 u3;
    (u1, u2, u3)
    end
  else
    begin
    let q = u3 / v3 in
    euclidean_division_definition u3 v3;
    assert (u3 - q * v3 = (q * v3 + u3 % v3) - q * v3);
    assert (q * v3 - q * v3 = 0);
    swap_add_plus_minus (q * v3) (u3 % v3) (q * v3);
    calc (==) {
      (u1 - q * v1) * a + (u2 - q * v2) * b;
      == { _ by (FStar.Tactics.Canon.canon()) }
      (u1 * a + u2 * b) - q * (v1 * a + v2 * b);
      == { }
      u3 - q * v3;
      == { lemma_div_mod u3 v3 }
      u3 % v3;
    };
    let u1, v1 = v1, u1 - q * v1 in
    let u2, v2 = v2, u2 - q * v2 in
    let u3' = u3 in
    let v3' = v3 in
    let u3, v3 = v3, u3 - q * v3 in
    (* proving the implication in the precondition *)
    introduce forall d. is_gcd v3' (u3' - q * v3') d ==> is_gcd u3' v3' d with
      introduce _ ==> _ with _.
        is_gcd_for_euclid u3' v3' q d;
    let r = egcd a b u1 u2 u3 v1 v2 v3 in
    r
    end

let euclid_gcd a b =
  if b >= 0 then
    egcd a b 1 0 a 0 1 b
  else (
    introduce forall d. is_gcd a (-b) d ==> is_gcd a b d
    with introduce _ ==> _
         with _pf. 
           (is_gcd_minus a b d;
            is_gcd_symmetric b a d);
    let res = egcd a b 1 0 a 0 (-1) (-b) in
    let _, _, d = res in
    assert (is_gcd a b d);
    res
  )

val is_gcd_prime_aux (p:int) (a:pos{a < p}) (d:int) : Lemma
  (requires is_prime p /\ d `divides` p /\ d `divides` a)
  (ensures  d = 1 \/ d = -1)
let is_gcd_prime_aux p a d = ()

val is_gcd_prime (p:int{is_prime p}) (a:pos{a < p}) : Lemma (is_gcd p a 1)
let is_gcd_prime p a =
  Classical.forall_intro_2 (Classical.move_requires_2 divides_minus);
  Classical.forall_intro (Classical.move_requires (is_gcd_prime_aux p a));
  assert (forall x. x `divides` p /\ x `divides` a ==> x = 1 \/ x = -1 /\ x `divides` 1)

let bezout_prime p a =
  let r, s, d = euclid_gcd p a in
  assert (r * p + s * a = d);
  assert (is_gcd p a d);
  is_gcd_prime p a;
  is_gcd_unique p a 1 d;
  assert (d = 1 \/ d = -1);
  assert ((-r) * p + (-s) * a == -(r * p + s * a)) by (FStar.Tactics.Canon.canon());
  if d = 1 then r, s else -r, -s

let euclid n a b r s =
  let open FStar.Math.Lemmas in
  calc (==) {
    b % n;
    == { distributivity_add_left (r * n) (s * a) b }
    (r * n * b + s * a * b) % n;
    == { paren_mul_right s a b }
    (r * n * b + s * (a * b)) % n;
    == { modulo_distributivity (r * n * b) (s * (a * b)) n }
    ((r * n * b) % n + s * (a * b) % n) % n;
    == { lemma_mod_mul_distr_r s (a * b) n }
    ((r * n * b) % n + s * ((a * b) % n) % n) % n;
    == { assert (a * b % n = 0) }
    ((r * n * b) % n + s * 0 % n) % n;
    == { assert (s * 0 == 0) }
    ((r * n * b) % n + 0 % n) % n;
    == { modulo_lemma 0 n }
    ((r * n * b) % n) % n;
    == { lemma_mod_twice (r * n * b) n }
    (r * n * b) % n;
    == { _ by (FStar.Tactics.Canon.canon ()) }
    (n * (r * b)) % n;
    == { lemma_mod_mul_distr_l n (r * b) n}
    n % n * (r * b) % n;
    == { assert (n % n = 0) }
    (0 * (r * b)) % n;
    == { assert (0 * (r * b) == 0) }
    0 % n;
    == { small_mod 0 n }
    0;
  }

let euclid_prime p a b =
  let ra, sa, da = euclid_gcd p a in
  let rb, sb, db = euclid_gcd p b in
  assert (is_gcd p a da);
  assert (is_gcd p b db);
  assert (da `divides` p);
  assert (da = 1 \/ da = -1 \/ da = p \/ da = -p);
  if da = 1 then
    euclid p a b ra sa
  else if da = -1 then
    begin
    assert ((-ra) * p + (-sa) * a == -(ra * p + sa * a)) by (FStar.Tactics.Canon.canon());
    euclid p a b (-ra) (-sa)
    end
  else if da = p then
    divides_mod a p
  else
    begin
    opp_idempotent p;
    divides_opp (-p) a;
    divides_mod a p
    end
