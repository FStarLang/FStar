module FStar.Math.Fermat

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Math.Euclid

#set-options "--fuel 1 --ifuel 0 --z3rlimit 20"

///
/// Pow
///

val pow_zero (k:pos) : Lemma (ensures pow 0 k == 0) (decreases k)
let rec pow_zero k =
  match k with
  | 1 -> ()
  | _ -> pow_zero (k - 1)

val pow_one (k:nat) : Lemma (pow 1 k == 1)
let rec pow_one = function
  | 0 -> ()
  | k -> pow_one (k - 1)

val pow_plus (a:int) (k m:nat): Lemma (pow a (k + m) == pow a k * pow a m)
let rec pow_plus a k m =
  match k with
  | 0 -> ()
  | _ ->
    calc (==) {
      pow a (k + m);
      == { }
      a * pow a ((k + m) - 1);
      == { pow_plus a (k - 1) m }
      a * (pow a (k - 1) * pow a m);
      == { }
      pow a k * pow a m;
    }

val pow_mod (p:pos) (a:int) (k:nat) : Lemma (pow a k % p == pow (a % p) k % p)
let rec pow_mod p a k =
  if k = 0 then ()
  else
    calc (==) {
      pow a k % p;
      == { }
      a * pow a (k - 1) % p;
      == { lemma_mod_mul_distr_r a (pow a (k - 1)) p }
      (a * (pow a (k - 1) % p)) % p;
      == { pow_mod p a (k - 1) }
      (a * (pow (a % p) (k - 1) % p)) % p;
      == { lemma_mod_mul_distr_r a (pow (a % p) (k - 1)) p }
      a * pow (a % p) (k - 1) % p;
      == { lemma_mod_mul_distr_l a (pow (a % p) (k - 1)) p }
      (a % p * pow (a % p) (k - 1)) % p;
      == { }
      pow (a % p) k % p;
    }

///
/// Binomial theorem
///

val binomial (n k:nat) : nat
let rec binomial n k =
  match n, k with
  | _, 0 -> 1
  | 0, _ -> 0
  | _, _ -> binomial (n - 1) k + binomial (n - 1) (k - 1)

val binomial_0 (n:nat) : Lemma (binomial n 0 == 1)
let binomial_0 n = ()

val binomial_lt (n:nat) (k:nat{n < k}) : Lemma (binomial n k = 0)
let rec binomial_lt n k =
  match n, k with
  | _, 0 -> ()
  | 0, _ -> ()
  | _ -> binomial_lt (n - 1) k; binomial_lt (n - 1) (k - 1)

val binomial_n (n:nat) : Lemma (binomial n n == 1)
let rec binomial_n n =
  match n with
  | 0 -> ()
  | _ -> binomial_lt n (n + 1); binomial_n (n - 1)

val pascal (n:nat) (k:pos{k <= n}) : Lemma
  (binomial n k + binomial n (k - 1) = binomial (n + 1) k)
let pascal n k = ()

val factorial: nat -> pos
let rec factorial = function
  | 0 -> 1
  | n -> n * factorial (n - 1)

let ( ! ) n = factorial n

val binomial_factorial (m n:nat) : Lemma (binomial (n + m) n * (!n * !m) == !(n + m))
let rec binomial_factorial m n =
  match m, n with
  | 0, _ -> binomial_n n
  | _, 0 -> ()
  | _ ->
    let open FStar.Math.Lemmas in
    let reorder1 (a b c d:int) : Lemma (a * (b * (c * d)) == c * (a * (b * d))) =
      assert (a * (b * (c * d)) == c * (a * (b * d))) by (FStar.Tactics.CanonCommSemiring.int_semiring())
    in
    let reorder2 (a b c d:int) : Lemma (a * ((b * c) * d) == b * (a * (c * d))) =
      assert (a * ((b * c) * d) == b * (a * (c * d))) by (FStar.Tactics.CanonCommSemiring.int_semiring())
    in
    calc (==) {
      binomial (n + m) n * (!n * !m);
      == { pascal (n + m - 1) n }
      (binomial (n + m - 1) n + binomial (n + m - 1) (n - 1)) * (!n * !m);
      == { addition_is_associative n m (-1) }
      (binomial (n + (m - 1)) n + binomial (n + (m - 1)) (n - 1)) * (!n * !m);
      == { distributivity_add_left (binomial (n + (m - 1)) n)
                                   (binomial (n + (m - 1)) (n - 1))
                                   (!n * !m)
         }
      binomial (n + (m - 1)) n * (!n * !m) +
      binomial (n + (m - 1)) (n - 1) * (!n * !m);
      == { }
      binomial (n + (m - 1)) n * (!n * (m * !(m - 1))) +
      binomial ((n - 1) + m) (n - 1) * ((n * !(n - 1)) * !m);
      == { reorder1 (binomial (n + (m - 1)) n) (!n) m (!(m - 1));
           reorder2 (binomial ((n - 1) + m) (n - 1)) n (!(n - 1)) (!m)
         }
      m * (binomial (n + (m - 1)) n * (!n * !(m - 1))) +
      n * (binomial ((n - 1) + m) (n - 1) * (!(n - 1) * !m));
      == { binomial_factorial (m - 1) n; binomial_factorial m (n - 1) }
      m * !(n + (m - 1)) + n * !((n - 1) + m);
      == { }
      m * !(n + m - 1) + n * !(n + m - 1);
      == { }
      n * !(n + m - 1) + m * !(n + m - 1);
      == { distributivity_add_left m n (!(n + m - 1)) }
      (n + m) * !(n + m - 1);
      == { }
      !(n + m);
    }

val sum: a:nat -> b:nat{a <= b} -> f:((i:nat{a <= i /\ i <= b}) -> int)
  -> Tot int (decreases (b - a))
let rec sum a b f =
  if a = b then f a else f a + sum (a + 1) b f

val sum_extensionality (a:nat) (b:nat{a <= b}) (f g:(i:nat{a <= i /\ i <= b}) -> int) : Lemma
  (requires forall (i:nat{a <= i /\ i <= b}). f i == g i)
  (ensures  sum a b f == sum a b g)
  (decreases (b - a))
let rec sum_extensionality a b f g =
  if a = b then ()
  else sum_extensionality (a + 1) b f g

val sum_first (a:nat) (b:nat{a < b}) (f:(i:nat{a <= i /\ i <= b}) -> int) : Lemma
  (sum a b f == f a + sum (a + 1) b f)
let sum_first a b f = ()

val sum_last (a:nat) (b:nat{a < b}) (f:(i:nat{a <= i /\ i <= b}) -> int) : Lemma
  (ensures sum a b f == sum a (b - 1) f + f b)
  (decreases (b - a))
let rec sum_last a b f =
  if a + 1 = b then sum_first a b f
  else sum_last (a + 1) b f

val sum_const (a:nat) (b:nat{a <= b}) (k:int) : Lemma
  (ensures sum a b (fun i -> k) == k * (b - a + 1))
  (decreases (b - a))
let rec sum_const a b k =
  if a = b then ()
  else
    begin
    sum_const (a + 1) b k;
    sum_extensionality (a + 1) b
      (fun (i:nat{a <= i /\ i <= b}) -> k)
      (fun (i:nat{a + 1 <= i /\ i <= b}) -> k)
    end

val sum_scale (a:nat) (b:nat{a <= b}) (f:(i:nat{a <= i /\ i <= b}) -> int) (k:int) : Lemma
  (ensures k * sum a b f == sum a b (fun i -> k * f i))
  (decreases (b - a))
let rec sum_scale a b f k =
  if a = b then ()
  else
    begin
    sum_scale (a + 1) b f k;
    sum_extensionality (a + 1) b
      (fun (i:nat{a <= i /\ i <= b}) -> k * f i)
      (fun (i:nat{a + 1 <= i /\ i <= b}) -> k * f i)
    end

val sum_add (a:nat) (b:nat{a <= b}) (f g:(i:nat{a <= i /\ i <= b}) -> int) : Lemma
  (ensures sum a b f + sum a b g == sum a b (fun i -> f i + g i))
  (decreases (b - a))
let rec sum_add a b f g =
  if a = b then ()
  else
    begin
    sum_add (a + 1) b f g;
    sum_extensionality (a + 1) b
      (fun (i:nat{a <= i /\ i <= b}) -> f i + g i)
      (fun (i:nat{a + 1 <= i /\ i <= b}) -> f i + g i)
    end

val sum_shift (a:nat) (b:nat{a <= b}) (f:(i:nat{a <= i /\ i <= b}) -> int) : Lemma
  (ensures sum a b f == sum (a + 1) (b + 1) (fun (i:nat{a + 1 <= i /\ i <= b + 1}) -> f (i - 1)))
  (decreases (b - a))
let rec sum_shift a b f =
  if a = b then ()
  else
    begin
    sum_shift (a + 1) b f;
    sum_extensionality (a + 2) (b + 1)
      (fun (i:nat{a + 1 <= i /\ i <= b + 1}) -> f (i - 1))
      (fun (i:nat{a + 1 + 1 <= i /\ i <= b + 1}) -> f (i - 1))
    end

val sum_mod (a:nat) (b:nat{a <= b}) (f:(i:nat{a <= i /\ i <= b}) -> int) (n:pos) : Lemma
  (ensures sum a b f % n == sum a b (fun i -> f i % n) % n)
  (decreases (b - a))
let rec sum_mod a b f n =
  if a = b then ()
  else
    let g = fun (i:nat{a <= i /\ i <= b}) -> f i % n in
    let f' = fun (i:nat{a + 1 <= i /\ i <= b}) -> f i % n in
    calc (==) {
      sum a b f % n;
      == { sum_first a b f }
      (f a + sum (a + 1) b f) % n;
      == { lemma_mod_plus_distr_r (f a) (sum (a + 1) b f) n }
      (f a + (sum (a + 1) b f) % n) % n;
      == { sum_mod (a + 1) b f n; sum_extensionality (a + 1) b f' g  }
      (f a + sum (a + 1) b g % n) % n;
      == { lemma_mod_plus_distr_r (f a) (sum (a + 1) b g) n }
      (f a + sum (a + 1) b g) % n;
      == { lemma_mod_plus_distr_l (f a) (sum (a + 1) b g) n }
      (f a % n + sum (a + 1) b g) % n;
      == { }
      sum a b g % n;
    }

val binomial_theorem_aux (a b:int) (n:nat) (i:nat{1 <= i /\ i <= n - 1}) : Lemma
  (a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i) +
   b * (binomial (n - 1) (i - 1) * pow a (n - 1 - (i - 1)) * pow b (i - 1)) ==
   binomial n i * pow a (n - i) * pow b i)
let binomial_theorem_aux a b n i =
  let open FStar.Math.Lemmas in
  calc (==) {
    a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i) +
    b * (binomial (n - 1) (i - 1) * pow a (n - 1 - (i - 1)) * pow b (i - 1));
    == { }
    a * (binomial (n - 1) i * pow a ((n - i) - 1) * pow b i) +
    b * (binomial (n - 1) (i - 1) * pow a (n - i) * pow b (i - 1));
    == { _ by (FStar.Tactics.CanonCommSemiring.int_semiring()) }
    binomial (n - 1) i * ((a * pow a ((n - i) - 1)) * pow b i) +
    binomial (n - 1) (i - 1) * (pow a (n - i) * (b * pow b (i - 1)));
    == { assert (a * pow a ((n - i) - 1) == pow a (n - i)); assert (b * pow b (i - 1) == pow b i) }
    binomial (n - 1) i * (pow a (n - i) * pow b i) +
    binomial (n - 1) (i - 1) * (pow a (n - i) * pow b i);
    == { _ by (FStar.Tactics.CanonCommSemiring.int_semiring()) }
    (binomial (n - 1) i + binomial (n - 1) (i - 1)) * (pow a (n - i) * pow b i);
    == { pascal (n - 1) i }
    binomial n i * (pow a (n - i) * pow b i);
    == { paren_mul_right (binomial n i) (pow a (n - i)) (pow b i) }
    binomial n i * pow a (n - i) * pow b i;
  }

#push-options "--fuel 2"

val binomial_theorem (a b:int) (n:nat) : Lemma
  (pow (a + b) n == sum 0 n (fun i -> binomial n i * pow a (n - i) * pow b i))
let rec binomial_theorem a b n =
  if n = 0 then ()
  else
    if n = 1 then
      (binomial_n 1; binomial_0 1)
    else
    let reorder (a b c d:int) : Lemma (a + b + (c + d) == a + d + (b + c)) =
      assert (a + b + (c + d) == a + d + (b + c)) by (FStar.Tactics.CanonCommSemiring.int_semiring())
    in
    calc (==) {
      pow (a + b) n;
      == { }
      (a + b) * pow (a + b) (n - 1);
      == { distributivity_add_left a b (pow (a + b) (n - 1)) }
      a * pow (a + b) (n - 1) + b * pow (a + b) (n - 1);
      == { binomial_theorem a b (n - 1) }
      a * sum 0 (n - 1) (fun i -> binomial (n - 1) i * pow a (n - 1 - i) * pow b i) +
      b * sum 0 (n - 1) (fun i -> binomial (n - 1) i * pow a (n - 1 - i) * pow b i);
      == { sum_scale 0 (n - 1) (fun i -> binomial (n - 1) i * pow a (n - 1 - i) * pow b i) a;
           sum_scale 0 (n - 1) (fun i -> binomial (n - 1) i * pow a (n - 1 - i) * pow b i) b
         }
      sum 0 (n - 1) (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i)) +
      sum 0 (n - 1) (fun i -> b * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i));
      == { sum_first 0 (n - 1) (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i));
           sum_last  0 (n - 1) (fun i -> b * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i));
           sum_extensionality 1 (n - 1)
             (fun (i:nat{1 <= i /\ i <= n - 1}) -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i))
             (fun (i:nat{0 <= i /\ i <= n - 1}) -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i));
           sum_extensionality 0 (n - 2)
             (fun (i:nat{0 <= i /\ i <= n - 2}) -> b * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i))
             (fun (i:nat{0 <= i /\ i <= n - 1}) -> b * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i))}
      (a * (binomial (n - 0) 0 * pow a (n - 1 - 0) * pow b 0)) + sum 1 (n - 1) (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i)) +
      (sum 0 (n - 2) (fun i -> b * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i)) + b * (binomial (n - 1) (n - 1) * pow a (n - 1 - (n - 1)) * pow b (n - 1)));
      == { binomial_0 n; binomial_n (n - 1) }
      pow a n + sum 1 (n - 1) (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i)) +
      (sum 0 (n - 2) (fun i -> b * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i)) + pow b n);
      == { sum_shift 0 (n - 2) (fun i -> b * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i));
           sum_extensionality 1 (n - 1)
             (fun (i:nat{1 <= i /\ i <= n - 1}) -> (fun (i:nat{0 <= i /\ i <= n - 2}) -> b * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i)) (i - 1))
             (fun (i:nat{1 <= i /\ i <= n - 2 + 1}) -> b * (binomial (n - 1) (i - 1) * pow a (n - 1 - (i - 1)) * pow b (i - 1)))
           }
      pow a n + sum 1 (n - 1) (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i)) +
      (sum 1 (n - 1) (fun i -> b * (binomial (n - 1) (i - 1) * pow a (n - 1 - (i - 1)) * pow b (i - 1))) + pow b n);
      == { reorder (pow a n)
                   (sum 1 (n - 1) (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i)))
                   (sum 1 (n - 2 + 1) (fun i -> b * (binomial (n - 1) (i - 1) * pow a (n - 1 - (i - 1)) * pow b (i - 1))))
                   (pow b n)
         }
      a * pow a (n - 1) + b * pow b (n - 1) +
      (sum 1 (n - 1) (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i)) +
       sum 1 (n - 1) (fun i -> b * (binomial (n - 1) (i - 1) * pow a (n - 1 - (i - 1)) * pow b (i - 1))));
      == { sum_add 1 (n - 1)
                   (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i))
                   (fun i -> b * (binomial (n - 1) (i - 1) * pow a (n - 1 - (i - 1)) * pow b (i - 1)))
         }
      pow a n + pow b n +
      (sum 1 (n - 1) (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i) +
                            b * (binomial (n - 1) (i - 1) * pow a (n - 1 - (i - 1)) * pow b (i - 1))));

      == { Classical.forall_intro (binomial_theorem_aux a b n);
           sum_extensionality 1 (n - 1)
             (fun i -> a * (binomial (n - 1) i * pow a (n - 1 - i) * pow b i) +
                    b * (binomial (n - 1) (i - 1) * pow a (n - 1 - (i - 1)) * pow b (i - 1)))
             (fun i -> binomial n i * pow a (n - i) * pow b i)
      }
      pow a n + pow b n + sum 1 (n - 1) (fun i -> binomial n i * pow a (n - i) * pow b i);
      == { }
      pow a n + (sum 1 (n - 1) (fun i -> binomial n i * pow a (n - i) * pow b i) + pow b n);
      == { binomial_0 n; binomial_n n }
      binomial n 0 * pow a (n - 0) * pow b 0 +
      (sum 1 (n - 1) (fun i -> binomial n i * pow a (n - i) * pow b i) +
      binomial n n * pow a (n - n) * pow b n);
      == { sum_first 0 n (fun i -> binomial n i * pow a (n - i) * pow b i);
           sum_last  1 n (fun i -> binomial n i * pow a (n - i) * pow b i);
           sum_extensionality 1 n
             (fun (i:nat{0 <= i /\ i <= n}) -> binomial n i * pow a (n - i) * pow b i)
             (fun (i:nat{1 <= i /\ i <= n}) -> binomial n i * pow a (n - i) * pow b i);
           sum_extensionality 1 (n - 1)
             (fun (i:nat{1 <= i /\ i <= n}) -> binomial n i * pow a (n - i) * pow b i)
             (fun (i:nat{1 <= i /\ i <= n - 1}) -> binomial n i * pow a (n - i) * pow b i)
         }
      sum 0 n (fun i -> binomial n i * pow a (n - i) * pow b i);
    }

#pop-options

val factorial_mod_prime (p:int{is_prime p}) (k:pos{k < p}) : Lemma
  (requires !k % p = 0)
  (ensures False)
  (decreases k)
let rec factorial_mod_prime p k =
  if k = 0 then ()
  else
    begin
    euclid_prime p k !(k - 1);
    factorial_mod_prime p (k - 1)
    end

val binomial_prime (p:int{is_prime p}) (k:pos{k < p}) : Lemma
  (binomial p k % p == 0)
let binomial_prime p k =
  calc (==) {
    (p * !(p -1)) % p;
    == { FStar.Math.Lemmas.lemma_mod_mul_distr_l p (!(p - 1)) p }
    (p % p * !(p - 1)) % p;
    == { }
    (0 * !(p - 1)) % p;
    == { }
    0;
  };
  binomial_factorial (p - k) k;
  assert (binomial p k * (!k * !(p - k)) == p * !(p - 1));
  euclid_prime p (binomial p k) (!k * !(p - k));
  if (binomial p k % p <> 0) then
    begin
    euclid_prime p !k !(p - k);
    assert (!k % p = 0 \/ !(p - k) % p = 0);
    if !k % p = 0 then
      factorial_mod_prime p k
    else
      factorial_mod_prime p (p - k)
    end

val freshman_aux (p:int{is_prime p}) (a b:int) (i:pos{i < p}): Lemma
  ((binomial p i * pow a (p - i) * pow b i) % p == 0)
let freshman_aux p a b i =
  calc (==) {
    (binomial p i * pow a (p - i) * pow b i) % p;
    == { paren_mul_right (binomial p i) (pow a (p - i))  (pow b i) }
    (binomial p i * (pow a (p - i) * pow b i)) % p;
    == { lemma_mod_mul_distr_l (binomial p i) (pow a (p - i) * pow b i) p }
    (binomial p i % p * (pow a (p - i) * pow b i)) % p;
    == { binomial_prime p i }
    0;
  }

val freshman (p:int{is_prime p}) (a b:int) : Lemma
  (pow (a + b) p % p = (pow a p + pow b p) % p)
let freshman p a b =
  let f (i:nat{0 <= i /\ i <= p}) = binomial p i * pow a (p - i) * pow b i % p in
  Classical.forall_intro (freshman_aux p a b);
  calc (==) {
    pow (a + b) p % p;
    == { binomial_theorem a b p }
    sum 0 p (fun i -> binomial p i * pow a (p - i) * pow b i) % p;
    == { sum_mod 0 p (fun i -> binomial p i * pow a (p - i) * pow b i) p }
    sum 0 p f % p;
    == { sum_first 0 p f; sum_last 1 p f }
    (f 0 + sum 1 (p - 1) f + f p) % p;
    == { sum_extensionality 1 (p - 1) f (fun _ -> 0) }
    (f 0 + sum 1 (p - 1) (fun _ -> 0) + f p) % p;
    == { sum_const 1 (p - 1) 0 }
    (f 0 + f p) % p;
    == { }
    ((binomial p 0 * pow a p * pow b 0) % p +
     (binomial p p * pow a 0 * pow b p) % p) % p;
    == { binomial_0 p; binomial_n p; small_mod 1 p }
    (pow a p % p + pow b p % p) % p;
    == { lemma_mod_plus_distr_l (pow a p) (pow b p % p) p;
         lemma_mod_plus_distr_r (pow a p) (pow b p) p }
    (pow a p + pow b p) % p;
  }

val fermat_aux (p:int{is_prime p}) (a:pos{a < p}) : Lemma
  (ensures pow a p % p == a % p)
  (decreases a)
let rec fermat_aux p a =
  if a = 1 then pow_one p
  else
    calc (==) {
      pow a p % p;
      == { }
      pow ((a - 1) + 1) p % p;
      == { freshman p (a - 1) 1 }
      (pow (a - 1) p + pow 1 p) % p;
      == { pow_one p }
      (pow (a - 1) p + 1) % p;
      == { lemma_mod_plus_distr_l (pow (a - 1) p) 1 p }
      (pow (a - 1) p % p + 1) % p;
      == { fermat_aux p (a - 1) }
      ((a - 1) % p + 1) % p;
      == { lemma_mod_plus_distr_l (a - 1) 1 p }
      ((a - 1) + 1) % p;
      == { }
      a % p;
    }

let fermat p a =
  if a % p = 0 then
    begin
    small_mod 0 p;
    pow_mod p a p;
    pow_zero p
    end
  else
    calc (==) {
      pow a p % p;
      == { pow_mod p a p }
      pow (a % p) p % p;
      == { fermat_aux p (a % p)  }
      (a % p) % p;
      == { lemma_mod_twice a p }
      a % p;
    }

val mod_mult_congr_aux (p:int{is_prime p}) (a b c:int) : Lemma
  (requires (a * c) % p = (b * c) % p /\ 0 <= b /\ b <= a /\ a < p /\ c % p <> 0)
  (ensures  a = b)
let mod_mult_congr_aux p a b c =
  let open FStar.Math.Lemmas in
  calc (==>) {
    (a * c) % p == (b * c) % p;
    ==> { mod_add_both (a * c) (b * c) (-b * c) p }
    (a * c - b * c) % p == (b * c - b * c) % p;
    ==> { swap_mul a c; swap_mul b c; lemma_mul_sub_distr c a b }
    (c * (a - b)) % p == (b * c - b * c) % p;
    ==> { small_mod 0 p; lemma_mod_mul_distr_l c (a - b) p }
    (c % p * (a - b)) % p == 0;
  };
  let r, s = FStar.Math.Euclid.bezout_prime p (c % p) in
  FStar.Math.Euclid.euclid p (c % p) (a - b) r s;
  small_mod (a - b) p

let mod_mult_congr p a b c =
  let open FStar.Math.Lemmas in
  lemma_mod_mul_distr_l a c p;
  lemma_mod_mul_distr_l b c p;
  if a % p = b % p then ()
  else if b % p < a % p then mod_mult_congr_aux p (a % p) (b % p) c
  else mod_mult_congr_aux p (b % p) (a % p) c

let fermat_alt p a =
  calc (==) {
    (pow a (p - 1) * a) % p;
    == { lemma_mod_mul_distr_r (pow a (p - 1)) a p;
         lemma_mod_mul_distr_l (pow a (p - 1)) (a % p) p
       }
     ((pow a (p - 1) % p) * (a % p)) % p;
    == { pow_mod p a (p - 1) }
    ((pow (a % p) (p - 1) % p) * (a % p)) % p;
    == { lemma_mod_mul_distr_l (pow (a % p) (p - 1)) (a % p) p }
    (pow (a % p) (p - 1) * (a % p)) % p;
    == { }
    pow (a % p) p % p;
    == { fermat p (a % p) }
    (a % p) % p;
    == { lemma_mod_twice a p }
    a % p;
    == { }
    (1 * a) % p;
  };
  small_mod 1 p;
  mod_mult_congr p (pow a (p - 1)) 1 a
