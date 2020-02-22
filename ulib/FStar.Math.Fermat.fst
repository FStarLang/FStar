module FStar.Math.Fermat

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Math.Euclid

/// Fermat's Little Theorem
///
/// The easiest is to prove it by induction from the Freshman's dream identity
///
///   pow (a + b) p % p = (pow a p + pow b p) % p
///
/// which follows from the Binomial Theorem
///
///   pow (a + b) n = sum_{i=0}^n (binomial n k * pow a (n - i) * pow b i)
///
/// which in turn can be proved by induction from Pascal's identity
///
///   binomial n k + binomial n (k - 1) = binomial (n + 1) k
///

#set-options "--fuel 1 --ifuel 0 --z3rlimit 20"

///
/// Pow
///

val pow: int -> nat -> int
let rec pow a k =
  if k = 0 then 1
  else a * pow a (k - 1)

val pow_zero (k:pos) : Lemma (pow 0 k == 0)
let rec pow_zero = function
  | 1 -> ()
  | k -> pow_zero (k - 1)

val pow_one (k:nat) : Lemma (pow 1 k == 1)
let rec pow_one = function
  | 0 -> ()
  | k -> pow_one (k - 1)

val pow_plus (a:int) (k m:nat): Lemma
  (ensures pow a (k + m) == pow a k * pow a m)
  (decreases k)
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

val factorial: nat -> pos
let rec factorial = function
  | 0 -> 1
  | n -> n * factorial (n - 1)

let ( ! ) n = factorial n

let binomial (n:nat) (k:nat{k <= n}) = !n / (!k * !(n - k))

val binomial_n (n:nat) : Lemma (binomial n n == 1)
let binomial_n n = ()

val binomial_0 (n:nat) : Lemma (binomial n 0 == 1)
let binomial_0 n = ()

val sum: a:nat -> b:nat{a <= b} 
  -> f:((i:nat{a <= i /\ i <= b}) -> int) -> Tot int (decreases (b - a))
let rec sum a b f =
  if a = b then f a else f a + sum (a + 1) b f

val sum_extensionality (a:nat) (b:nat{a <= b}) 
  (f:(i:nat{a <= i /\ i <= b}) -> int) 
  (g:(i:nat{a <= i /\ i <= b}) -> int) : Lemma
  (requires forall (i:nat{a <= i /\ i <= b}). f i == g i)
  (ensures  sum a b f == sum a b g)
  (decreases (b - a))
  [SMTPat (sum a b f == sum a b g)]
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
      (fun (i:nat{a <= i /\ i <= b}) -> k) (fun (i:nat{a + 1 <= i /\ i <= b}) -> k)
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

val sum_mod (a:nat) (b:nat{a <= b}) 
  (f:(i:nat{a <= i /\ i <= b}) -> int) (n:pos) : Lemma
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

assume
val pascal (n:nat) (k:pos{k <= n}) : Lemma
  (binomial n k + binomial n (k - 1) = binomial (n + 1) k)

val binomial_theorem (a b:int) (n:nat) : Lemma
  (pow (a + b) n == sum 0 n (fun i -> binomial n i * pow a (n - i) * pow b i))
let rec binomial_theorem a b n =
  if n = 0 then ()
  else 
    calc (==) {
      pow (a + b) n;
      == { }
      (a + b) * pow (a + b) (n - 1);
      == { distributivity_add_left a b (pow (a + b) (n - 1)) }
      a * pow (a + b) (n - 1) + b * pow (a + b) (n - 1);
      == { binomial_theorem a b (n - 1) }
      a * sum 0 (n - 1) (fun i -> binomial (n - 1) i * pow a (n - 1 - i) * pow b i) +
      b * sum 0 (n - 1) (fun i -> binomial (n - 1) i * pow a (n - 1 - i) * pow b i);
      == { admit() }
      sum 0 n (fun i -> binomial n i * pow a (n - i) * pow b i);
    }

assume
val binomial_prime (p:pos{1 < p /\ is_prime p}) (i:pos{i < p}) : Lemma
  (binomial p i % p == 0)

val freshman_aux (p:pos{1 < p /\ is_prime p}) (a b:int) (i:pos{i < p}): Lemma
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

val freshman (p:pos{1 < p /\ is_prime p}) (a b:int) : Lemma 
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

val fermat_aux (p:pos{1 < p /\ is_prime p}) (a:pos{a < p}) : Lemma 
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

val fermat (p:pos{1 < p /\ is_prime p}) (a:int) : Lemma (pow a p % p == a % p)
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
      == { }
      (a % p) * pow (a % p) (p - 1) % p;
      == { lemma_mod_mul_distr_r (a % p) (pow (a % p) (p - 1)) p }
      (a % p) * (pow (a % p) (p - 1) % p) % p;
      == { fermat_aux p (a % p) }
      (a % p) * (1 % p) % p;
      == { small_mod 1 p; lemma_mod_twice a p }
      a % p;
    }
