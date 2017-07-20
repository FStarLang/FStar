module FactIsOk

val factorial: x:nat -> Tot nat
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)

val mult_plus : n:nat{n>0} -> m:nat -> Lemma
      (ensures (n*m = m+((n-1)*m)))
let mult_plus n m = ()

val mult_plus_distr_r : n:nat -> m:nat -> p:nat -> Lemma
      (ensures (n + m) * p = (n * p) + (m * p))
let rec mult_plus_distr_r n m p =
  match n with
  | 0 -> ()
  | _ -> mult_plus_distr_r (n-1) m p; mult_plus (n+m) p; mult_plus n p

val mult_assoc : m:nat -> n:nat -> p:nat -> Lemma
      (ensures ((m * n) * p = m * (n * p)))
let rec mult_assoc m n p =
  match m with
  | 0 -> ()
  | _ -> mult_assoc (m-1) n p; mult_plus m n; mult_plus m (n*p);
         mult_plus_distr_r n ((m-1)*n) p

val fact: a:nat -> n:nat -> Tot nat (decreases n)
let rec fact a n =
  if n = 0 then a
  else fact (a * n) (n - 1)

val fact_is_ok: a:nat 
             -> n:nat 
             -> Lemma (ensures (fact a n = a * factorial n)) 
                      (decreases n)
let rec fact_is_ok a = function
  | 0 -> ()
  | n -> fact_is_ok (a * n) (n - 1); mult_assoc a n (factorial (n-1))

val fact_monotone : n:nat -> m:nat -> Lemma (requires (n <= m))
                                            (ensures (factorial n <= factorial m))
                                            (decreases m)
let rec fact_monotone n m =
  match m - n with
  | 0 -> ()
  | _ -> fact_monotone n (m-1)

// let tryx = fact_monotone 4 0 -- this fails

assume val fact_monotone' : n:nat -> m:nat ->
  Lemma (ensures (n <= m ==> factorial n <= factorial m))

let tryx' = fact_monotone' 4 0 // this works
