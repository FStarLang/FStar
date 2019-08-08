module M

open FStar.Algebra.CommMonoid
open FStar.Tactics.CanonCommSemiring
open FStar.Tactics
open FStar.Mul

#set-options "--z3rlimit 40 --max_fuel 0 --max_ifuel 0"

val pow2_130: n:nat -> Lemma (
  match n with
  | 130 -> pow2 n - 5 == 1361129467683753853853498429727072845819
  | _ -> True)
  [SMTPat (pow2 n - 5)]
let pow2_130 n =
  match n with
  | 130 ->
    assert_norm (pow2 130 - 5 == 1361129467683753853853498429727072845819)
  | _ -> () 

let prime: pos = pow2 130 - 5

//val prime_value: unit -> Lemma (prime == 1361129467683753853853498429727072845819)
//let prime_value () = 
//  assert_norm (prime == 1361129467683753853853498429727072845819)

let ring = a:nat{a < prime}

let zero : ring = 0

let one : ring = 1

let ( +. ) a b = (a + b) % prime

let ( *. ) a b = (a * b) % prime

#push-options "--z3cliopt smt.arith.nl=false"

let add_identity a = ()

let add_associativity a b c = 
  calc (==) {
    a +. b +. c;
    == { }
    ((a + b) % prime + c) % prime;
    == { Math.Lemmas.lemma_mod_plus_distr_l (a + b) c prime }
    ((a + b) + c) % prime;
    == { }
    (a + (b + c)) % prime;
    == { Math.Lemmas.lemma_mod_plus_distr_r a (b + c) prime }
    a +. (b +. c);
  }

let add_commutativity a b = ()

let mul_identity a = ()

let mul_associativity a b c =
  calc (==) {
    a *. b *. c; 
    == { }
    (((a * b) % prime) * c) % prime;
    == { Math.Lemmas.lemma_mod_mul_distr_l (a * b) c prime }
    ((a * b) * c) % prime;
    == { Math.Lemmas.paren_mul_right a b c }
    (a * (b * c)) % prime;
    == { Math.Lemmas.lemma_mod_mul_distr_r a (b * c) prime }
    (a * ((b * c) % prime)) % prime;
    == { }
    a *. (b *. c);
  }
 
let mul_commutativity a b = ()

let mul_add_distr a b c =
  calc (==) {
    a *. (b +. c);
    == { }
    (a * (b +. c)) % prime;
    == { Math.Lemmas.lemma_mod_add_distr a (b + c) prime }
    (a * ((b + c) % prime)) % prime;
    == { Math.Lemmas.lemma_mod_mul_distr_r a (b + c) prime }
    (a * (b + c)) % prime;
    == { Math.Lemmas.distributivity_add_right a b c }
    (a * b + a * c) % prime;
    == { Math.Lemmas.lemma_mod_add_distr (a * b) (a * c) prime }
    (a * b + a *. c) % prime;
    == { }
    (a *. c + a * b) % prime;
    == { Math.Lemmas.lemma_mod_add_distr (a *. c) (a * b) prime }
    (a *. c + a *. b) % prime;
    == { }
    (a *. b + a *. c) % prime;
    == { }
    a *. b +. a *. c;
  }
