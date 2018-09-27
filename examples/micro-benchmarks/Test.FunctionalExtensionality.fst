module Test.FunctionalExtensionality
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality

(* To begin with, eta is provable *)
let eta_is_eq #a (#b:a -> Type) (f: (x:a -> b x)) : (f == (fun (x:a) -> f x)) =
  FStar.Squash.return_squash Refl

(** Illustrating the use of F.on_dom to restrict the domain of a
    function for use with the extensionality axiom *)

(* on a #b f: is a function whose domain is at most `a`

     One way to see it is that `on a #b f` introduces a
     lambda abstraction at type `a ^-> b`

     And the interpretation of `a ^-> b` is an arrow whose **maximal
     domain** is a.
*)
[@expect_failure]
let sub_fails (f: int ^-> int) : (nat ^-> int) = f
//this fails because `f`'s maximal domain is `int`,
//but we are trying to return it at a type that claims
//its maximal domain is just a nat

let sub_ok (f: int ^-> int) : nat -> int = f
//this is fine because the return type `nat -> int` makes no claims
//about `f`'s maximal domain.

(* Now for some examples of it in action *)
assume val f : int -> int
assume val g : int ^-> int
assume val h : nat ^-> int

let on_dom_transitivity_of_equality =
  assume (on int f == on int g); //H0
  assume (on nat g == on nat h); //H1
  //we know that f and g are equal on the int domain
  //and that g is equal to h only on g's nat sub-domain
  //We want to be able to show that f restricted to nat
  //is equal to h
  assert (on int f == g); //A0: g is restricted
  assert (on nat (on int f) == on nat g);//A1: congruence; adding `on nat` to both sides
  assert (on nat h == h); //A2: h is restricted
  assert (on nat (on int f) == h); //using H1, A1, A2
  assert (F.feq (on nat f) h) //`f` is pointwise equal to h on nat, but not provably equal


(* Now for a negative test *)

assume val f1 : int -> int
assume val g1 : nat ^-> int
[@expect_failure]
let unable_to_extend_equality_to_larger_domains_1 =
  assume (on nat f1 == on nat g1); //H0: f1 restricted to nat is equal to g1
  //But, trying to show that f1 is equal to g1 on int fails
  //in two ways:
  //1: this assertion is well-formed since (on int f1) can be
  //   subsumed to (nat -> int) (see sub_ok above).
  //   But the assertion is not provable, since we only know from H0
  //   that `on nat f1 == g1`
  //   not that `f1 == g1`.
  //   Without on `H0` is not expressible, and `f1` is incorrectly
  //   equated with `g1` on incompatibile domains.
  assert (eq2 #(nat -> int) (on int f1) g1)

[@expect_failure]
let unable_to_extend_equality_to_larger_domains_2 =
  //Same example as before, now failing in a different way
  assume (on nat f1 == on nat g1); //H0: f1 restricted to nat is equal to g1
  //But, trying to show that f1 is equal to g1 on int fails
  //in a different way
  //2: This time we try to expand the domain of `on nat f1` back
  //   to the domain of `f`, i.e., `int`. But this fails because of
  //   `sub_fails` (see above). And the assertion is not even
  //   well-formed.
  assert (eq2 #(nat -> int) (on int (on nat f1)) g1)

let shrinking_domains_ok =
  assume (on nat f1 == on nat g1); //H0: f1 restricted to nat is equal to g1
  //We can prove that their restrictions to a subdomain of nat (say pos) are equal
  //By:
  //1. Proving them pointwise equal on pos
  assert (F.feq (on pos (on nat f1)) (on pos g1));
  //2. Relying on the extensionality axiom to show that their restrictions are equal
  assert (on pos (on pos (on nat f1)) == (on pos (on pos g1)));
  //3. And idempotence of `on`
  assert (on pos (on nat f1) == on pos g1)


////////////////////////////////////////////////////////////////////////////////
//on_dom is abstract but the normalizer can reduce it, carefully.
//Note: `on_dom a f` is irreducible
//But, `on_dom a f x` reduces to `f x`.
////////////////////////////////////////////////////////////////////////////////
[@"opaque_to_smt"]
let f_1542 (x:int) :int = x + 1

let test_1542 () =
  assert_norm ((on int f_1542) 1 == 2);
  assert_norm (on int f_1542 2 == 3);
  assert_norm (F.on_domain int f_1542 3 == 4);
  assert_norm ((F.on_domain int f_1542) 4 == 5)

////////////////////////////////////////////////////////////////////////////////
//Iterating restricted function types is relatively straightforward
////////////////////////////////////////////////////////////////////////////////
let restricted_t_2_idem (#a #b #c:Type) (f: a ^-> b ^-> c)
  : Lemma (on a f == f)
  = ()

let on_2 (#a #b:Type) (#c:Type) (f:(a -> b -> Tot c))
  : (a ^-> b ^-> c)
  = on a (fun x -> on b (fun y -> f x y))

let on_2_interp (#a #b #c:Type) (f: (a -> b -> Tot c)) (x:a) (y:b)
    : Lemma (on_2 f x y == f x y)
    = ()
