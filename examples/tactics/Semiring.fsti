module Semiring

open FStar.Algebra.CommMonoid
open FStar.Tactics.CanonCommSemiring
open FStar.Tactics
open FStar.Mul

#set-options "--z3rlimit 40 --max_fuel 0 --max_ifuel 0"

val ring: eqtype

val zero: ring

val one: ring

val ( +. ) : a:ring -> b:ring -> ring

val ( *. ) : a:ring -> b:ring -> ring

val add_identity: a:ring -> Lemma (zero +. a == a)

val add_associativity: a:ring -> b:ring -> c:ring 
  -> Lemma (a +. b +. c == a +. (b +. c))

val add_commutativity: a:ring -> b:ring -> Lemma (a +. b == b +. a)

val mul_identity: a:ring -> Lemma (one *. a == a)

val mul_associativity: a:ring -> b:ring -> c:ring 
  -> Lemma (a *. b *. c == a *. (b *. c))

val mul_commutativity: a:ring -> b:ring -> Lemma (a *. b == b *. a)

unfold
let ring_add_cm : cm ring =
  CM zero ( +. ) add_identity add_associativity add_commutativity

unfold
let ring_mul_cm : cm ring =
  CM one ( *. ) mul_identity mul_associativity mul_commutativity

val mul_add_distr: distribute_left_lemma ring ring_add_cm ring_mul_cm

[@canon_attr]
let ring_cr : cr ring =
  CR (CM zero ( +. ) add_identity add_associativity add_commutativity)
     (CM one  ( *. ) mul_identity mul_associativity mul_commutativity)
     mul_add_distr

//#set-options "--tactic_trace_d 1"

let test (a b:int) =
  assert (a + b == b + a) by (canon_semiring int_cr)

let test1 (a b c:ring) =
  assert ((a +. b) *. c == a *. c +. b *. c) by (canon_semiring ring_cr)

let test2 (a b c:ring) =
  assert ((a +. b) *. c == b *. c +. a *. c) by (canon_semiring ring_cr)

let poly_update_repeat_blocks_multi_lemma2_simplify (a b c w r d:ring) : Lemma
  ((((a *. (r *. r)) +. c) *. (r *. r)) +. ((b *. (r *. r)) +. d) *. r ==
   (((((a *. (r *. r)) +. b *. r) +. c) *. r) +. d) *. r)
=
  assert (  
    (((a *. (r *. r)) +. c) *. (r *. r)) +. ((b *. (r *. r)) +. d) *. r ==
    ((a *. (r *. r) +. b *. r +. c) *. r +. d) *. r)   
  by (canon_semiring ring_cr)


let add_commutativity' (a b c d:ring) :
  Lemma (a +. b +. (c +. d) == a +. c +. b +. d)
  [SMTPat (a +. b +. (c +. d))]
=
  calc (==) {
    (a +. b) +. (c +. d);
    == { add_associativity a b (c +. d) }
    a +. (b +. (c +. d));
    == { add_associativity b c d }
    a +. ((b +. c) +. d);
    == { add_commutativity b c}
    a +. ((c +. b) +. d);
    == { add_associativity a (c +. b) d }
    (a +. (c +. b)) +. d;
    == { add_associativity a c b }
    (a +. c +. b) +. d;
  }

