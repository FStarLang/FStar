module Lib.Exponentiation.Definition

open FStar.Mul

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//we don't require to have an inverse element to be an abelian group
//so this is just commutative monoid
inline_for_extraction
class comm_monoid (t:Type) = {
  one: t;
  mul: t -> t -> t;
  lemma_one: a:t -> Lemma (mul a one == a);
  lemma_mul_assoc: a:t -> b:t -> c:t -> Lemma (mul (mul a b) c == mul a (mul b c));
  lemma_mul_comm: a:t -> b:t -> Lemma (mul a b == mul b a)
  }


inline_for_extraction
class abelian_group (t:Type) = {
  cm:comm_monoid t;
  inverse: t -> t;
  lemma_inverse: a:t -> Lemma (mul (inverse a) a == one)
  }

let sqr (#t:Type) (k:comm_monoid t) (a:t) : t = mul a a


[@(strict_on_arguments [3])]
let rec pow (#t:Type) (k:comm_monoid t) (x:t) (n:nat) : t =
  if n = 0 then one
  else mul x (pow k x (n - 1))

let pow_neg (#t:Type) (k:abelian_group t) (x:t) (n:int) : t =
  if n >= 0 then pow k.cm x n else k.inverse (pow k.cm x (- n))

// Properties of an inverse function
//---------------------------------

val lemma_inverse_one: #t:Type -> k:abelian_group t ->
  Lemma (inverse k.cm.one == k.cm.one)

val lemma_inverse_id: #t:Type -> k:abelian_group t -> a:t ->
  Lemma (inverse (inverse a) == a)

val lemma_inverse_mul: #t:Type -> k:abelian_group t -> a:t -> b:t ->
  Lemma (inverse (cm.mul a b) == cm.mul (inverse a) (inverse b))

// Properties of an exponentiation function
//--------------------------------------

val lemma_pow0: #t:Type -> k:comm_monoid t -> x:t -> Lemma (pow k x 0 == one)

val lemma_pow1: #t:Type -> k:comm_monoid t -> x:t -> Lemma (pow k x 1 == x)

val lemma_pow_unfold: #t:Type -> k:comm_monoid t -> x:t -> n:pos ->
  Lemma (mul x (pow k x (n - 1)) == pow k x n)


val lemma_pow_one: #t:Type -> k:comm_monoid t -> n:nat -> Lemma (pow k one n == one)

val lemma_pow_add: #t:Type -> k:comm_monoid t -> x:t -> n:nat -> m:nat ->
  Lemma (mul (pow k x n) (pow k x m) == pow k x (n + m))

val lemma_pow_mul: #t:Type -> k:comm_monoid t -> x:t -> n:nat -> m:nat ->
  Lemma (pow k (pow k x n) m == pow k x (n * m))

val lemma_pow_mul_base: #t:Type -> k:comm_monoid t -> a:t -> b:t -> n:nat ->
  Lemma (mul (pow k a n) (pow k b n) == pow k (mul a b) n)

val lemma_pow_double: #t:Type -> k:comm_monoid t -> x:t -> b:nat ->
  Lemma (pow k (mul x x) b == pow k x (b + b))


val lemma_inverse_pow: #t:Type -> k:abelian_group t -> x:t -> n:nat ->
  Lemma (inverse (pow cm x n) == pow cm (inverse x) n)

val lemma_pow_neg_one: #t:Type -> k:abelian_group t -> n:int ->
  Lemma (pow_neg k cm.one n == cm.one)

val lemma_pow_neg_add: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int ->
  Lemma (cm.mul (pow_neg k x n) (pow_neg k x m) == pow_neg k x (n + m))

val lemma_pow_neg_mul: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int ->
  Lemma (pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))

val lemma_pow_neg_mul_base: #t:Type -> k:abelian_group t -> a:t -> b:t -> n:int ->
  Lemma (cm.mul (pow_neg k a n) (pow_neg k b n) == pow_neg k (cm.mul a b) n)

val lemma_pow_neg_double: #t:Type -> k:abelian_group t -> x:t -> b:int ->
  Lemma (pow_neg k (cm.mul x x) b == pow_neg k x (b + b))
