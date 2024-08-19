module Misc.Norm2

(* During PR https://github.com/FStarLang/FStar/pull/3385, this once
triggered a failwith in the normalizer due to not respecting erase_universes. *)

open FStar.Mul

type comm_monoid (t:Type) = {
  one: t;
}

[@(strict_on_arguments [3])]
let pow (#t:Type) (k:comm_monoid t) (x:t) (n:nat) : t =
  x

assume
val lemma_pow_mul: #t:Type -> k:comm_monoid t -> x:t -> n:nat -> m:nat ->
  Lemma (pow k x m == pow k x m)
