(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Parameters --admit_fsi Modulo --admit_fsi Bignum --verify_module ConcretePointLemmas;
    variables:MATH=../math_interfaces BIGNUM=../bignum_proof;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.fst FStar.SeqProperties.fst FStar.Array.fst FStar.Ghost.fst $BIGNUM/axiomatic.fst $BIGNUM/intlib.fst $BIGNUM/lemmas.fst $BIGNUM/parameters.fsti $BIGNUM/uint.fst $BIGNUM/bigint.fst $BIGNUM/eval.fst $MATH/definitions.fst $MATH/field.fst $BIGNUM/modulo.fsti $BIGNUM/bignum.fsti $MATH/curve.fst concrete_point.fst
  --*)

module ConcretePointLemmas

open ConcretePoint

val distinct_is_commutative: a:point -> b:point -> Lemma (Distinct a b <==> Distinct b a)
let distinct_is_commutative a b = ()

val distinct_is_commutative2: a:point -> b:point -> Lemma 
    (requires (Distinct b a))
    (ensures (Distinct a b))
let distinct_is_commutative2 a b = ()
