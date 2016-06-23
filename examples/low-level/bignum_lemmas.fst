module BignumLemmas

val modulo_lemma_1: x:nat -> s:pos{ x < s } -> Lemma (x % s = x)
let modulo_lemma_1 x s = ()
