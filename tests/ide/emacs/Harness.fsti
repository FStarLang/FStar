module Harness

val foo : nat -> prop
val always_foo a : Lemma (foo a) [SMTPat (foo a)]