module IfaceNoSmtLeak

(* An assumed `val` of the interface --- in particular the SMT axiom of a
   lemma with an SMTPat --- must not be visible while checking the
   implementation. Otherwise the implementation could prove [use_it] from
   [leaky], and [leaky] from [use_it], a cyclic proof of [False]. *)

val q : int -> prop

val use_it (x:int) : Lemma (q x)

val leaky (x:int) : Lemma (q x) [SMTPat (q x)]
