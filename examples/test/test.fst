module Test0
abstract type t (x:int) = int

module Test
open Test0
abstract type t (x:bool) = int
abstract val foo : t true -> Lemma (requires True) (ensures True) [SMTPatT (t true)]
