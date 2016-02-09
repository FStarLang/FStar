module Test
type s : nat -> Type

type t (i:nat) = 
  | Mk : s i -> t i
