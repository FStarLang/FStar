module Haseq

type t (a:Type) =
  | C: a -> t a

let foo _ = assert (hasEq (t int))
let bar _ = assert (hasEq (t nat))
