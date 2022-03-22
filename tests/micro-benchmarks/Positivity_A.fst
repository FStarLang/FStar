module Positivity_A

//
//the interface Positivity_A.fsti specifies a strictly_positive annotation on a
//
[@@ expect_failure]
noeq
type t (a:Type0) : Type0 =
  | Mk : (a -> False) -> t a

noeq
type t (a:Type0) : Type0 =
  | Mk : a -> t a
