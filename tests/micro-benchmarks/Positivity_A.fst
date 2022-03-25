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

[@@ expect_failure]
noeq
type t1 (a:Type0 -> Type0) (b:Type0) =
  | Mk1 : a b -> t1 a b

noeq type t1 (a:Type0 -> Type0) (b:Type0) =
  | Mk1 : b -> t1 a b
