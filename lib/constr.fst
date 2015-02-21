module Constructive

type cand : Type -> Type -> Type =
  | Conj : #a:Type -> #b:Type -> pa:a -> pb:b -> cand a b

type ciff (a : Type) (b : Type) = cand (a -> Tot b) (b -> Tot a)

type cexists : #a:Type -> (a -> Type) -> Type =
  | ExIntro : #a:Type -> #p:(a -> Type) -> x:a -> p x -> cexists p
