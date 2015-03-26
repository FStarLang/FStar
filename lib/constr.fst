module Constructive

type cand : Type -> Type -> Type =
  | Conj : #a:Type -> #b:Type -> pa:a -> pb:b -> cand a b

type cimp (a:Type) (b:Type) = a -> Tot b

type ciff (a : Type) (b : Type) = cand (a -> Tot b) (b -> Tot a)

type cexists : #a:Type -> (a -> Type) -> Type =
  | ExIntro : #a:Type -> #p:(a -> Type) -> x:a -> p x -> cexists p

type cexists_type : (Type -> Type) -> Type =
  | ExTypeIntro : #p:(Type -> Type) -> t:Type -> p t -> cexists_type p

type ceq : #a:Type -> a -> a -> Type =
  | Eq : a:Type -> x:a -> ceq x x

(* can we make this work?
type cfalse : Type

val cfalse_elim : cfalse -> a:Type -> a
let cfalse_elim pf _ =
  match pf with
*)
