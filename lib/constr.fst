module Constructive

type cand : Type -> Type -> Type =
  | Conj : #a:Type -> #b:Type -> pa:a -> pb:b -> cand a b

type cor : Type -> Type -> Type =
  | IntroL : #a:Type -> #b:Type -> pa:a -> cor a b
  | IntroR : #a:Type -> #b:Type -> pb:b -> cor a b

type cimp (a:Type) (b:Type) = a -> Tot b

type ciff (a : Type) (b : Type) = cand (cimp a b) (cimp b a)

type cexists : #a:Type -> (a -> Type) -> Type =
  | ExIntro : #a:Type -> #p:(a -> Type) -> x:a -> p x -> cexists p

type cexists_type : (Type -> Type) -> Type =
  | ExTypeIntro : #p:(Type -> Type) -> t:Type -> p t -> cexists_type p

type ceq : #a:Type -> a -> a -> Type =
  | Eq : a:Type -> x:a -> ceq x x

val ceq_eq : #a:Type -> #x:a -> #y:a -> ceq x y -> Lemma (x = y)
let ceq_eq x y p = ()

type ctrue : Type =
  | I : ctrue

(* hopefully this is an empty type *)
type cfalse : Type =

(* can we make this work?
val cfalse_elim : cfalse -> 'a
let cfalse_elim pf =
  match pf with
  | _ -> 76 (* silly, fails type checking *)
*)
