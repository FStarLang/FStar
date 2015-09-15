module FStar.Constructive

type cand : Type -> Type -> Type =
  | Conj : #p1:Type -> #p2:Type -> h1:p1 -> h2:p2 -> cand p1 p2

type cor : Type -> Type -> Type =
  | IntroL : #p1:Type -> #p2:Type -> h:p1 -> cor p1 p2
  | IntroR : #p1:Type -> #p2:Type -> h:p2 -> cor p1 p2

type cimp (a:Type) (b:Type) = a -> Tot b

type ciff (a : Type) (b : Type) = cand (cimp a b) (cimp b a)

type cexists : #a:Type -> (a -> Type) -> Type =
  | ExIntro : #a:Type -> #p:(a -> Type) -> x:a -> h:(p x) -> cexists p

type cexists_type : (Type -> Type) -> Type =
  | ExTypeIntro : #p:(Type -> Type) -> t:Type -> h:(p t) -> cexists_type p

type ceq : #a:Type -> a -> a -> Type =
  | Refl : #a:Type -> x:a -> ceq x x

type ceq_type : Type -> Type -> Type =
  | ReflType : a:Type -> ceq_type a a

val ceq_eq : #a:Type -> #x:a -> #y:a -> h:(ceq x y) -> Lemma (x = y)
let ceq_eq x y p = ()

val ceq_congruence : #a:Type -> #b:Type -> #x:a -> #y:a -> ceq x y ->
                     f:(a->GTot b) -> GTot (ceq (f x) (f y))
let ceq_congruence (a:Type) (b:Type) x y h f = Refl (f x)

val ceq_symm : #a:Type -> #x:a -> #y:a -> ceq x y -> Tot (ceq y x)
let ceq_symm (a:Type) x y h = Refl x

val ceq_trans : #a:Type -> #x:a -> #y:a -> #z:a -> ceq x y -> ceq y z ->
                  Tot (ceq x z)
let ceq_trans (a:Type) x y z hxy hyz = Refl x

type ctrue : Type =
  | I : ctrue

(* hopefully this is an empty type *)
type cfalse : Type =

assume val cfalse_elim : #a:Type -> cfalse -> Tot a
(* can we make this work?
let cfalse_elim pf =
  match pf with
  | _ -> 76 (* silly, fails type checking *)
*)

type cnot (p:Type) = cimp p cfalse
