module FStar.Constructive

type cand (p1:Type) (p2:Type) : Type =
  | Conj : h1:p1 -> h2:p2 -> cand p1 p2

type cor (p1:Type) (p2:Type) : Type =
  | IntroL : h:p1 -> cor p1 p2
  | IntroR : h:p2 -> cor p1 p2

type cimp (a:Type) (b:Type) = a -> Tot b

type ciff (a:Type) (b:Type) = cand (cimp a b) (cimp b a)

type cexists (#a:Type) (p:a -> Type) : Type =
  | ExIntro : x:a -> h:p x -> cexists p

(* this currently fails because of ill-typed generated projector;
   it's a strong elimination so we can't soundly allow that anyway *)
(* type cexists_type (p:Type -> Type) : Type = *)
(*   | ExTypeIntro : t:Type -> h:p t -> cexists_type p *)

type ceq (#a:Type) (x:a) : a -> Type =
  | Refl : ceq #a x x

type ceq_type (a:Type) : Type -> Type =
  | ReflType : ceq_type a a

val eq_ind : #a:Type -> x:a -> p:(a -> Type) -> f:p x -> y:a -> e:ceq x y -> Tot (p y)
let eq_ind (a:Type) x (p:a -> Type) f y _ = f

val ceq_eq : #a:Type -> #x:a -> #y:a -> h:(ceq x y) -> Lemma (x = y)
let ceq_eq (#a:Type) x y h = ()

val ceq_congruence : #a:Type -> #b:Type -> #x:a -> #y:a -> ceq x y ->
                     f:(a -> GTot b) -> GTot (ceq (f x) (f y))
let ceq_congruence (a:Type) (b:Type) x y h f = Refl 

val ceq_symm : #a:Type -> #x:a -> #y:a -> ceq x y -> Tot (ceq y x)
let ceq_symm (a:Type) x y h = Refl

val ceq_trans : #a:Type -> #x:a -> #y:a -> #z:a -> ceq x y -> ceq y z -> Tot (ceq x z)
let ceq_trans (a:Type) x y z hxy hyz = Refl

type ctrue : Type =
  | I : ctrue

(* hopefully this is an empty type *)
type cfalse : Type =

val false_elim : #a:Type -> u:unit{false} -> Tot a
let rec false_elim (a:Type) () = false_elim ()

assume val cfalse_elim : #a:Type -> cfalse -> Tot a
(* This sholud work (see issue #70)
E.g. in Coq: False_rect = fun (P:Type) (f:False) => match f return P with end
let cfalse_elim f =
  match f with
  | _ -> 76 (* silly, fails type checking *)
*)

type cnot (p:Type) = cimp p cfalse
