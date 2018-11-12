module FStar.Constructive
type cand p1 p2 =
  | Conj : h1:p1 -> h2:p2 -> cand p1 p2

type cor p1 p2 =
  | IntroL : h:p1 -> cor p1 p2
  | IntroR : h:p2 -> cor p1 p2

type cimp a b = a -> Tot b

type ciff a b = cand (cimp a b) (cimp b a)

noeq type cexists (#a:Type) (p:a -> Type) = 
  | ExIntro : x:a -> h:p x -> cexists p

// val ex_intro_x : #a:Type -> #p:(a -> Type) -> projectee:cexists p -> Tot a
// let ex_intro_x #a #p = function
//   | ExIntro x _ -> x

type ceq (#a:Type) x : a -> Type =
  | Refl : ceq #a x x

type ceq_type (a:Type) : Type -> Type =
  | ReflType : ceq_type a a

val eq_ind : #a:Type -> x:a -> p:(a -> Type) -> f:p x -> y:a -> e:ceq x y -> Tot (p y)
let eq_ind #a x p f y _ = f

val ceq_eq : #a:Type{hasEq a} -> #x:a -> #y:a -> h:(ceq x y) -> Lemma (x = y)
let ceq_eq #a #x #y h = ()

val ceq_congruence : #a:Type -> #b:Type -> #x:a -> #y:a -> ceq x y ->
                     f:(a -> GTot b) -> GTot (ceq (f x) (f y))
let ceq_congruence #a #b #x #y h f = Refl #_ #(f x) //refuse to infer terms with non-Tot effect

val ceq_symm : #a:Type -> #x:a -> #y:a -> ceq x y -> Tot (ceq y x)
let ceq_symm #a #x #y h = Refl

val ceq_trans : #a:Type -> #x:a -> #y:a -> #z:a -> ceq x y -> ceq y z -> Tot (ceq x z)
let ceq_trans #a #x #y #z hxy hyz = Refl

type ctrue =
  | I : ctrue

(* hopefully this is an empty type *)
type cfalse : Type =

val cfalse_elim : #a:Type -> cfalse -> Tot a
let cfalse_elim #a f = match f with

val false_elim2 : #a:Type -> cfalse -> Tot a
let false_elim2 #a x = false_elim ()

val false_elim : #a:Type -> u:unit{false} -> Tot a
let false_elim #a u = false_elim ()

type cnot (p:Type) = cimp p cfalse
