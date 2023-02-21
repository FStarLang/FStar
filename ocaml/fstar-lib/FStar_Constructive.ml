open Prims
type ('Ap1,'Ap2) cand =
  | Conj of 'Ap1* 'Ap2
let uu___is_Conj projectee = true
let __proj__Conj__item__h1 projectee =
  match projectee with | Conj (h1,h2) -> h1
let __proj__Conj__item__h2 projectee =
  match projectee with | Conj (h1,h2) -> h2
type ('Ap1,'Ap2) cor =
  | IntroL of 'Ap1
  | IntroR of 'Ap2
let uu___is_IntroL projectee =
  match projectee with | IntroL h -> true | uu____104 -> false
let __proj__IntroL__item__h projectee = match projectee with | IntroL h -> h
let uu___is_IntroR projectee =
  match projectee with | IntroR h -> true | uu____148 -> false
let __proj__IntroR__item__h projectee = match projectee with | IntroR h -> h
type ('Aa,'Ab) cimp = 'Aa -> 'Ab
type ('Aa,'Ab) ciff = (('Aa,'Ab) cimp,('Ab,'Aa) cimp) cand
type ('Aa,'Ap) cexists =
  | ExIntro of 'Aa* 'Ap
let uu___is_ExIntro projectee = true
let __proj__ExIntro__item__x projectee =
  match projectee with | ExIntro (x,h) -> x
let __proj__ExIntro__item__h projectee =
  match projectee with | ExIntro (x,h) -> h
type ('Aa,'Ax,'dummyV0) ceq =
  | Refl
let uu___is_Refl x uu____306 projectee = true
type ('Aa,'dummyV0) ceq_type =
  | ReflType
let uu___is_ReflType projectee = true
let eq_ind x p f y uu____369 = f
let ceq_eq x y h = ()
let ceq_congruence x y h f = Obj.magic ()
let ceq_symm x y h = Refl
let ceq_trans x y z hxy hyz = Refl
type ctrue =
  | I
let uu___is_I: ctrue -> Prims.bool = fun projectee  -> true
type cfalse
let cfalse_elim = Obj.magic (fun f  -> ())
let false_elim2 x = FStar_Pervasives.false_elim ()
let false_elim u = FStar_Pervasives.false_elim ()
type 'Ap cnot = ('Ap,cfalse) cimp
