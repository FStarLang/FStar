module FStar.Enumerable

open FStar.Fin
open FStar.Bijection
open FStar.Injection

(* This class is for enumerable types, i.e. those in a bijection
   with a prefix of the natural numbers. *)
[@@erasable]
class enumerable (a:Type) = {
  _cardinal : nat;
  bij : a =~ fin _cardinal;
}

let cardinal (a:Type) {| d:enumerable a |} : GTot nat = d._cardinal

let to_nat (#a:Type) {| d : enumerable a |} (x:a) : GTot (fin (cardinal a #_)) =
  d.bij.right x

let of_nat (#a:Type) {| d : enumerable a |} (x:fin (cardinal a #_)) : GTot a =
  d.bij.left x

val to_of_pat (#a:Type) {| d:enumerable a |} (x : fin (cardinal a #_))
  : Lemma (to_nat (of_nat x) == x)
          [SMTPat (to_nat (of_nat x))]

val of_to_pat (#a:Type) {| d:enumerable a |} (x : a)
  : Lemma (of_nat (to_nat x) == x)
          [SMTPat (of_nat (to_nat x))]

instance enumerable_fin (n:nat) : enumerable (fin n) = {
  _cardinal = n;
  bij = bij_self _;
}

instance enumerable_prod (t1 t2 : Type)
  {| d1 : enumerable t1 |} {| d2 : enumerable t2 |}
  : enumerable (t1 & t2)
= {
  _cardinal = cardinal t1 #_ * cardinal t2 #_;
  bij = bij_prod d1.bij d2.bij `bij_comp` bij_nat_prod;
}

instance enumerable_sum (t1 t2 : Type)
  {| d1 : enumerable t1 |} {| d2 : enumerable t2 |}
  : enumerable (either t1 t2)
= {
  _cardinal = cardinal t1 #_ + cardinal t2 #_;
  bij = bij_either d1.bij d2.bij `bij_comp` bij_nat_sum _ _;
}

val bijection_implies_equal_cardinal
  (a b : Type) {| enumerable a, enumerable b |}
  (bij : bijection a b)
  : Lemma (cardinal a #_ == cardinal b #_)

val injection_implies_lte_cardinal
  (a b : Type) {| enumerable a, enumerable b |}
  (inj : injection a b)
  : Lemma (cardinal a #_ <= cardinal b #_)

val injection_equal_cardinal_implies_bijection
  (a b : Type) {| enumerable a, enumerable b |}
  (inj : injection a b)
  : Lemma (requires cardinal a #_ == cardinal b #_)
          (ensures  FStar.Functions.is_surj inj.f)

instance enumerable_unit : enumerable unit = {
  _cardinal = 1;
  bij = bij_unit_fin1;
}
