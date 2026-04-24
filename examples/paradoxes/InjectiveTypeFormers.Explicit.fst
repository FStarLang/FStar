module InjectiveTypeFormers.Explicit

let coerce (x:'a{'a == 'b}) : 'b = x
let lemma_of_squash (x:squash 'a) : Lemma 'a = ()

type i (f : Type u#1 -> Type u#0) : Type u#1 =
  | Mkinj : i f

[@@(expect_failure [19])]
let isInj (x:_) (y:_) (w:i x)
  : Lemma (i x == i y ==> x == y)
  = ()

assume
val isInj_admit (x:_) (y:_) (w:i x)
  : Lemma (i x == i y ==> x == y)

// With the prop refactoring (prop : Type0 opaque), the paradox below
// is no longer expressible because ~(a x) requires a x : prop,
// but a : Type u#1 -> Type u#0, not -> prop.
[@@(expect_failure [12])]
let pa (x:Type u#1) (a:(Type u#1 -> Type u#0)) =
  i a == x /\ ~(a x)
