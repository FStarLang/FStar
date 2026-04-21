module InjectiveTypeFormers.SMT
type i (f : Type u#1 -> Type u#0) : Type u#1 =
  | Mkinj : i f

[@@(expect_failure [19])]
let isInj (x:_) (y:_) (w:i x)
  : Lemma (i x == i y ==> x == y)
  = ()

assume
val isInj_admit (x:_) (y:_)
  : Lemma (i x == i y ==> x == y)
          [SMTPat (i x);
           SMTPat (i y)]

// With the prop refactoring (prop : Type0 opaque), the paradox below
// is no longer expressible because ~(a x) requires a x : prop,
// but a : Type u#1 -> Type u#0, not -> prop.
// The paradox relied on Type0/prop confusion.
[@@(expect_failure [12])]
let p (x : Type u#1) : prop =
  exists a. i a == x /\ ~(a x)
