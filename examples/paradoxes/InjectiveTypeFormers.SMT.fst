module InjectiveTypeFormers.SMT
type i (f : Type u#1 -> Type u#0) : Type u#1 =
  | Mkinj : i f

[@(expect_failure [19])]
let isInj (x:_) (y:_) (w:i x)
  : Lemma (i x == i y ==> x == y)
  = ()

assume
val isInj_admit (x:_) (y:_)
  : Lemma (i x == i y ==> x == y)
          [SMTPat (i x);
           SMTPat (i y)]

let p (x : Type u#1) : Type u#0 =
  exists a. i a == x /\ ~(a x)

let w : i p = Mkinj

let q = i p

val false_of_pq : p q -> Lemma False
let false_of_pq pq = ()

let pq : p q = assert (exists a. i a == q /\ ~(a q))

let falso () : Lemma False = false_of_pq pq
