module InjectiveTypeFormers.Explicit

let coerce (x:'a{'a == 'b}) : 'b = x
let lemma_of_squash (x:squash 'a) : Lemma 'a = ()

type i (f : Type u#1 -> Type u#0) : Type u#1 =
  | Mkinj : i f

[@(expect_failure [19])]
let isInj (x:_) (y:_) (w:i x)
  : Lemma (i x == i y ==> x == y)
  = ()

assume
val isInj_admit (x:_) (y:_) (w:i x)
  : Lemma (i x == i y ==> x == y)

let pa (x:Type u#1) (a:(Type u#1 -> Type u#0)) =
  i a == x /\ ~(a x)

let p (x : Type u#1) : Type u#0 =
  exists a. pa x a

let w : i p = Mkinj
let _ = intro_ambient w
let q = i p
let _ = intro_ambient q

val false_of_pq : p q -> Lemma False
let false_of_pq pq =
  FStar.Classical.(
    exists_elim
      c_False
      (give_witness pq)
      (fun (a:(Type u#1 -> Type u#0){i a == q /\ ~(a q)}) ->
        isInj_admit p a w))

let false_of_pq_squash (pq: p q) : False =
  false_of_pq pq;
  coerce (FStar.Squash.return_squash #c_False (match () with))

let not_pq : ~ (p q) =
  FStar.Classical.give_witness
    #(p q -> False) false_of_pq_squash

let _ = intro_ambient not_pq

let pq : p q =
  FStar.Classical.(
    lemma_of_squash (not_pq);
    exists_intro (pa q) p)

let falso () : Lemma False = false_of_pq pq
