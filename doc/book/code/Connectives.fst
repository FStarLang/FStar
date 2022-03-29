module Connectives
open FStar.Classical.Sugar

type empty =

//SNIPPET_START: empty_elim$
let empty_elim (#a:Type) (x:empty) : a = match x with
//SNIPPET_END: empty_elim$

//SNIPPET_START: false_elim$
let rec false_elim (#a:Type) (x:False) : a = false_elim x
//SNIPPET_END: false_elim$

//SNIPPET_START: and_intro$
let and_intro #p #q (pf_p:p) (pf_q:q)
  : p & q
  = pf_p, pf_q
//SNIPPET_END: and_intro$

//SNIPPET_START: conj_intro$
let conj_intro #p #q (pf_p:squash p) (pf_q: squash q)
  : Lemma (p /\ q)
  = ()
//SNIPPET_END: conj_intro$

//SNIPPET_START: conj_intro_sugar$
let conj_intro_sugar #p #q (pf_p:squash p) (pf_q: squash q)
  : squash (p /\ q)
  = introduce p /\ q
    with pf_p
    and  pf_q
//SNIPPET_END: conj_intro_sugar$


//SNIPPET_START: and_elim$
let and_elim_1 #p #q (pf_pq:p & q)
  : p
  = pf_pq._1

let and_elim_2 #p #q (pf_pq:p & q)
  : q
  = pf_pq._2
//SNIPPET_END: and_elim$


//SNIPPET_START: conj_elim$
let conj_elim_1 #p #q (pf_pq:squash (p /\ q))
  : squash p
  = ()

let conj_elim_2 #p #q (pf_pq:squash (p /\ q))
  : squash q
  = ()
//SNIPPET_END: conj_elim$

//SNIPPET_START: conj_elim_sugar$
let conj_elim_sugar_1 #p #q (pf_pq:squash (p /\ q))
  : squash p
  = eliminate p /\ q
    returns p
    with pf_p pf_q. pf_p

let conj_elim_sugar_2 #p #q (pf_pq:squash (p /\ q))
  : squash p
  = eliminate p /\ q
    returns p
    with pf_p pf_q. pf_q
//SNIPPET_END: conj_elim_sugar$

//SNIPPET_START: or_intro$
let or_intro_left #p #q (pf_p:squash p)
  : squash (p \/ q)
  = ()

let or_intro_right #p #q (pf_p:squash p)
  : squash (p \/ q)
  = ()
//SNIPPET_END: or_intro$

//SNIPPET_START: or_intro_sugar$
let or_intro_sugar_left #p #q (pf_p:squash p)
  : squash (p \/ q)
  = introduce p \/ q
    with Left pf_p

let or_intro_sugar_right #p #q (pf_p:squash p)
  : squash (p \/ q)
  = introduce p \/ q
    with Right pf_p
//SNIPPET_END: or_intro_sugar$

//SNIPPET_START: either_elim$
let either_elim #p #q #r (p_or_q: either p q)
                         (pr: p -> r)
                         (qr: q -> r)
  : r
  = match p_or_q with
    | Inl p -> pr p
    | Inr q -> qr q
//SNIPPET_END: either_elim$

//SNIPPET_START: or_elim$
let or_elim #p #q #r (pf_p:squash (p \/ q))
                     (pf_pr:squash (p ==> r))
                     (pf_qr:squash (q ==> r))
  : squash r
  = ()
//SNIPPET_END: or_elim$

//SNIPPET_START: or_elim_sugar$
let or_elim_sugar #p #q #r
                  (pf_p:squash (p \/ q))
                  (pf_pr:unit -> Lemma (requires p) (ensures r))
                  (pf_qr:unit -> Lemma (requires q) (ensures r))
  : squash r
  = eliminate p \/ q
    returns r
    with pf_p. pf_pr () //pf_p : squash p
    and  pf_q. pf_qr () //pf_q : squash q
//SNIPPET_END: or_elim_sugar$

//SNIPPET_START: implies_intro$
let implies_intro_1 #p #q (pq: squash p -> squash q)
  : squash (p ==> q)
  = introduce p ==> q
    with pf_p. pq pf_p

let implies_intro_2 #p #q (pq: unit -> Lemma (requires p) (ensures q))
  : squash (p ==> q)
  = introduce p ==> q
    with pf_p. pq pf_p

let implies_intro_3 #p #q (pq: unit -> Lemma (requires p) (ensures q))
  : Lemma (p ==> q)
  = introduce p ==> q
    with pf_p. pq pf_p
//SNIPPET_END: implies_intro$

//SNIPPET_START: implies_elim$
let implies_elim #p #q (pq:squash (p ==> q)) (pf_p: squash p)
  : squash q
  = ()

let implies_elim_sugar #p #q (pq:squash (p ==> q)) (pf_p: squash p)
  : squash q
  = eliminate p ==> q
    with pf_p
//SNIPPET_END: implies_elim$

//SNIPPET_START: neg_intro$
let neg_intro #p (f:squash p -> squash False)
  : squash (~p)
  = introduce p ==> False
    with pf_p. f pf_p
//SNIPPET_END: neg_intro$

//SNIPPET_START: neg_elim$
let neg_elim #p #q (f:squash (~p)) (lem:unit -> Lemma p)
  : squash q
  = eliminate p ==> False
    with lem()
//SNIPPET_END: neg_elim$


//SNIPPET_START: forall_intro$
let forall_intro_1 (#t:Type)
                   (#q:t -> Type)
                   (f : (x:t -> squash (q x)))
  : squash (forall (x:t). q x)
  = introduce forall (x:t). q x
    with f x

let forall_intro_2 (#t:Type)
                   (#q:t -> Type)
                   (f : (x:t -> Lemma (q x)))
  : squash (forall (x:t). q x)
  = introduce forall (x:t). q x
    with f x

let forall_intro_3 (#t0:Type)
                   (#t1:t0 -> Type)
                   (#q: (x0:t0 -> x1:t1 x0 -> Type))
                   (f : (x0:t0 -> x1:t1 x0 ->  Lemma (q x0 x1)))
  : squash (forall (x0:t0) (x1:t1 x0). q x0 x1)
  = introduce forall (x0:t0) (x1:t1 x0). q x0 x1
    with f x0 x1
//SNIPPET_END: forall_intro$

//SNIPPET_START: forall_elim_1$
let forall_elim_1 (#t:Type)
                  (#q:t -> Type)
                  (f : squash (forall (x:t). q x))
                  (a:t)
  : squash (q a)
  = ()
//SNIPPET_END: forall_elim_1$

//SNIPPET_START: forall_elim_sugar$
let forall_elim_2 (#t0:Type)
                  (#t1:t0 -> Type)
                  (#q: (x0:t0 -> x1:t1 x0 -> Type))
                  (f : squash (forall x0 x1. q x0 x1))
                  (v0: t0)
                  (v1: t1 v0)
  : squash (q v0 v1)
  = eliminate forall x0 x1. q x0 x1
    with v0 v1
//SNIPPET_END: forall_elim_sugar$

//SNIPPET_START: dtuple2_intro$
let dtuple2_intro (x:int) (y:int { y > x })
  : (a:int & b:int{b > a})
  = (| x, y |)
//SNIPPET_END: dtuple2_intro$


//SNIPPET_START: exists_intro$
let exists_intro_1 (#t:Type)
                   (#q:t -> Type)
                   (a:t) (b:t)
                   (f : squash (q a /\ q b))
  : squash (exists x. q x)
  = () //instantiation found by SMT, it chose a or b, unclear/irrelevant which

let exists_intro_2 (#t:Type)
                   (#q:t -> Type)
                   (a:t) (b:t)
                   (f : squash (q a))
                   (g : squash (q b))
  : squash (exists x. q x)
  = introduce exists x. q x
    with a //witness
    and f  //proof term of q applied to witness

let exists_intro_3 (#t:Type)
                   (#q:t -> Type)
                   (a:t) (b:t)
                   (f : squash (q a /\ q b))
  : squash (exists x. q x)
  = introduce exists x. q x
    with a
    and f // f: squash (q a /\ q b) implicitly eliminated to squash (q a) by SMT
//SNIPPET_END: exists_intro$


//SNIPPET_START: dtuple2_elim$
let dtuple2_elim (#t:Type) (#p:t -> Type) (#q:Type)
                 (pf: (x:t & p x))
                 (k : (x:t -> p x -> q))
  : q
  = let (| x, pf_p |) = pf in
    k x pf_p
//SNIPPET_END: dtuple2_elim$

//SNIPPET_START: exists_elim$
let exists_elim (#t:Type) (#p:t -> Type) (#q:Type)
                 (pf: squash (exists (x:t). p x))
                 (k : (x:t -> squash (p x) -> squash q))
  : squash q
  = eliminate exists (x:t). p x
    returns q
    with pf_p. k x pf_p

let exists_elim_alt (#t:Type) (#p:t -> Type) (#q:Type)
                    (pf: squash (exists (x:t). p x))
                    (k : (x:t -> Lemma (requires p x)
                                      (ensures q)))
  : Lemma q
  = eliminate exists (x:t). p x
    returns q
    with pf_p. k x
//SNIPPET_END: exists_elim$
