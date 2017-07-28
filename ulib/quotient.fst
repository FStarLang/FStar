module Quotient

open FStar.Tactics

module SEM = FStar.StrongExcludedMiddle
module C = FStar.Classical

type rel (a:Type) = a -> a -> Type

let equivalence_relation (#a:Type) (r:rel a) =
  (forall x. r x x) /\ (forall x y. r x y ==> r y x) /\ (forall x y z. r x y /\ r y z ==> r x z)

let equiv (a:Type) = r:rel a{equivalence_relation r}

let equivalence_class (#a:Type) (p: a -> GTot bool) (r:equiv a) =
  exists x. p x /\ (forall y. r x y <==> p y)

let quotient (a:Type u#a) (r:equiv a): Type u#a = p:(a -> GTot bool){equivalence_class p r}

let prop = a:Type{forall (x y: a). x == y}

let squash (#a:Type) (r:equiv a) (x:a) : p:(quotient a r) =
  let f (y:a) : GTot bool = SEM.strong_excluded_middle (r x y) in
  f

(* let g (x:nat) = x + x + x *)

(* let bidule : tactic unit = *)
(*   t <-- quote g ; *)
(*   unfold_def t ;; *)
(*   smt *)

let prop_equiv (a b:prop) :Lemma (requires (a == b)) (ensures (a <==> b)) = ()

let intro_quotient_type (#a:Type) (r:equiv a) (f: a -> prop)
  : Ghost (quotient a r -> prop)
    (requires (forall x y. r x y ==> f x == f y))
    (ensures (fun g -> forall x. g (squash r x) <==> f x))
= let g (p:quotient a r) : prop = exists (x:a). p x /\ f x in
  assert (forall x. f x ==> (exists x'. squash r x x' /\ f x')) ;
  assert (forall x. f x ==> g (squash r x)) ;
  assert (forall x p. p == squash r x ==> g p == (exists x'. p x' /\ f x')) ;
  let h (x:a) (p:quotient a r) : Lemma (requires (p == squash r x)) (ensures (g p ==> f x)) =
      assert (g p == (exists x'. p x' /\ f x'));
      prop_equiv (g p) (exists x'. p x' /\ f x') ;
      assert ((exists x'. p x' /\ f x') ==> f x)
  in
  let h1 (x:a) : Lemma (let p = squash r x in g p ==> f x) = h x (squash r x) in
  C.forall_intro h1 ;
  assert (forall x. g (squash r x) ==> f x) ;
  (* assert_by_tactic *)
  (*   ( x <-- forall_intro ; *)
  (*     exact (apply (quote h1) x) *)
  (*   ) *)
  (*   (forall x.let p = squash r x in g p ==> f x) *)
  g

let op_String_Access (#a:Type) (x:a) (r:equiv a) = squash r x

let imod5 :  rel int = fun x y -> b2t (x = y % 5)
let mod5 : equiv int = admit () ; imod5

let test = (2).[mod5] = (7).[mod5]

let intro_quotient (#a #b:Type) (ra:equiv a) (rb:equiv b) (f: a -> quotient b rb)
  : Pure (quotient a ra -> quotient b rb)
    (requires (forall x y. ra x y ==> f x == f y))
    (ensures (fun g -> forall x. g (squash ra x) == f x))
= let g (p:quotient a ra) : quotient b rb = fun (y:b) -> SEM.strong_excluded_middle (exists x. p x /\ f x y) in
  g
