module FStar.Algebra.Monoid

open FStar.Classical
module PropExt = FStar.PropositionalExtensionality

(** Definition of a monoid *)

let right_unitality_lemma (m:Type) (u:m) (mult:m -> m -> m) =
  forall (x:m). x `mult` u == x

let left_unitality_lemma (m:Type) (u:m) (mult:m -> m -> m) =
  forall (x:m). u `mult` x == x

let associativity_lemma (m:Type) (mult:m -> m -> m) =
  forall (x y z:m). x `mult` y `mult` z == x `mult` (y `mult` z)

unopteq
type monoid (m:Type) =
  | Monoid :
    unit:m ->
    mult:(m -> m -> m) ->
    right_unitality:right_unitality_lemma m unit mult ->
    left_unitality:left_unitality_lemma m unit mult ->
    associativity:associativity_lemma m mult ->
    monoid m


let intro_monoid (m:Type) (u:m) (mult:m -> m -> m)
  : Pure (monoid m)
    (requires (right_unitality_lemma m u mult /\ left_unitality_lemma m u mult /\ associativity_lemma m mult))
    (ensures (fun mm -> Monoid?.unit mm == u /\ Monoid?.mult mm == mult))
=
  Monoid u mult
    (get_forall (fun (x:m) -> x `mult` u == x))
    (get_forall (fun (x:m) -> u `mult` x == x))
    (get_forall (fun (x:m) -> forall (y z:m). x `mult` y `mult` z == x `mult` (y `mult` z)))


(** Some monoid structures *)

let nat_monoid : monoid nat =
  let add (x y : nat) : nat = x + y in
  intro_monoid nat 0 add

let int_monoid : monoid int =
  intro_monoid int 0 (+)

let conjunction_monoid : monoid prop =
  let u : prop = True in
  let mult (p q : prop) : prop = p /\ q in

  let left_unitality_helper (p:prop) : Lemma ((u `mult` p) == p) =
    assert ((u `mult` p) <==> p) ;
    PropExt.apply (u `mult` p) p
  in

  let right_unitality_helper (p:prop) : Lemma ((p `mult` u) == p) =
    assert ((p `mult` u) <==> p) ;
    PropExt.apply (p `mult` u) p
  in

  let associativity_helper (p1 p2 p3 : prop) : Lemma (p1 `mult` p2 `mult` p3 == p1 `mult` (p2 `mult` p3)) =
    assert (p1 `mult` p2 `mult` p3 <==> p1 `mult` (p2 `mult` p3)) ;
    PropExt.apply (p1 `mult` p2 `mult` p3) (p1 `mult` (p2 `mult` p3))
  in

  forall_intro right_unitality_helper ;
  assert (right_unitality_lemma prop u mult) ;
  forall_intro left_unitality_helper ;
  assert (left_unitality_lemma prop u mult) ;
  forall_intro_3 associativity_helper;
  assert (associativity_lemma prop mult) ;
  intro_monoid prop u mult


let disjunction_monoid : monoid prop =
  let u : prop = False in
  let mult (p q : prop) : prop = p \/ q in

  let left_unitality_helper (p:prop) : Lemma ((u `mult` p) == p) =
    assert ((u `mult` p) <==> p) ;
    PropExt.apply (u `mult` p) p
  in

  let right_unitality_helper (p:prop) : Lemma ((p `mult` u) == p) =
    assert ((p `mult` u) <==> p) ;
    PropExt.apply (p `mult` u) p
  in

  let associativity_helper (p1 p2 p3 : prop) : Lemma (p1 `mult` p2 `mult` p3 == p1 `mult` (p2 `mult` p3)) =
    assert (p1 `mult` p2 `mult` p3 <==> p1 `mult` (p2 `mult` p3)) ;
    PropExt.apply (p1 `mult` p2 `mult` p3) (p1 `mult` (p2 `mult` p3))
  in

  forall_intro right_unitality_helper ;
  assert (right_unitality_lemma prop u mult) ;
  forall_intro left_unitality_helper ;
  assert (left_unitality_lemma prop u mult) ;
  forall_intro_3 associativity_helper;
  assert (associativity_lemma prop mult) ;
  intro_monoid prop u mult

(* Definition of a left action *)

let mult_act_lemma (m a:Type) (mult:m -> m -> m) (act:m -> a -> a) =
  forall (x x':m) (y:a). (x `mult` x') `act` y == x `act` (x' `act` y)

let unit_act_lemma (m a:Type) (u:m) (act:m -> a -> a) =
  forall (y:a). u `act` y == y

unopteq
type left_action (#m:Type) (mm:monoid m) (a:Type) =
  | LAct :
    act:(m -> a -> a) ->
    mult_lemma: mult_act_lemma m a (Monoid?.mult mm) act ->
    unit_lemma: unit_act_lemma m a (Monoid?.unit mm) act ->
    left_action mm a
