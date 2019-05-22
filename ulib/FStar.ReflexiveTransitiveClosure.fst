module FStar.ReflexiveTransitiveClosure

open FStar.Tactics

#set-options "--max_ifuel 1 --max_fuel 0"

let closure_reflexive #a r =
  assert (forall x. closure r x x) by
    (let x = forall_intro () in mapply (quote Refl))

let closure_transitive #a r =
  assert (transitive (closure r)) by
    (let x = forall_intro () in
     let y = forall_intro () in
     let z = forall_intro () in
     let h = implies_intro () in
     and_elim (binder_to_term h);
     let h1 = implies_intro () in
     let h2 = implies_intro () in
     mapply (quote (Closure #a #r));
     assumption ();
     assumption ())

val _inv_closure: #a:Type0 -> r:relation a -> p:(a -> Type0) 
  -> hr: (x:a -> y:a -> Lemma (requires p x /\ r x y) (ensures p y)) 
  -> x:a 
  -> y:a
  -> h:closure r x y
  -> Lemma (requires p x) (ensures p y) (decreases h)
let rec _inv_closure #a r p hr x y h =
  match h with
  | Refl _ -> ()
  | Step _ _ _ -> hr x y
  | Closure x a y xa ay ->
    _inv_closure r p hr x a xa;
    _inv_closure r p hr a y ay

val inv_closure: #a:Type0 -> r:relation a -> p:(a -> Type0) 
  -> hr: (x:a -> y:a -> Lemma (requires p x /\ r x y) (ensures p y)) 
  -> x:a 
  -> y:a
  -> Lemma (requires p x /\ closure r x y) (ensures p y)
let inv_closure #a r p hr x y =
  let rxy = Squash.get_proof (closure r x y) in
  let l = Classical.move_requires (_inv_closure r p hr x y) in
  let l = Classical.lemma_to_squash_gtot l in
  Squash.bind_squash rxy l

let stable_on_closure #a r p p_stable_on_r =
  assert (forall x y. p x /\ closure r x y ==> p y) by
    (let x = forall_intros () in
     match x with
     | [x;_;_] ->
       let x = binder_to_term x in
       let x: a = unquote x in
       mapply (quote (inv_closure r p p_stable_on_r x))
     | _ -> ())

/// Test

type state = | A | B | C 

let r x y = 
  match x, y with 
  | A, B | B, C | C, B -> True
  | _ -> False

let p = function 
  | A -> False 
  | B | C -> True 

let hp x y : Lemma (requires p x /\ r x y) (ensures p y) = ()

let cl = reflexive_transitive_closure r

let reachable_from_B (x:state{ cl B x }) : Lemma (x = B \/ x = C) =
  stable_on_closure r p hp
