module PulseCore.IndirectionTheoryCSLBasic
open PulseCore.IndirectionTheory
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module RTC = FStar.ReflexiveTransitiveClosure
module HS = PulseCore.HeapSig
let address = nat
assume
val pulse_heap_sig : HS.heap_sig u#3
let pulse_heap : Type u#4 = pulse_heap_sig.mem
let invariants (x:Type u#4) : Type u#4 = address ^-> option x 
let fmap #a #b (f:a -> b) 
: (invariants a ^-> invariants b)
= F.on_dom _ 
  (fun (x:invariants a) ->
    let y: invariants b =
      F.on_dom address
      (fun (a:address) ->
        match x a with | Some v -> Some (f v) | None -> None)
    in
    y)
let elim_feq #a #b (f g: (a ^-> b))
: Lemma
  (requires F.feq f g)
  (ensures f == g)
= ()

let fmap_id (a:Type) (x:invariants a)
: squash (fmap (id #a) == id #(invariants a))
= introduce forall x. fmap (id #a) x == id #(invariants a) x with
    elim_feq (fmap (id #a) x) (id #(invariants a) x);
  elim_feq (fmap (id #a)) (id #(invariants a))


let fmap_comp (a:Type) (b:Type) (c:Type) (b2c:b -> c) (a2b:a -> b)
: (squash (compose (fmap b2c) (fmap a2b) ==
            fmap (compose b2c a2b)))
= let lhs : (invariants a ^-> invariants c) = compose (fmap b2c) (fmap a2b) in
  let rhs : (invariants a ^-> invariants c) = fmap (compose b2c a2b) in
  introduce forall x. lhs x == rhs x
  with (
    assert (F.feq (lhs x) (rhs x))
  );
  assert (lhs `F.feq` rhs);
  elim_feq lhs rhs

noeq
type rest : Type u#4 = {
  pulse_heap : pulse_heap;
  saved_credits : nat;
  freshness_counter : nat;
}

let functor_heap : functor u#3 invariants = {
  fmap = fmap;
  fmap_id = fmap_id;
  fmap_comp = fmap_comp;
  tt = prop;
  t_bot = False;
  other = rest;
}

let istore : Type u#4 = knot_t functor_heap

let world = istore & rest
let istore_repr = nat & invariants (predicate functor_heap)
let of_repr (f:istore_repr) : istore = down f
let as_repr (x:istore) : istore_repr = up x
let world_pred : Type u#4 = world ^-> prop

// let approx (n:nat) (p:world_pred) : world_pred = approx n p
let eq_n (n:nat) (t0 t1:world_pred) =
  approx n t0 == approx n t1

noeq
type core_world = {
  invariants : istore;
  pulse_heap : pulse_heap_sig.sep.core;
  saved_credits : nat;
}  

let core_of (w:world)
: core_world
= let _, rest = w in
  let pc = pulse_heap_sig.sep.core_of rest.pulse_heap in
  { invariants = fst w; pulse_heap = pc; saved_credits = rest.saved_credits }

let disjoint_istore_repr (is0 is1:istore_repr) =
  let n0, i0 = is0 in
  let n1, i1 = is1 in
  n0 == n1 /\
  (forall a. 
    match i0 a, i1 a with
    | None, None
    | None, Some _
    | Some _, None -> True
    | Some p0, Some p1 -> p0 == p1)

let join_istore_repr (is0:istore_repr) (is1:istore_repr { disjoint_istore_repr is0 is1 })
: istore_repr
= let n, i0 = is0 in
  let _, i1 = is1 in
  let i : invariants (predicate functor_heap) =
    F.on_dom _ (fun a -> 
      match i0 a, i1 a with
      | None, None -> None
      | Some p, _
      | _, Some p -> Some p)
  in
  n, i

let join_istore_repr_commutative (is0:istore_repr) (is1:istore_repr { disjoint_istore_repr is0 is1 })
: Lemma (join_istore_repr is0 is1 == join_istore_repr is1 is0)
= let _, i = join_istore_repr is0 is1 in
  let _, i' = join_istore_repr is1 is0 in
  assert (F.feq i i')

let fold_world_pred (f:predicate functor_heap) : world_pred = f
let unfold_world_pred (f:world_pred) : predicate functor_heap = f

let as_repr_of_repr (is:istore_repr)
: Lemma (as_repr (of_repr (fst is, snd is)) == (fst is, fmap (approx (fst is)) (snd is)))
= let n, x = is in
  calc (==) {
    up (down (n, x));
  (==) { up_down n x }
    (n, fmap (approx n) x);
  }

let join_istore_repr_associative
    (is0:istore_repr)
    (is1:istore_repr)
    (is2:istore_repr { 
      disjoint_istore_repr is1 is2 /\
      disjoint_istore_repr is0 (join_istore_repr is1 is2)
    })
: Lemma (
    disjoint_istore_repr is0 is1 /\
    disjoint_istore_repr (join_istore_repr is0 is1) is2 /\
    join_istore_repr is0 (join_istore_repr is1 is2) ==
    join_istore_repr (join_istore_repr is0 is1) is2
  )
= let _, i = join_istore_repr is0 (join_istore_repr is1 is2) in
  let _, i' = join_istore_repr (join_istore_repr is0 is1) is2 in
  assert (F.feq i i')
    
let disjoint_istore (is0 is1:istore) =
  disjoint_istore_repr (as_repr is0) (as_repr is1)

let join_istore (is0:istore) (is1:istore { disjoint_istore is0 is1 }) =
  of_repr (join_istore_repr (as_repr is0) (as_repr is1))

let of_repr_as_repr (i:istore)
: Lemma (of_repr (as_repr i) == i)
= down_up i

let as_repr_join_istore (is0:istore) (is1:istore {disjoint_istore is0 is1})
: Lemma (as_repr (join_istore is0 is1) == join_istore_repr (as_repr is0) (as_repr is1))
= let n, is = join_istore_repr (as_repr is0) (as_repr is1) in
  calc (==) { 
  as_repr (join_istore is0 is1);
  (==) {}
  as_repr (of_repr (join_istore_repr (as_repr is0) (as_repr is1)));
  (==) { as_repr_of_repr (n, is) }
  (n, fmap (approx n) is);
  };
  introduce forall a. fmap (approx n) is a == is a
  with  (
    match fmap (approx n) is a, is a with
    | None, None -> ()
    | Some p, Some q -> 
      calc (==) {
        p;
      (==) {}
        approx n q;
      };
      let _, left = as_repr is0 in
      let _, right = as_repr is1 in
      match left a, right a with
      | Some q', _ ->
        assert (q == q');
        of_repr_as_repr is0;
        as_repr_of_repr (as_repr is0);
        assert (approx n q' == q') 
      | _, Some q' -> 
        of_repr_as_repr is1;
        as_repr_of_repr (as_repr is1)
  );
  assert (F.feq (fmap (approx n) is) is);
  elim_feq (fmap (approx n) is) is;
  assert (fmap (approx n) is == is)

let join_istore_commutative (is0:istore) (is1:istore { disjoint_istore is0 is1 })
: Lemma (join_istore is0 is1 == join_istore is1 is0)
= join_istore_repr_commutative (as_repr is0) (as_repr is1)

let join_istore_associative
    (is0:istore)
    (is1:istore)
    (is2:istore { 
      disjoint_istore is1 is2 /\
      disjoint_istore is0 (join_istore is1 is2)
    })
: Lemma (
    disjoint_istore is0 is1 /\
    disjoint_istore (join_istore is0 is1) is2 /\
    join_istore is0 (join_istore is1 is2) ==
    join_istore (join_istore is0 is1) is2
  )
= assert (disjoint_istore_repr (as_repr is1) (as_repr is2));
  as_repr_join_istore is1 is2;
  assert (disjoint_istore_repr (as_repr is0) (join_istore_repr (as_repr is1) (as_repr is2)));
  join_istore_repr_associative (as_repr is0) (as_repr is1) (as_repr is2);
  as_repr_join_istore is0 is1

let disjoint_worlds (w0 w1:core_world)
: prop 
= disjoint_istore w0.invariants w1.invariants /\
  pulse_heap_sig.sep.disjoint w0.pulse_heap w1.pulse_heap

let disjoint_world_sym (w0 w1:core_world)
: Lemma 
  (ensures disjoint_worlds w0 w1 <==> disjoint_worlds w1 w0)
= pulse_heap_sig.sep.disjoint_sym w0.pulse_heap w1.pulse_heap

let join_worlds (w0:core_world) (w1:core_world { disjoint_worlds w0 w1 })
: core_world
= { invariants = join_istore w0.invariants w1.invariants;
    pulse_heap = pulse_heap_sig.sep.join w0.pulse_heap w1.pulse_heap;
    saved_credits = w0.saved_credits + w1.saved_credits }

let join_worlds_commutative (w0:core_world) (w1:core_world { disjoint_worlds w0 w1 })
: Lemma (disjoint_world_sym w0 w1; join_worlds w0 w1 == join_worlds w1 w0)
= join_istore_commutative w0.invariants w1.invariants;
  pulse_heap_sig.sep.join_commutative w0.pulse_heap w1.pulse_heap

let join_worlds_associative
    (w0:core_world)
    (w1:core_world)
    (w2:core_world { disjoint_worlds w1 w2 /\ disjoint_worlds w0 (join_worlds w1 w2) })
: Lemma (
    disjoint_worlds w0 w1 /\
    disjoint_worlds (join_worlds w0 w1) w2 /\
    join_worlds w0 (join_worlds w1 w2) ==
    join_worlds (join_worlds w0 w1) w2
  )
= join_istore_associative w0.invariants w1.invariants w2.invariants;
  pulse_heap_sig.sep.join_associative w0.pulse_heap w1.pulse_heap w2.pulse_heap

let core_world_pred = core_world ^-> prop
let emp : core_world_pred = F.on_dom core_world #(fun _ -> prop) (fun _ -> True)
let star (p1 p2:core_world_pred) : core_world_pred =
  F.on_dom core_world #(fun _ -> prop)
    (fun w ->
      exists w1 w2.
        disjoint_worlds w1 w2 /\
        w == join_worlds w1 w2 /\
        p1 w1 /\
        p2 w2)
let star_commutative (p1 p2:core_world_pred)
: Lemma (p1 `star` p2 == p2 `star` p1)
= FStar.Classical.forall_intro_2 disjoint_world_sym;
  FStar.Classical.forall_intro_2 join_worlds_commutative;
  FStar.PredicateExtensionality.predicateExtensionality core_world (p1 `star` p2) (p2 `star` p1)



// // inv i p
// let inv (i:address) (p:world_pred) : world_pred =
//   fun (invs, ph) ->
//     let n, inv_heap = mup invs in
//     exists p'.
//       inv_heap i == Some p' /\
//       eq_n n p p'

// let pulse_pred = pulse_heap -> prop
// let lift (p:pulse_pred) : world_pred = fun (k, (ph, _)) -> p ph

// open FStar.Preorder
// let box (r:relation world) (p:world_pred) : world_pred =
//   fun w -> forall w'. r w w' ==> p w'

// let extends : relation world =
//   fun (k,ph) (k',ph') -> //pulse heap can change arbitrarily
//     let n, inv_heap = mup k in
//     let n', inv_heap' = mup k' in
//     n==n' /\
//     (forall a. Some? (inv_heap a) ==> inv_heap a == inv_heap' a)

// let extendely (t:heap_pred) = box extends t

// let age_istore (k:istore) : option istore =
//   let n, psi = mup k in
//   if n = 0 then None
//   else Some (mdown (n - 1, psi))

// let age_world (k:world) : option world =
//   let i, ph = k in
//   match age_istore i with
//   | None -> None
//   | Some k' -> Some (k', ph)



// let iworld = w:world {
//   let ih, ph = w in
//   let n, inv_heap = mup ih in
//   forall i. 
//     match inv_heap i, age1 ih with
//     | Some p, Some ih' -> fold_heap_pred p (ih', ph)
//     | _ -> True
// }

//worlds related by a step of aging
// let relA : relation world =
//   fun w w' -> age_world w == Some w'

// let remaining w = fst (mup (fst w))
// let remaining_k k = fst (mup k)
// let age1_decreases (k:heap { Some? (age1 k)})
// : Lemma (
//     remaining_k (Some?.v (age1 k)) == remaining_k k - 1
//   )
// = let n, psi = mup k in
//   up_down #heap (n - 1) psi
// let rec relAplus_alt (w0:world) (w1:world { remaining w0 > remaining w1})
// : Tot prop (decreases (remaining w0 - remaining w1))
// = if remaining w0 = remaining w1 + 1 then relA w0 w1
//   else (
//     match age1 (fst w0) with
//     | None -> False
//     | Some k ->
//       age1_decreases (fst w0);
//       relAplus_alt (k, snd w0) w1
//   )
// let relAplus (w0 w1:world) =
//   if remaining w0 > remaining w1 then relAplus_alt w0 w1
//   else False
// let later (t:heap_pred) : heap_pred = box relAplus t


// ----------------

// inv i p  @ w_n  // eq_n n p p'

// i -> Some p' /\ eq_n (n - 1) p p'   @ (agew1 w_n)

// p' (age1 w_n) ///because w_n is an iworld

// have p (age1 w_n) because level (age1 w_n) = n - 1


