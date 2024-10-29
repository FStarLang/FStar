module PulseCore.IndirectionTheorySep
open PulseCore.IndirectionTheory
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module RTC = FStar.ReflexiveTransitiveClosure
module HS = PulseCore.HeapSig
module E = PulseCore.HeapExtension
module B = PulseCore.BaseHeapSig
module IT = PulseCore.IndirectionTheory
open FStar.Ghost {erased, hide, reveal}
friend PulseCore.MemoryAlt // FIXME

let address = nat
let pulse_heap_sig : HS.heap_sig u#3 = PM.sig

[@@erasable]
noeq type istore_val_ (x: Type u#4) =
  | None
  | Inv : x -> istore_val_ x

let map_istore_val #x #y (f: x->y) (v: istore_val_ x) : istore_val_ y =
  match v with
  | None -> None
  | Inv p -> Inv (f p)

[@@erasable]
let invariants (x:Type u#4) : Type u#4 = address ^-> istore_val_ x

let fmap #a #b (f:a -> b) 
: (invariants a ^-> invariants b)
= F.on_dom (invariants a) fun x ->
    F.on_dom address fun a ->
      map_istore_val f (x a)

let elim_feq #a #b (f g: (a ^-> b))
: Lemma
  (requires F.feq f g)
  (ensures f == g)
= ()

let on_dom_ext #t #s (f g: t ^-> s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x;
  F.extensionality _ _ f g

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
  pulse_heap : pulse_heap_sig.sep.core;
  saved_credits : erased nat;
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
let world_pred : Type u#4 = world ^-> prop

let istore_val = istore_val_ world_pred

let age_istore_to (is: istore) (n: nat) : istore =
  down (n, snd (up is))

let age_to (w: world) (n: nat) : world =
  (age_istore_to (fst w) n, snd w)

let up_age_to (w: world) (n: nat) : Lemma (up (age_to w n)._1 == (n, fmap (approx n) (snd (up (fst w))))) =
  assert up (age_to w n)._1 == up (down (n, snd (up (fst w))));
  up_down n (snd (up (fst w)))

let age_to_rest (w: world) (n: nat) : Lemma ((age_to w n)._2 == w._2) = ()

let level_istore (is: istore) : nat =
  level is

let level (w: world) : nat =
  level_istore (fst w)

let read_istore (is: istore) a : istore_val = snd (up is) a
let read (w: world) a = read_istore (fst w) a

let read_age_istore_to (is: istore) n a : Lemma (read_istore (age_istore_to is n) a ==
    (map_istore_val (approx n) (read_istore is a))) =
  up_down n (snd (up is))

let read_age_to (w: world) n a : Lemma (read (age_to w n) a == map_istore_val (approx n) (read w a)) =
  read_age_istore_to w._1 n a

let level_age_to w n : Lemma (level (age_to w n) == n) [SMTPat (level (age_to w n))] =
  up_down n (snd (up (fst w)))

let age1 (w: world) : world =
  if level_istore (fst w) > 0 then age_to w (level_istore (fst w) - 1) else w

let credits (w: world) : GTot nat =
  w._2.saved_credits

noeq type mem = {
  invariants: istore;
  pulse_heap : pulse_heap_sig.mem;
  saved_credits : erased nat;
  freshness_counter: nat;
}

let core_of (m: mem) : world =
  (m.invariants, ({ pulse_heap = pulse_heap_sig.sep.core_of m.pulse_heap; saved_credits = m.saved_credits } <: rest))

let istore_repr = nat & invariants (predicate functor_heap)
let of_repr (f:istore_repr) : istore = down f
let as_repr (x:istore) : istore_repr = up x

let level_down (f: istore_repr) : Lemma (level_istore (down f) == f._1) [SMTPat (level_istore (down f))] =
  up_down f._1 f._2

let istore_ext (i1: istore) (i2: istore { level_istore i1 == level_istore i2 })
    (h: (a:address -> squash (read_istore i1 a == read_istore i2 a))) : squash (i1 == i2) =
  introduce forall a. (up i1)._2 a == (up i2)._2 a with h a;
  elim_feq (up i1)._2 (up i2)._2;
  down_up i1;
  down_up i2

let world_ext (w1: world) (w2: world { level w1 == level w2 /\ snd w1 == snd w2 })
    (h: (a: address -> squash (read w1 a == read w2 a))) : squash (w1 == w2) =
  istore_ext (fst w1) (fst w2) h

let world_pred_ext (f g: world_pred) (h: (w:world -> squash (f w <==> g w))) : squash (f == g) =
  introduce forall w. f w == g w with
    (h w; PropositionalExtensionality.apply (f w) (g w));
  elim_feq f g

let approx_approx m n (p: world_pred) : Lemma (approx m (approx n p) == approx (min m n) p) [SMTPat (approx m (approx n p))] =
  world_pred_ext (approx m (approx n p)) (approx (min m n) p) fun w ->
    assert_norm (approx n p w == (if level w >= n then False else p w));
    assert_norm (approx m (approx n p) w == (if level w >= m then False else if level w >= n then False else p w));
    assert_norm (approx (min m n) p w == (if level w >= min m n then False else p w))

let age_to_age_to (w: world) (m n: nat) :
    Lemma (requires n <= m) (ensures age_to (age_to w m) n == age_to w n) =
  world_ext (age_to (age_to w m) n) (age_to w n) fun a ->
    read_age_to (age_to w m) n a;
    read_age_to w m a;
    read_age_to w n a;
    assert read (age_to (age_to w m) n) a == map_istore_val (approx n) (map_istore_val (approx m) (read w a));
    assert map_istore_val (approx n) (map_istore_val (approx m) (read w a))
      == map_istore_val (approx (min m n)) (read w a);
    ()

// let approx (n:nat) (p:world_pred) : world_pred = approx n p
let eq_n (n:nat) (t0 t1:world_pred) =
  approx n t0 == approx n t1

let is_ghost_action = admit ()
let ghost_action_preorder = admit ()

let is_full = admit ()

let hereditary (p: world_pred) : prop =
  forall (w: world) (n: nat).
    n < level w /\ p w ==>
    p (age_to w n)

let slprop = p:world_pred { hereditary p }

let interp p w = p w

unfold
let istore_val_compat (x y: istore_val) =
  match x, y with
  | None, _ | _, None -> True
  | Inv p0, Inv p1 -> p0 == p1

let disjoint_istore (is0 is1:istore) =
  level_istore is0 == level_istore is1 /\
  (forall a. istore_val_compat (read_istore is0 a) (read_istore is1 a))

let disjoint_istore_read is0 is1 a :
    Lemma (requires disjoint_istore is0 is1)
      (ensures istore_val_compat (read_istore is0 a) (read_istore is1 a))
      [SMTPatOr [
        [SMTPat (disjoint_istore is0 is1); SMTPat (read_istore is0 a)];
        [SMTPat (disjoint_istore is0 is1); SMTPat (read_istore is1 a)];
      ]] =
  ()

let mk_istore n (is: address -> istore_val) : istore =
  let f' = F.on_dom address is in
  down (n, f')

let level_mk_istore n is : Lemma (level_istore (mk_istore n is) == n) [SMTPat (level_istore (mk_istore n is))] =
  let f' = F.on_dom address is in
  assert_norm (mk_istore n is == down (n, f'));
  up_down #_ #functor_heap n f'

let read_mk_istore n is a :
    Lemma (read_istore (mk_istore n is) a == map_istore_val (approx n) (is a))
      [SMTPat (read_istore (mk_istore n is) a)] =
  let is' = F.on_dom address is in
  assert_norm (mk_istore n is == down (n, is'));
  up_down #_ #functor_heap n is';
  assert_norm (fmap (approx n) is' a == map_istore_val (approx n) (is' a))

let empty_istore n : istore = mk_istore n fun _ -> None
let empty n : world = (empty_istore n, ({ pulse_heap = pulse_heap_sig.sep.empty; saved_credits = 0 } <: rest))

let age_to_empty (m n: nat) : Lemma (age_to (empty n) m == empty m) [SMTPat (age_to (empty n) m)] =
  world_ext (age_to (empty n) m) (empty m) fun a -> read_age_to (empty n) m a

let emp : slprop =
  F.on_dom world #(fun _ -> prop) fun w -> w == empty (level w)

let pure p = F.on_dom _ fun w -> p

let join_istore (is0:istore) (is1:istore { disjoint_istore is0 is1 }) : istore =
  mk_istore (level_istore is0) fun a ->
    match read_istore is0 a, read_istore is1 a with
    | None, None -> None
    | Inv p, _ | _, Inv p -> Inv p

let read_join_istore (is0:istore) (is1:istore { disjoint_istore is0 is1 }) a :
  Lemma (read_istore (join_istore is0 is1) a ==
    (match read_istore is0 a, read_istore is1 a with
    | None, None -> None
    | Inv p, _ | _, Inv p -> Inv (approx (level_istore is0) p))) =
  ()

let join_istore_commutative (is0:istore) (is1:istore { disjoint_istore is0 is1 }) :
    Lemma (join_istore is0 is1 == join_istore is1 is0) =
  istore_ext (join_istore is0 is1) (join_istore is1 is0) fun a -> ()

let approx_read_istore (is: istore) a :
    Lemma (map_istore_val (approx (level_istore is)) (read_istore is a) == read_istore is a)
    [SMTPat (read_istore is a)] =
  let n, i = up is in down_up is; up_down n i

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
=
  istore_ext (join_istore is0 (join_istore is1 is2)) (join_istore (join_istore is0 is1) is2) fun a -> ()

// let disjoint_istore_repr (is0 is1:istore_repr) =
//   let n0, i0 = is0 in
//   let n1, i1 = is1 in
//   n0 == n1 /\
//   (forall a. istore_val_compat (i0 a) (i1 a))

// let join_istore_repr (is0:istore_repr) (is1:istore_repr { disjoint_istore_repr is0 is1 })
// : istore_repr
// = let n, i0 = is0 in
//   let _, i1 = is1 in
//   let i : invariants (predicate functor_heap) =
//     F.on_dom _ (fun a -> 
//       hide (match reveal (i0 a), reveal (i1 a) with
//       | None, None -> None
//       | Some p, _
//       | _, Some p -> Some p))
//   in
//   n, i

// let join_istore_repr_commutative (is0:istore_repr) (is1:istore_repr { disjoint_istore_repr is0 is1 })
// : Lemma (join_istore_repr is0 is1 == join_istore_repr is1 is0)
// = let _, i = join_istore_repr is0 is1 in
//   let _, i' = join_istore_repr is1 is0 in
//   elim_feq i i'

// let fold_world_pred (f:predicate functor_heap) : world_pred = f
// let unfold_world_pred (f:world_pred) : predicate functor_heap = f

// let as_repr_of_repr (is:istore_repr)
// : Lemma (as_repr (of_repr (fst is, snd is)) == (fst is, fmap (approx (fst is)) (snd is)))
// = let n, x = is in
//   calc (==) {
//     up (down (n, x));
//   (==) { up_down n x }
//     (n, fmap (approx n) x);
//   }

// let join_istore_repr_associative
//     (is0:istore_repr)
//     (is1:istore_repr)
//     (is2:istore_repr { 
//       disjoint_istore_repr is1 is2 /\
//       disjoint_istore_repr is0 (join_istore_repr is1 is2)
//     })
// : Lemma (
//     disjoint_istore_repr is0 is1 /\
//     disjoint_istore_repr (join_istore_repr is0 is1) is2 /\
//     join_istore_repr is0 (join_istore_repr is1 is2) ==
//     join_istore_repr (join_istore_repr is0 is1) is2
//   )
// = let _, i = join_istore_repr is0 (join_istore_repr is1 is2) in
//   let _, i' = join_istore_repr (join_istore_repr is0 is1) is2 in
//   assert (F.feq i i')
    
// let disjoint_istore (is0 is1:istore) =
//   disjoint_istore_repr (as_repr is0) (as_repr is1)

// let join_istore (is0:istore) (is1:istore { disjoint_istore is0 is1 }) =
//   of_repr (join_istore_repr (as_repr is0) (as_repr is1))

// let of_repr_as_repr (i:istore)
// : Lemma (of_repr (as_repr i) == i)
// = down_up i

// let as_repr_join_istore (is0:istore) (is1:istore {disjoint_istore is0 is1})
// : Lemma (as_repr (join_istore is0 is1) == join_istore_repr (as_repr is0) (as_repr is1))
// = let n, is = join_istore_repr (as_repr is0) (as_repr is1) in
//   calc (==) { 
//   as_repr (join_istore is0 is1);
//   (==) {}
//   as_repr (of_repr (join_istore_repr (as_repr is0) (as_repr is1)));
//   (==) { as_repr_of_repr (n, is) }
//   (n, fmap (approx n) is);
//   };
//   introduce forall a. fmap (approx n) is a == is a
//   with  (
//     match reveal (fmap (approx n) is a), reveal (is a) with
//     | None, None -> ()
//     | Some p, Some q -> 
//       calc (==) {
//         p;
//       (==) {}
//         approx n q;
//       };
//       let _, left = as_repr is0 in
//       let _, right = as_repr is1 in
//       match reveal (left a), reveal (right a) with
//       | Some q', _ ->
//         assert (q == q');
//         of_repr_as_repr is0;
//         as_repr_of_repr (as_repr is0);
//         assert (approx n q' == q') 
//       | _, Some q' -> 
//         of_repr_as_repr is1;
//         as_repr_of_repr (as_repr is1)
//   );
//   assert (F.feq (fmap (approx n) is) is);
//   elim_feq (fmap (approx n) is) is;
//   assert (fmap (approx n) is == is)

// let join_istore_commutative (is0:istore) (is1:istore { disjoint_istore is0 is1 })
// : Lemma (join_istore is0 is1 == join_istore is1 is0)
// = join_istore_repr_commutative (as_repr is0) (as_repr is1)

// let join_istore_associative
//     (is0:istore)
//     (is1:istore)
//     (is2:istore { 
//       disjoint_istore is1 is2 /\
//       disjoint_istore is0 (join_istore is1 is2)
//     })
// : Lemma (
//     disjoint_istore is0 is1 /\
//     disjoint_istore (join_istore is0 is1) is2 /\
//     join_istore is0 (join_istore is1 is2) ==
//     join_istore (join_istore is0 is1) is2
//   )
// = assert (disjoint_istore_repr (as_repr is1) (as_repr is2));
//   as_repr_join_istore is1 is2;
//   assert (disjoint_istore_repr (as_repr is0) (join_istore_repr (as_repr is1) (as_repr is2)));
//   join_istore_repr_associative (as_repr is0) (as_repr is1) (as_repr is2);
//   as_repr_join_istore is0 is1

let disjoint_worlds (w0 w1:world)
: prop 
= disjoint_istore w0._1 w1._1 /\
  pulse_heap_sig.sep.disjoint w0._2.pulse_heap w1._2.pulse_heap

let disjoint_world_sym (w0 w1:world)
: Lemma 
  (ensures disjoint_worlds w0 w1 <==> disjoint_worlds w1 w0)
= pulse_heap_sig.sep.disjoint_sym w0._2.pulse_heap w1._2.pulse_heap

let join_worlds (w0:world) (w1:world { disjoint_worlds w0 w1 })
: world
= (join_istore w0._1 w1._1, ({
    pulse_heap = pulse_heap_sig.sep.join w0._2.pulse_heap w1._2.pulse_heap;
    saved_credits = w0._2.saved_credits + w1._2.saved_credits } <: rest))

let join_worlds_commutative (w0:world) (w1:world { disjoint_worlds w0 w1 })
: Lemma (disjoint_world_sym w0 w1; join_worlds w0 w1 == join_worlds w1 w0)
= join_istore_commutative w0._1 w1._1;
  pulse_heap_sig.sep.join_commutative w0._2.pulse_heap w1._2.pulse_heap

let join_worlds_associative
    (w0:world)
    (w1:world)
    (w2:world { disjoint_worlds w1 w2 /\ disjoint_worlds w0 (join_worlds w1 w2) })
: Lemma (
    disjoint_worlds w0 w1 /\
    disjoint_worlds (join_worlds w0 w1) w2 /\
    join_worlds w0 (join_worlds w1 w2) ==
    join_worlds (join_worlds w0 w1) w2
  )
= join_istore_associative w0._1 w1._1 w2._1;
  pulse_heap_sig.sep.join_associative w0._2.pulse_heap w1._2.pulse_heap w2._2.pulse_heap

let age_to_disjoint_worlds (w1 w2: world) n :
    Lemma (requires disjoint_worlds w1 w2)
      (ensures disjoint_worlds (age_to w1 n) (age_to w2 n)) =
  assert level (age_to w1 n) == level (age_to w2 n);
  introduce forall a. istore_val_compat (read (age_to w1 n) a) (read (age_to w2 n) a) with (
    read_age_to w1 n a;
    read_age_to w2 n a
  )

let age_to_join (w1 w2: world) n :
    Lemma (requires disjoint_worlds w1 w2)
      (ensures disjoint_worlds (age_to w1 n) (age_to w2 n) /\
        age_to (join_worlds w1 w2) n == join_worlds (age_to w1 n) (age_to w2 n))
    [SMTPat (age_to (join_worlds w1 w2) n)] =
  let i1, r1 = w1 in
  let i2, r1 = w2 in
  age_to_disjoint_worlds w1 w2 n;
  assert level_istore (join_istore (age_istore_to i1 n) (age_istore_to i2 n)) == level_istore (age_istore_to i1 n);
  istore_ext (age_istore_to (join_istore i1 i2) n) (join_istore (age_istore_to i1 n) (age_istore_to i2 n)) fun a ->
    read_age_istore_to (join_istore i1 i2) n a;
    read_age_istore_to i1 n a;
    read_age_istore_to i2 n a

let star (p1 p2:slprop) : slprop =
  introduce forall is a.
      map_istore_val (approx (level_istore is)) (read_istore is a) == read_istore is a
    with approx_read_istore is a;
  F.on_dom world #(fun _ -> prop)
    fun w -> (exists w1 w2.
      disjoint_worlds w1 w2 /\ w == join_worlds w1 w2 /\ p1 w1 /\ p2 w2)

let star_commutative (p1 p2:slprop)
: Lemma (p1 `star` p2 == p2 `star` p1)
= FStar.Classical.forall_intro_2 disjoint_world_sym;
  FStar.Classical.forall_intro_2 join_worlds_commutative;
  FStar.PredicateExtensionality.predicateExtensionality world (p1 `star` p2) (p2 `star` p1)

let star_assoc (x y z:slprop)
: Lemma (star x (star y z) == star (star x y) z)
= FStar.Classical.forall_intro_2 disjoint_world_sym;
  FStar.Classical.forall_intro_2 join_worlds_commutative;
  FStar.Classical.forall_intro_3 join_worlds_associative;
  world_pred_ext (star x (star y z)) (star (star x y) z) fun w -> admit ()

let disjoint_istore_empty is : squash (disjoint_istore (empty_istore (level_istore is)) is) = ()

let join_istore_empty is : squash (join_istore (empty_istore (level_istore is)) is == is) =
  istore_ext (join_istore (empty_istore (level_istore is)) is) is fun a -> ()

let disjoint_empty w : squash (disjoint_worlds (empty (level w)) w) =
  pulse_heap_sig.sep.join_empty w._2.pulse_heap;
  pulse_heap_sig.sep.join_commutative w._2.pulse_heap pulse_heap_sig.sep.empty;
  admit ()

let join_empty w : squash (disjoint_empty w; join_worlds (empty (level w)) w == w) =
  disjoint_empty w;
  pulse_heap_sig.sep.join_empty w._2.pulse_heap;
  pulse_heap_sig.sep.join_commutative w._2.pulse_heap pulse_heap_sig.sep.empty;
  join_istore_empty w._1;
  world_ext (join_worlds (empty (level w)) w) w fun a -> ()

let star_emp (x: slprop) : squash (star x emp == x) =
  world_pred_ext (star x emp) x fun w ->
    introduce forall w. (disjoint_empty w; join_worlds (empty (level w)) w) == w with join_empty w;
    introduce forall w. (disjoint_empty w; disjoint_world_sym (empty (level w)) w; join_worlds w (empty (level w))) == w with
      (join_empty w; disjoint_empty w; join_worlds_commutative (empty (level w)) w);
    join_empty w;
    disjoint_empty w;
    let w1 = w in
    let w2 = empty (level w) in
    join_worlds_commutative w2 w;
    disjoint_world_sym w1 w2

let (exists*) #a f = admit ()

let sep_laws () =
  let open PulseCore.Semantics in
  introduce forall x y. star x y == star y x with star_commutative x y; assert commutative star;
  introduce forall x y z. star (star x y) z == star x (star y z) with star_assoc x y z; assert associative star;
  introduce forall x. star x emp == x with star_emp x; assert is_unit emp star

let lift (p: PM.slprop) : slprop =
  F.on_dom world fun w -> pulse_heap_sig.interp p ((snd w).pulse_heap)

let lift_emp_eq = admit ()
let lift_pure_eq = admit ()
let lift_later_eq #_ = admit ()
let lift_star_eq = admit ()
let lift_exists_eq = admit ()

let iref = erased (admit ())
let deq_iref = admit ()
let lower_inames = admit ()
let inames_ok = admit ()
let inames_ok_empty = admit ()

let world_invariant = admit ()

let inv = admit ()

let later (p: slprop) : slprop =
  admit ();
  F.on_dom _ fun w -> p (age1 w)

let timeless (p: slprop) = later p == p

let timeless_lift (p: PM.slprop) : squash (timeless (lift p)) =
  world_pred_ext (later (lift p)) (lift p) fun w -> ()

let hereditary_lift (p: PM.slprop) : squash (hereditary (lift p)) =
  ()

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


