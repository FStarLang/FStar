module PulseCore.IndirectionTheorySepImpl
open PulseCore.IndirectionTheory
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt
module RTC = FStar.ReflexiveTransitiveClosure
module HS = PulseCore.HeapSig
module E = PulseCore.HeapExtension
module B = PulseCore.BaseHeapSig
module IT = PulseCore.IndirectionTheory
open FStar.Ghost {erased, hide, reveal}

let address = erased nat
let pulse_mem : Type u#4 = PM.mem u#0
let pulse_core_mem : Type u#4 = PM.pulse_heap_sig.sep.core
let pulse_heap_sig : HS.heap_sig u#3 = PM.pulse_heap_sig

[@@erasable]
noeq type istore_val_ (x: Type u#4) =
  | None
  | Inv : x -> istore_val_ x
  | Pred : x -> istore_val_ x

let istore_val_le #t (x y: istore_val_ t) : prop =
  match x, y with
  | None, _ -> True
  | Inv p, Inv q -> p == q
  | Pred p, Pred q -> p == q
  | _ -> False

let map_istore_val #x #y (f: x->y) (v: istore_val_ x) : istore_val_ y =
  match v with
  | None -> None
  | Pred p -> Pred (f p)
  | Inv p -> Inv (f p)

[@@erasable]
let invariants (x:Type u#4) : Type u#4 = address ^-> istore_val_ x

let fmap #a #b (f:a -> b) 
: (invariants a ^-> invariants b)
= F.on_dom (invariants a) fun x ->
    F.on_dom address fun a ->
      map_istore_val f (x a)

let f_ext #t #s (f g: t ^-> s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x;
  F.extensionality _ _ f g

let fmap_id (a:Type) (x:invariants a)
: squash (fmap (id #a) == id #(invariants a))
= f_ext (fmap (id #a)) (id #(invariants a)) fun x ->
    f_ext (fmap (id #a) x) (id x) fun _ -> ()


let fmap_comp (a:Type) (b:Type) (c:Type) (b2c:b -> c) (a2b:a -> b)
: (squash (compose (fmap b2c) (fmap a2b) ==
            fmap (compose b2c a2b)))
= let lhs = compose (fmap b2c) (fmap a2b) in
  let rhs = fmap (compose b2c a2b) in
  f_ext lhs rhs fun x -> f_ext (lhs x) (rhs x) fun _ -> ()

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

let preworld = istore & rest
let world_pred : Type u#4 = preworld ^-> prop

let approx n : (world_pred ^-> world_pred) = approx n

let pulse_heap_le (a b: pulse_heap_sig.sep.core) : prop =
  exists c. pulse_heap_sig.sep.disjoint a c /\ b == pulse_heap_sig.sep.join a c

let istore_val = istore_val_ world_pred

let read_istore (is: istore) a : istore_val = snd (up is) a
let read (w: preworld) a = read_istore (fst w) a

let level_istore (is: istore) : nat = level is
let level_ (w: preworld) : nat = level_istore (fst w)

let approx_def n (p: world_pred) w :
    Lemma (approx n p w == (if level_ w >= n then False else p w))
      [SMTPat (approx n p w)] =
  assert_norm (approx n p w == (if level_ w >= n then False else p w))

let istore_le (x y: istore) : prop =
  level_istore x == level_istore y /\
  forall a. istore_val_le (read_istore x a) (read_istore y a)

let world_le (a b: preworld) : prop =
  let ai, ar = a in
  let bi, br = b in
  istore_le ai bi /\
  pulse_heap_le ar.pulse_heap br.pulse_heap /\
  ar.saved_credits <= br.saved_credits

let world_pred_affine (p: world_pred) : prop =
  forall a b. world_le a b /\ p a ==> p b

let age_istore_to (is: istore) (n: nat) : istore =
  down (n, snd (up is))

let age_to_ (w: preworld) (n: nat) : preworld =
  (age_istore_to (fst w) n, snd w)

let hereditary (p: world_pred) : prop =
  forall (w: preworld) (n: nat).
    n < level_ w /\ p w ==>
    p (age_to_ w n)

let slprop_ok (p: world_pred) = hereditary p /\ world_pred_affine p

let fresh_addr (is: istore) (a: address) =
  forall (b: address). b >= a ==> None? (read_istore is b)

let istore_bounded (is: istore) =
  exists a. fresh_addr is a

let istore_val_ok (v: istore_val) =
  match v with
  | None -> True
  | Pred p -> slprop_ok p
  | Inv p -> slprop_ok p

let istore_ok (is: istore) : prop =
  istore_bounded is /\
  forall a. istore_val_ok (read_istore is a)

let world_ok (w: preworld) : prop =
  istore_ok (fst w)

let slprop = p:world_pred { slprop_ok p }

let world = w:preworld { world_ok w }

let read_age_istore_to (is: istore) n a : Lemma (read_istore (age_istore_to is n) a ==
    (map_istore_val (approx n) (read_istore is a)))
    [SMTPat (read_istore (age_istore_to is n) a)] =
  up_down n (snd (up is))

let read_age_to_ (w: preworld) n a :
    Lemma (read (age_to_ w n) a == map_istore_val (approx n) (read w a)) =
  ()

let level_age_istore_to_ is n : Lemma (level_istore (age_istore_to is n) == n) [SMTPat (level_istore (age_istore_to is n))] =
  up_down n (snd (up is))

let level_age_to_ w n : Lemma (level_ (age_to_ w n) == n) =
  ()

let age_to (w: world) (n: nat) : world =
  age_to_ w n

let istore_ext (i1: istore) (i2: istore { level_istore i1 == level_istore i2 })
    (h: (a:address -> squash (read_istore i1 a == read_istore i2 a))) : squash (i1 == i2) =
  f_ext (up i1)._2 (up i2)._2 (fun a -> h a);
  down_up i1;
  down_up i2

let world_ext (w1: preworld) (w2: preworld { level_ w1 == level_ w2 /\ snd w1 == snd w2 })
    (h: (a: address -> squash (read w1 a == read w2 a))) : squash (w1 == w2) =
  istore_ext (fst w1) (fst w2) h

let world_pred_ext (f g: world_pred) (h: (w:preworld -> squash (f w <==> g w))) : squash (f == g) =
  f_ext f g fun w ->
    h w;
    PropositionalExtensionality.apply (f w) (g w)

let approx_approx m n (p: world_pred) : Lemma (approx m (approx n p) == approx (min m n) p) [SMTPat (approx m (approx n p))] =
  world_pred_ext (approx m (approx n p)) (approx (min m n) p) fun w -> ()

let age_to_age_to (w: preworld) (m n: nat) :
    Lemma (requires n <= m) (ensures age_to_ (age_to_ w m) n == age_to_ w n)
      [SMTPat (age_to_ (age_to_ w m) n)] =
  world_ext (age_to_ (age_to_ w m) n) (age_to_ w n) fun a -> ()

let age_to_rest (w: world) (n: nat) : Lemma ((age_to w n)._2 == w._2) = ()

let level (w: world) : nat = level_ w

let age1_istore (is: istore) : istore =
  if level_istore is > 0 then age_istore_to is (level_istore is - 1) else is

let age1_ (w: preworld) : w':preworld { w' == (age1_istore (fst w), snd w) } =
  if level_ w > 0 then age_to_ w (level_ w - 1) else w

let age1 (w: world) : world = age1_ w

let credits (w: world) : GTot nat =
  w._2.saved_credits

let okay_istore = is:istore { istore_ok is }

let eq_at (n:nat) (t0 t1:world_pred) =
  approx n t0 == approx n t1

let eq_at_mono (p q: world_pred) m n :
    Lemma (requires n <= m /\ eq_at m p q) (ensures eq_at n p q)
      [SMTPat (eq_at m p q); SMTPat (eq_at n p q)] =
  assert approx n p == approx n (approx m p);
  assert approx n q == approx n (approx m q)

let interp p w = p w

unfold
let istore_val_compat (x y: istore_val) =
  match x, y with
  | None, _ | _, None -> True
  | Pred p0, Pred p1 -> p0 == p1
  | Inv p0, Inv p1 -> p0 == p1
  | Inv _, Pred _ | Pred _, Inv _ -> False

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
  world_ext (age_to (empty n) m) (empty m) fun a -> read_age_to_ (empty n) m a

let emp : slprop =
  F.on_dom preworld #(fun _ -> prop) fun w -> True

let pure p : slprop = F.on_dom _ fun w -> p

let join_istore (is0:istore) (is1:istore { disjoint_istore is0 is1 }) : istore =
  mk_istore (level_istore is0) fun a ->
    match read_istore is0 a, read_istore is1 a with
    | None, None -> None
    | Pred p, _ | _, Pred p -> Pred p
    | Inv p, _ | _, Inv p -> Inv p

let read_join_istore (is0:istore) (is1:istore { disjoint_istore is0 is1 }) a :
  Lemma (read_istore (join_istore is0 is1) a ==
    (match read_istore is0 a, read_istore is1 a with
    | None, None -> None
    | Pred p, _ | _, Pred p -> Pred (approx (level_istore is0) p)
    | Inv p, _ | _, Inv p -> Inv (approx (level_istore is0) p))) =
  ()

let join_istore_commutative (is0:istore) (is1:istore { disjoint_istore is0 is1 }) :
    Lemma (join_istore is0 is1 == join_istore is1 is0) =
  istore_ext (join_istore is0 is1) (join_istore is1 is0) fun a -> ()

let approx_read_istore (is: istore) a :
    Lemma (map_istore_val (approx (level_istore is)) (read_istore is a) == read_istore is a)
    [SMTPat (read_istore is a)] =
  let n, i = up is in down_up is; up_down n i

let join_istore_refl (is: istore) : Lemma (disjoint_istore is is /\ join_istore is is == is) =
  istore_ext (join_istore is is) is fun a -> ()

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

let istore_le_iff (is1 is2: istore) :
    Lemma (istore_le is1 is2 <==> exists is3. join_istore is1 is3 == is2) =
  introduce istore_le is1 is2 ==> exists is3. join_istore is1 is3 == is2 with _.
    istore_ext (join_istore is1 is2) is2 fun _ -> ()

let disjoint_worlds (w0 w1:preworld)
: prop 
= disjoint_istore w0._1 w1._1 /\
  pulse_heap_sig.sep.disjoint w0._2.pulse_heap w1._2.pulse_heap

let disjoint_world_sym (w0 w1:preworld)
: Lemma 
  (ensures disjoint_worlds w0 w1 <==> disjoint_worlds w1 w0)
= pulse_heap_sig.sep.disjoint_sym w0._2.pulse_heap w1._2.pulse_heap

let join_worlds (w0:preworld) (w1:preworld { disjoint_worlds w0 w1 })
: preworld
= (join_istore w0._1 w1._1, ({
    pulse_heap = pulse_heap_sig.sep.join w0._2.pulse_heap w1._2.pulse_heap;
    saved_credits = w0._2.saved_credits + w1._2.saved_credits } <: rest))

open FStar.IndefiniteDescription { indefinite_description_ghost, strong_excluded_middle }

let world_le_iff (w1 w2: preworld) :
    Lemma (world_le w1 w2 <==> exists w3. join_worlds w1 w3 == w2) =
  istore_le_iff (fst w1) (fst w2);
  introduce world_le w1 w2 ==> exists w3. join_worlds w1 w3 == w2 with _. (
    assert pulse_heap_le (snd w1).pulse_heap (snd w2).pulse_heap;
    let ph3 = indefinite_description_ghost _ fun ph3 ->
      (snd w2).pulse_heap == pulse_heap_sig.sep.join (snd w1).pulse_heap ph3 in
    let is3 = indefinite_description_ghost _ fun is3 ->
      fst w2 == join_istore (fst w1) is3 in
    let sc3: nat = (snd w2).saved_credits - (snd w1).saved_credits in
    let w3: preworld = (is3, ({ pulse_heap = ph3; saved_credits = sc3 } <: rest)) in
    assert join_worlds w1 w3 == w2
  )

let join_worlds_commutative (w0:preworld) (w1:preworld { disjoint_worlds w0 w1 })
: Lemma (disjoint_worlds w1 w0 /\ join_worlds w0 w1 == join_worlds w1 w0)
= disjoint_world_sym w0 w1;
  join_istore_commutative w0._1 w1._1;
  pulse_heap_sig.sep.join_commutative w0._2.pulse_heap w1._2.pulse_heap

let join_worlds_associative
    (w0:preworld)
    (w1:preworld)
    (w2:preworld { disjoint_worlds w1 w2 /\ disjoint_worlds w0 (join_worlds w1 w2) })
: Lemma (
    disjoint_worlds w0 w1 /\
    disjoint_worlds (join_worlds w0 w1) w2 /\
    join_worlds w0 (join_worlds w1 w2) ==
    join_worlds (join_worlds w0 w1) w2
  )
= join_istore_associative w0._1 w1._1 w2._1;
  pulse_heap_sig.sep.join_associative w0._2.pulse_heap w1._2.pulse_heap w2._2.pulse_heap

let age_to_disjoint_worlds (w1 w2: preworld) n :
    Lemma (requires disjoint_worlds w1 w2)
      (ensures disjoint_worlds (age_to_ w1 n) (age_to_ w2 n)) =
  ()

let age_to_istore_join (i1 i2: istore) n :
    Lemma (requires disjoint_istore i1 i2)
      (ensures disjoint_istore (age_istore_to i1 n) (age_istore_to i2 n) /\
        age_istore_to (join_istore i1 i2) n == join_istore (age_istore_to i1 n) (age_istore_to i2 n))
    [SMTPat (age_istore_to (join_istore i1 i2) n)] =
  istore_ext (age_istore_to (join_istore i1 i2) n) (join_istore (age_istore_to i1 n) (age_istore_to i2 n)) fun a -> ()

let age_to_join (w1 w2: preworld) n :
    Lemma (requires disjoint_worlds w1 w2)
      (ensures disjoint_worlds (age_to_ w1 n) (age_to_ w2 n) /\
        age_to_ (join_worlds w1 w2) n == join_worlds (age_to_ w1 n) (age_to_ w2 n))
    [SMTPat (age_to_ (join_worlds w1 w2) n)] =
  ()

let star_ (p1 p2: world_pred) : world_pred =
  F.on_dom preworld #(fun _ -> prop)
    fun w -> (exists w1 w2.
      disjoint_worlds w1 w2 /\ w == join_worlds w1 w2 /\ p1 w1 /\ p2 w2)

[@@"opaque_to_smt"] irreducible
let indefinite_description_ghost2 (a b: Type) (p: (a -> b -> prop) { exists x y. p x y })
  : GTot (x: (a&b) { p x._1 x._2 }) =
  let x = indefinite_description_ghost a fun x -> exists y. p x y in
  let y = indefinite_description_ghost b fun y -> p x y in
  (x, y)

let star__elim (p1 p2: world_pred) (w: preworld { star_ p1 p2 w }) :
    GTot (w':(preworld & preworld) { disjoint_worlds w'._1 w'._2 /\ w == join_worlds w'._1 w'._2 /\ p1 w'._1 /\ p2 w'._2 }) =
  indefinite_description_ghost2 _ _ fun w1 w2 -> 
    disjoint_worlds w1 w2 /\ w == join_worlds w1 w2 /\ p1 w1 /\ p2 w2 

let star__intro (p1 p2: world_pred) (w w1 w2: preworld) :
    Lemma (requires disjoint_worlds w1 w2 /\ w == join_worlds w1 w2 /\ p1 w1 /\ p2 w2)
      (ensures star_ p1 p2 w) =
  ()

let star__commutative (p1 p2:world_pred)
: Lemma (p1 `star_` p2 == p2 `star_` p1)
= FStar.Classical.forall_intro_2 disjoint_world_sym;
  FStar.Classical.forall_intro_2 join_worlds_commutative;
  world_pred_ext (p1 `star_` p2) (p2 `star_` p1) fun w -> ()

let star__assoc (x y z:world_pred)
: Lemma (star_ x (star_ y z) == star_ (star_ x y) z)
=
  introduce forall x y z w. star_ x (star_ y z) w ==> star_ (star_ x y) z w with introduce _ ==> _ with _. (
    let (w1, w23) = star__elim x (star_ y z) w in
    let (w2, w3) = star__elim y z w23 in
    join_worlds_associative w1 w2 w3;
    let w12 = join_worlds w1 w2 in
    assert star_ x y w12;
    let w' = join_worlds w12 w3 in
    assert star_ (star_ x y) z w';
    assert w == w'
  );
  world_pred_ext (star_ x (star_ y z)) (star_ (star_ x y) z) fun w ->
    star__commutative y z;
    star__commutative x y;
    star__commutative x (star_ y z);
    star__commutative (star_ x y) z;
    assert star_ x (star_ y z) == star_ (star_ z y) x;
    assert star_ (star_ x y) z == star_ z (star_ y x)

let star (p1 p2:slprop) : slprop =
  introduce forall a b. world_le a b /\ star_ p1 p2 a ==> star_ p1 p2 b with introduce _ ==> _ with _. (
    world_le_iff a b;
    let c = indefinite_description_ghost _ fun c -> b == join_worlds a c in
    let (a1, a2) = star__elim p1 p2 a in
    assert b == join_worlds (join_worlds a1 a2) c;
    join_worlds_commutative (join_worlds a1 a2) c; 
    assert b == join_worlds c (join_worlds a1 a2);
    join_worlds_associative c a1 a2; 
    assert b == join_worlds (join_worlds c a1) a2;
    join_worlds_commutative c a1;
    assert b == join_worlds (join_worlds a1 c) a2;
    world_le_iff a1 (join_worlds a1 c);
    assert world_le a1 (join_worlds a1 c);
    assert p1 (join_worlds a1 c)
  );
  star_ p1 p2

let star_elim (p1 p2: slprop) (w: preworld { star p1 p2 w }) :
    GTot (w':(preworld & preworld) { disjoint_worlds w'._1 w'._2 /\ w == join_worlds w'._1 w'._2 /\ p1 w'._1 /\ p2 w'._2 }) =
  star__elim p1 p2 w

let star_intro (p1 p2: slprop) (w w1 w2: preworld) :
    Lemma (requires disjoint_worlds w1 w2 /\ w == join_worlds w1 w2 /\ p1 w1 /\ p2 w2)
      (ensures star p1 p2 w) = ()

let star_commutative (p1 p2:slprop)
: Lemma (p1 `star` p2 == p2 `star` p1)
= star__commutative p1 p2

let star_assoc (x y z:slprop)
: Lemma (star x (star y z) == star (star x y) z)
= star__assoc x y z

let disjoint_istore_empty is : squash (disjoint_istore (empty_istore (level_istore is)) is) = ()

let join_istore_empty is : squash (join_istore (empty_istore (level_istore is)) is == is) =
  istore_ext (join_istore (empty_istore (level_istore is)) is) is fun a -> ()

let disjoint_empty w : squash (disjoint_worlds w (empty (level_ w)) /\ disjoint_worlds (empty (level_ w)) w) =
  pulse_heap_sig.sep.join_empty w._2.pulse_heap;
  disjoint_world_sym w (empty (level_ w))

let join_empty w : squash (disjoint_worlds (empty (level_ w)) w /\ join_worlds (empty (level_ w)) w == w) =
  disjoint_empty w;
  pulse_heap_sig.sep.join_empty w._2.pulse_heap;
  pulse_heap_sig.sep.join_commutative w._2.pulse_heap pulse_heap_sig.sep.empty;
  join_istore_empty w._1;
  world_ext (join_worlds (empty (level_ w)) w) w fun a -> ()

let star_emp (x: slprop) : squash (star x emp == x) =
  world_pred_ext (star x emp) x fun w ->
    introduce x w ==> star x emp w with _. (
      let w2 = empty (level_ w) in
      join_empty w;
      join_worlds_commutative w2 w
    );
    introduce star x emp w ==> x w with _. (
      let (w1, w2) = star_elim x emp w in
      world_le_iff w1 w
    )

let (exists*) #a f =
  F.on_dom preworld #(fun _ -> prop) fun w ->
    exists (x:a). f x w

let sep_laws (_:unit) : squash (
  PulseCore.Semantics.(
    associative star /\
    commutative star /\
    is_unit emp star
  )
) =
  let open PulseCore.Semantics in
  introduce forall x y. star x y == star y x with star_commutative x y; assert commutative star;
  introduce forall x y z. star (star x y) z == star x (star y z) with star_assoc x y z; assert associative star;
  introduce forall x. star x emp == x with star_emp x; assert is_unit emp star

let lift (p: PM.slprop) : slprop =
  F.on_dom preworld fun w -> pulse_heap_sig.interp p ((snd w).pulse_heap)

let lift_emp_eq () =
  world_pred_ext (lift PM.emp) emp fun w ->
    pulse_heap_sig.intro_emp (snd w).pulse_heap

let lift_pure_eq p =
  world_pred_ext (lift (PM.pure p)) (pure p) fun w ->
    pulse_heap_sig.pure_interp p (snd w).pulse_heap

// let lift_later_eq #_ = admit ()

let lift_star_eq p q =
  world_pred_ext (lift (PM.star p q)) (star (lift p) (lift q)) fun w ->
    pulse_heap_sig.star_equiv p q (snd w).pulse_heap;
    introduce
      forall (m0 m1 : pulse_core_mem).
          pulse_heap_sig.sep.disjoint m0 m1 /\
          (snd w).pulse_heap == pulse_heap_sig.sep.join m0 m1 /\
          pulse_heap_sig.interp p m0 /\
          pulse_heap_sig.interp q m1
        ==> star (lift p) (lift q) w with introduce _ ==> _ with _. (
      let w0: preworld = (fst w, ({ snd w with pulse_heap = m0 } <: rest)) in
      let w1: preworld = (fst w, ({ pulse_heap = m1; saved_credits = 0 } <: rest)) in
      assert disjoint_worlds w0 w1;
      join_istore_refl (fst w);
      assert join_worlds w0 w1 == w;
      assert lift p w0;
      assert lift q w1;
      ()
    );
    introduce star (lift p) (lift q) w ==> lift (PM.star p q) w with _.
      let (w1, w2) = star_elim (lift p) (lift q) w in
      ()

// let lift_exists_eq a f =
//   world_pred_ext (lift (PM.h_exists f)) (exists* x. lift (f x)) fun w ->
//     HS.interp_exists #pulse_heap_sig f

let later (p: slprop) : slprop =
  introduce forall (w: preworld) (n: nat).
      n < level_ w /\ p (age1_ w) ==>
      p (age1_ (age_to_ w n)) with introduce _ ==> _ with _. (
    let n' = if n > 0 then n-1 else 0 in
    assert age_to_ (age1_ w) n' == age_to_ w n'
  );
  introduce forall a b. world_le a b /\ p (age1_ a) ==> p (age1_ b) with (
    world_le_iff a b;
    world_le_iff (age1_ a) (age1_ b)
  );
  F.on_dom preworld fun w -> p (age1_ w)

let timeless (p: slprop) = later p == p

let timeless_lift (p: PM.slprop) : squash (timeless (lift p)) =
  world_pred_ext (later (lift p)) (lift p) fun w -> ()

let timeless_pure (p: prop) : squash (timeless (pure p)) =
  world_pred_ext (later (pure p)) (pure p) fun w -> ()

let later_credit (n: nat) : slprop =
  F.on_dom preworld #(fun _ -> prop) fun w -> (snd w).saved_credits >= n

let later_credit_zero () : squash (later_credit 0 == emp) =
  world_pred_ext (later_credit 0) emp fun _ -> ()

let later_credit_add (m n: nat) : squash (later_credit (m + n) == later_credit m `star` later_credit n) =
  world_pred_ext (later_credit (m+n)) (later_credit m `star` later_credit n) fun w ->
    introduce later_credit (m+n) w ==> (later_credit m `star` later_credit n) w with _. (
      let w1: preworld = (fst w, ({ saved_credits = (snd w).saved_credits - n; pulse_heap = (snd w).pulse_heap } <: rest)) in
      let w2: preworld = (fst w, ({ saved_credits = n; pulse_heap = pulse_heap_sig.sep.empty } <: rest)) in
      pulse_heap_sig.sep.join_empty (snd w).pulse_heap;
      assert disjoint_worlds w1 w2;
      world_ext w (join_worlds w1 w2) fun _ -> ()
    )

let timeless_later_credit n : squash (timeless (later_credit n)) =
  world_pred_ext (later (later_credit n)) (later_credit n) fun w -> ()

let equiv p q : slprop =
  F.on_dom preworld #(fun _ -> prop) fun w -> eq_at (level_ w + 1) p q

let eq_at_elim n (p q: world_pred) (w: preworld) :
    Lemma (requires eq_at n p q /\ level_ w < n) (ensures p w <==> q w) =
  assert approx n p w == approx n q w

let equiv_comm (p q: slprop) : squash (equiv p q == equiv q p) =
  world_pred_ext (equiv p q) (equiv q p) fun _ -> ()

let equiv_elim (p q: slprop) : squash (equiv p q `star` p == equiv p q `star` q) =
  let aux (p q: slprop) (w: preworld) =
    introduce (equiv p q `star` p) w ==> (equiv p q `star` q) w with _. (
      let (w1, w2) = star_elim (equiv p q) p w in
      eq_at_elim (level_ w + 1) p q w2
    ) in
  world_pred_ext (equiv p q `star` p) (equiv p q `star` q) fun w ->
    aux p q w; aux q p w

let equiv_trans (p q r: slprop) : squash (equiv p q `star` equiv q r == equiv p q `star` equiv p r) =
  world_pred_ext (equiv p q `star` equiv q r) (equiv p q `star` equiv p r) fun w -> ()

let timeless_emp () : squash (timeless emp) =
  world_pred_ext (later emp) emp fun w -> ()

let rejuvenate1_istore (is: istore) (is': istore { istore_le is' (age1_istore is) }) :
    is'':istore { age1_istore is'' == is' /\ istore_le is'' is } =
  let is'' = mk_istore (level_istore is) fun a -> if None? (read_istore is' a) then None else read_istore is a in
  istore_ext (age1_istore is'') is' (fun a -> ());
  is''

let rejuvenate1_istore_sep (is is1': istore) (is2': istore { disjoint_istore is1' is2' /\ age1_istore is == join_istore is1' is2' }) :
    is'':(istore&istore) { age1_istore is''._1 == is1' /\ age1_istore is''._2 == is2'
      /\ disjoint_istore is''._1 is''._2 /\ is == join_istore is''._1 is''._2 } =
  let is1'' = rejuvenate1_istore is is1' in
  join_istore_commutative is1' is2';
  let is2'' = rejuvenate1_istore is is2' in
  assert disjoint_istore is1'' is2'';
  istore_ext is (join_istore is1'' is2'') (fun a -> ());
  (is1'', is2'')

let rejuvenate1 (w: preworld) (w': preworld { world_le w' (age1_ w) }) :
    w'':preworld { age1_ w'' == w' /\ world_le w'' w /\ snd w'' == snd w' } =
  (rejuvenate1_istore (fst w) (fst w'), snd w')

let rejuvenate1_sep (w w1': preworld) (w2': preworld { disjoint_worlds w1' w2' /\ age1_ w == join_worlds w1' w2' }) :
    w'':(preworld&preworld) { age1_ w''._1 == w1' /\ age1_ w''._2 == w2'
      /\ disjoint_worlds w''._1 w''._2 /\ w == join_worlds w''._1 w''._2 } =
  let (is1'', is2'') = rejuvenate1_istore_sep (fst w) (fst w1') (fst w2') in
  ((is1'', snd w1'), (is2'', snd w2'))

let later_star (p q: slprop) : squash (later (star p q) == star (later p) (later q)) =
  world_pred_ext (later (star p q)) (star (later p) (later q)) fun w ->
    introduce star p q (age1_ w) ==> star (later p) (later q) w with _. (
      let (w1', w2') = star_elim p q (age1_ w) in
      let (w1, w2) = rejuvenate1_sep w w1' w2' in
      assert later p w1;
      assert later q w2
    )

let later_exists #t (f:t->slprop) : squash (later (exists* x. f x) == (exists* x. later (f x))) =
  world_pred_ext _ _ fun w -> ()

let iref = address

let inv_prop (i:iref) (p:slprop) (is:istore) : prop =
  exists p'.
    read_istore is i == Inv p' /\
    eq_at (level_istore is) p p'

let inv (i:iref) (p:slprop) : slprop =
  F.on_dom preworld #(fun _ -> prop) fun w -> inv_prop i p (fst w)

module GS = FStar.GhostSet

let inames = GS.set iref
let inames_dec_eq : GS.decide_eq address = fun x y -> reveal x = reveal y
let single (i:iref) : inames = GS.singleton inames_dec_eq i
let add_inv (e:inames) (i:iref) : inames = GS.union (single i) e

let iname_ok (i: iref) (is: istore) =
  Inv? (read_istore is i)

let read_inv (i: iref) (is: okay_istore { iname_ok i is }) : slprop =
  let Inv p = read_istore is i in p

let read_inv_equiv i (w: world { level_ w > 0 }) (p: slprop) :
    Lemma (requires inv i p w)
      (ensures eq_at (level_ w) (read_inv i (fst w)) p) =
  ()

let inames_ok (e: inames) (is: istore) : prop =
  forall a. GS.mem a e ==> iname_ok a is

let istore_dom (is: istore) : inames =
  GS.comprehend fun a -> Inv? (read_istore is a)

let rec istore_invariant_ (ex: inames) (is: okay_istore) (f: address) : slprop =
  if reveal f = 0 then
    emp
  else
    let f': address = f - 1 in
    if GS.mem f' ex then
      istore_invariant_ ex is f'
    else
      match read_istore is f' with
      | Inv p -> later p `star` istore_invariant_ ex is f'
      | _ -> istore_invariant_ ex is f'

let rec istore_invariant__congr (ex: inames) (m: okay_istore) (f1 f2: (f:address { fresh_addr m f })) :
    Lemma (ensures istore_invariant_ ex m f1 == istore_invariant_ ex m f2) (decreases f1+f2+f2) =
  if f1 < f2 then
    istore_invariant__congr ex m f2 f1
  else if f1 > f2 then
    istore_invariant__congr ex m (f1 - 1) f2
  else
    ()

[@@"opaque_to_smt"] irreducible let some_fresh_addr (is: okay_istore) : a:address { fresh_addr is a } =
  indefinite_description_ghost address fun a -> fresh_addr is a

let istore_invariant (ex: inames) (is: okay_istore) : slprop =
  istore_invariant_ ex is (some_fresh_addr is)

let rec istore_invariant__equiv (ex: inames) (m: okay_istore) (i:iref { iname_ok i m /\ ~(GS.mem i ex) }) (f: address) :
    Lemma (istore_invariant_ ex m f ==
      (if i < f then
        istore_invariant_ (add_inv ex i) m f `star` later (read_inv i m)
      else
        istore_invariant_ (add_inv ex i) m f)) =
  if reveal f = 0 then
    ()
  else
    let f': address = f - 1 in
    istore_invariant__equiv ex m i f';
    if GS.mem f' ex then
      ()
    else
      match read_istore m f' with
      | Inv p -> sep_laws ()
      | _ -> ()

let istore_invariant_equiv (ex: inames) (m: okay_istore) (i:iref { iname_ok i m /\ ~(GS.mem i ex) }) :
    Lemma (istore_invariant ex m ==
      istore_invariant (add_inv ex i) m `star` later (read_inv i m)) =
  istore_invariant__equiv ex m i (some_fresh_addr m)

let rec istore_invariant__age (e:inames) (is: okay_istore { level_istore is > 0 }) (f: address) :
    Lemma (forall w. 1 < level_ w /\ level_ w <= level_istore is /\ istore_invariant_ e is f w ==>
        istore_invariant_ e (age1_istore is) f (age1_ w)) =
  if reveal f = 0 then
    ()
  else
    let f': address = f - 1 in
    istore_invariant__age e is f';
    if GS.mem f' e then
      ()
    else
      match read_istore is f' with
      | Inv p ->
        let Inv p' = read_istore (age1_istore is) f' in
        assert eq_at (level_istore is - 1) p p';
        introduce forall (w:preworld { 1 < level_ w /\ level_ w <= level_istore is /\ istore_invariant_ e is f w }).
            istore_invariant_ e (age1_istore is) f (age1_ w) with (
          let (w1, w2) = star_elim (later p) (istore_invariant_ e is f') w in
          assert istore_invariant_ e (age1_istore is) f' (age1_ w2);
          assert p (age1_ w1);
          eq_at_elim (level_istore is - 1) p p' (age1_ (age1_ w1));
          star_intro (later (later p')) (later (istore_invariant_ e (age1_istore is) f')) w w1 w2;
          later_star (later p') (istore_invariant_ e (age1_istore is) f');
          assert (later p' `star` istore_invariant_ e (age1_istore is) f') (age1_ w)
        )
      | _ ->
        ()

let istore_invariant_age (e:inames) (is: okay_istore { level_istore is > 0 })
    (w: preworld { 1 < level_ w /\ level_ w <= level_istore is }) :
    Lemma (istore_invariant e is w ==> istore_invariant e (age1_istore is) (age1_ w)) =
  introduce istore_invariant e is w ==> istore_invariant e (age1_istore is) (age1_ w) with _. (
    istore_invariant__age e is (some_fresh_addr is);
    istore_invariant__congr e (age1_istore is) (some_fresh_addr is) (some_fresh_addr (age1_istore is))
  )

let gs_disjoint_elim #t (a: GS.set t) (b: GS.set t { GS.disjoint a b }) (x: t { GS.mem x a }) :
    Lemma (~(GS.mem x b)) =
  ()

let rec istore_invariant__disjoint (e1 e2:inames) (m1 m2:okay_istore) (f: iref) :
    Lemma (requires
      disjoint_istore m1 m2 /\
      GS.disjoint (istore_dom m1) (istore_dom m2) /\
      GS.disjoint e1 (istore_dom m2) /\ GS.disjoint e2 (istore_dom m1))
    (ensures 
      istore_invariant_ (GS.union e1 e2) (join_istore m1 m2) f ==
        istore_invariant_ e1 m1 f `star` istore_invariant_ e2 m2 f) =
  if reveal f = 0 then
    sep_laws ()
  else
    let f': address = f - 1 in
    istore_invariant__disjoint e1 e2 m1 m2 f';
    if GS.mem f' (GS.union e1 e2) then
      ()
    else
      match read_istore (join_istore m1 m2) f' with
      | Inv p -> 
        if Inv? (read_istore m1 f') then (
          gs_disjoint_elim (istore_dom m1) (istore_dom m2) f';
          sep_laws ()
        ) else if Inv? (read_istore m2 f') then (
          gs_disjoint_elim (istore_dom m2) (istore_dom m1) f';
          sep_laws ()
        ) else
          assert False
      | _ -> ()

let istore_invariant_disjoint (e1 e2:inames) (m1 m2:okay_istore) :
    Lemma (requires
      disjoint_istore m1 m2 /\
      GS.disjoint (istore_dom m1) (istore_dom m2) /\
      GS.disjoint e1 (istore_dom m2) /\ GS.disjoint e2 (istore_dom m1))
    (ensures 
      istore_invariant (GS.union e1 e2) (join_istore m1 m2) ==
        istore_invariant e1 m1 `star` istore_invariant e2 m2) =
  let m = join_istore m1 m2 in
  istore_invariant__congr e1 m1 (some_fresh_addr m1) (some_fresh_addr m);
  istore_invariant__congr e2 m2 (some_fresh_addr m2) (some_fresh_addr m);
  istore_invariant__disjoint e1 e2 m1 m2 (some_fresh_addr m)

let rec istore_invariant__mono (ex1: inames) (ex2: inames)
    (m: okay_istore { forall i. GS.mem i (istore_dom m) /\ GS.mem i ex1 ==> GS.mem i ex2 })
    (f: address) (w: preworld) :
    squash (istore_invariant_ ex1 m f w ==> istore_invariant_ ex2 m f w) =
  introduce _ ==> _ with _.
  if reveal f = 0 then
    ()
  else
    let f': address = f - 1 in
    if GS.mem f' ex1 then
      istore_invariant__mono ex1 ex2 m f' w
    else
      match read_istore m f' with
      | Inv p ->
        let (w1, w2) = star_elim (later p) (istore_invariant_ ex1 m f') w in
        istore_invariant__mono ex1 ex2 m f' w2;
        join_worlds_commutative w1 w2;
        assert world_le w2 w
      | _ ->
        istore_invariant__mono ex1 ex2 m f' w

let istore_invariant_mono (ex1: inames) (ex2: inames)
    (m: okay_istore { forall i. GS.mem i (istore_dom m) /\ GS.mem i ex1 ==> GS.mem i ex2 })
    (w: preworld) :
    squash (istore_invariant ex1 m w ==> istore_invariant ex2 m w) =
  istore_invariant__mono ex1 ex2 m (some_fresh_addr m) w

let gs_diff #t (a b: GS.set t) : GS.set t =
  GS.comprehend fun i -> GS.mem i a && not (GS.mem i b)

let istore_invariant_disjoint' (e f:inames) (p0 p1:slprop) (m0 m1:world) :
    Lemma (requires
      disjoint_worlds m0 m1 /\
      GS.disjoint (istore_dom (fst m0)) (istore_dom (fst m1)) /\
      (p0 `star` istore_invariant e (fst m0)) m0 /\
      (p1 `star` istore_invariant f (fst m1)) m1)
    (ensures (
      let m = join_worlds m0 m1 in
      (p0 `star` p1 `star` istore_invariant (GS.union e f) (fst m)) m)) =
  let e' = gs_diff e (istore_dom (fst m1)) in
  let _ : squash ((p0 `star` istore_invariant e' (fst m0)) m0) =
    let (w1, w2) = star_elim p0 (istore_invariant e (fst m0)) m0 in
    istore_invariant_mono e e' (fst m0) w2;
    star_intro p0 (istore_invariant e' (fst m0)) m0 w1 w2 in
  let f' = gs_diff f (istore_dom (fst m0)) in
  let _ : squash ((p1 `star` istore_invariant f' (fst m1)) m1) =
    let (w1, w2) = star_elim p1 (istore_invariant f (fst m1)) m1 in
    istore_invariant_mono f f' (fst m1) w2;
    star_intro p1 (istore_invariant f' (fst m1)) m1 w1 w2 in
  istore_invariant_disjoint e' f' (fst m0) (fst m1);
  let g = GS.union e' f' in
  let m: world = join_worlds m0 m1 in
  star_intro
    (p0 `star` istore_invariant e' (fst m0)) (p1 `star` istore_invariant f' (fst m1))
    m m0 m1;
  let _ : squash (
    (p0 `star` istore_invariant e' (fst m0)) `star` (p1 `star` istore_invariant f' (fst m1)) ==
    (p0 `star` p1) `star` (istore_invariant (GS.union e' f') (fst m))
  ) = sep_laws () in
  let (w1, w2) = star_elim (p0 `star` p1) (istore_invariant (GS.union e' f') (fst m)) m in
  istore_invariant_mono (GS.union e' f') (GS.union e f) (fst m) w2;
  star_intro (p0 `star` p1) (istore_invariant (GS.union e f) (fst m)) m w1 w2

let max x y = if x > y then x else y

let istore_single n (a: iref) (p: slprop) : okay_istore =
  let is = mk_istore n fun b -> if reveal a = reveal b then Inv p else None in
  assert fresh_addr is (a + 1);
  is

let rec istore_single_invariant_ n a p f : squash (istore_invariant_ (single a) (istore_single n a p) f == emp) =
  if reveal f = 0 then
    ()
  else
    istore_single_invariant_ n a p (f - 1)

let istore_single_invariant n a p : Lemma (istore_invariant (single a) (istore_single n a p) == emp) =
  istore_single_invariant_ n a p (some_fresh_addr (istore_single n a p))

let fresh_inv (p: slprop) (is: okay_istore) (a: iref { None? (read_istore is a) }) :
    is':okay_istore {
      disjoint_istore is is' /\
      inv_prop a p is' /\
      istore_invariant (single a) is' == emp /\
      GS.disjoint (istore_dom is) (istore_dom is')
    } =
  let is' = istore_single (level_istore is) a p in
  istore_single_invariant (level_istore is) a p;
  is'

let non_pulse_prop (p: slprop) =
  forall i r1 r2. p (i, r1) <==> p (i, r2)

let dup_inv_equiv i p : Lemma (inv i p == (inv i p `star` inv i p)) =
  world_pred_ext (inv i p) (inv i p `star` inv i p) fun w ->
    introduce inv i p w ==> star (inv i p) (inv i p) w with _. (
      let w2 = (fst w, snd (empty (level_ w))) in
      assert inv i p w;
      assert inv i p w2;
      pulse_heap_sig.sep.join_empty (snd w).pulse_heap;
      assert disjoint_worlds w w2;
      world_ext w (join_worlds w w2) (fun a -> ())
    )

let invariant_name_identifies_invariant (i: iref) (p q: slprop) (w: preworld { level_ w > 0 }) :
    squash (star (inv i p) (inv i q) w ==> later (equiv p q) w) =
  ()

// ----------------

// inv i p  @ w_n  // eq_at n p p'

// i -> Some p' /\ eq_at (n - 1) p p'   @ (agew1 w_n)

// p' (age1 w_n) ///because w_n is an iworld

// have p (age1 w_n) because level (age1 w_n) = n - 1


