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
let timeless_mem : Type u#4 = PM.mem u#0
let timeless_heap_sig : HS.heap_sig u#3 = PM.pulse_heap_sig

[@@erasable]
noeq type hogs_val_ (x: Type u#4) =
  | None
  | Inv : x -> hogs_val_ x
  | Pred : x -> hogs_val_ x

let hogs_val_le #t (x y: hogs_val_ t) : prop =
  match x, y with
  | None, _ -> True
  | Inv p, Inv q -> p == q
  | Pred p, Pred q -> p == q
  | _ -> False

let map_hogs_val #x #y (f: x->y) (v: hogs_val_ x) : hogs_val_ y =
  match v with
  | None -> None
  | Pred p -> Pred (f p)
  | Inv p -> Inv (f p)

[@@erasable]
let invariants (x:Type u#4) : Type u#4 = address ^-> hogs_val_ x

let fmap #a #b (f:a -> b) 
: (invariants a ^-> invariants b)
= F.on_dom (invariants a) fun x ->
    F.on_dom address fun a ->
      map_hogs_val f (x a)

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
  timeless_heap : timeless_heap_sig.mem;
  saved_credits : erased nat;
}

let functor_heap : functor u#3 invariants = {
  fmap = fmap;
  fmap_id = fmap_id;
  fmap_comp = fmap_comp;
  other = rest;
}

let hogs : Type u#4 = knot_t functor_heap

let premem = hogs & rest
let mem_pred : Type u#4 = premem ^-> prop

let approx n : (mem_pred ^-> mem_pred) = approx n

let timeless_heap_le (a b: timeless_heap_sig.mem) : prop =
  exists c. timeless_heap_sig.sep.disjoint a c /\ b == timeless_heap_sig.sep.join a c

let hogs_val = hogs_val_ mem_pred

let read_hogs (is: hogs) a : hogs_val = unpack is a
let read (w: premem) a = read_hogs (fst w) a

let level_hogs (is: hogs) : GTot nat = level is
let level_ (w: premem) : GTot nat = level_hogs (fst w)

let approx_def n (p: mem_pred) w :
    Lemma (approx n p w == (if level_ w >= n then False else p w))
      [SMTPat (approx n p w)] =
  assert_norm (approx n p w == (if level_ w >= n then False else p w))

let hogs_le (x y: hogs) : prop =
  level_hogs x == level_hogs y /\
  forall a. hogs_val_le (read_hogs x a) (read_hogs y a)

let mem_le (a b: premem) : prop =
  let ai, ar = a in
  let bi, br = b in
  hogs_le ai bi /\
  timeless_heap_le ar.timeless_heap br.timeless_heap /\
  ar.saved_credits <= br.saved_credits

let mem_pred_affine (p: mem_pred) : prop =
  forall a b. mem_le a b /\ p a ==> p b

let age_hogs_to (is: hogs) (n: erased nat) : hogs =
  pack n (unpack is)

let age_to_ (w: premem) (n: erased nat) : premem =
  (age_hogs_to (fst w) n, snd w)

let hereditary (p: mem_pred) : prop =
  forall (w: premem) (n: erased nat).
    n < level_ w /\ p w ==>
    p (age_to_ w n)

let slprop_ok (p: mem_pred) = hereditary p /\ mem_pred_affine p

let fresh_addr (is: hogs) (a: address) =
  forall (b: address). b >= a ==> None? (read_hogs is b)

let hogs_bounded (is: hogs) =
  exists a. fresh_addr is a

let hogs_val_ok (v: hogs_val) =
  match v with
  | None -> True
  | Pred p -> slprop_ok p
  | Inv p -> slprop_ok p

let hogs_ok (is: hogs) : prop =
  hogs_bounded is /\
  forall a. hogs_val_ok (read_hogs is a)

let mem_ok (w: premem) : prop =
  hogs_ok (fst w)

let slprop = p:mem_pred { slprop_ok p }

let mem = w:premem { mem_ok w }

let read_age_hogs_to (is: hogs) (n: erased nat) a : Lemma (read_hogs (age_hogs_to is n) a ==
    (map_hogs_val (approx n) (read_hogs is a)))
    [SMTPat (read_hogs (age_hogs_to is n) a)] =
  unpack_pack n (unpack is)

let read_age_to_ (w: premem) (n: erased nat) a :
    Lemma (read (age_to_ w n) a == map_hogs_val (approx n) (read w a)) =
  ()

let level_age_hogs_to_ is (n: erased nat) :
    Lemma (level_hogs (age_hogs_to is n) == reveal n) [SMTPat (level_hogs (age_hogs_to is n))] =
  unpack_pack n (unpack is)

let level_age_to_ w (n: erased nat) : Lemma (level_ (age_to_ w n) == reveal n) =
  ()

let age_to (w: mem) (n: erased nat) : mem =
  age_to_ w n

let hogs_ext (i1: hogs) (i2: hogs { level_hogs i1 == level_hogs i2 })
    (h: (a:address -> squash (read_hogs i1 a == read_hogs i2 a))) : squash (i1 == i2) =
  f_ext (unpack i1) (unpack i2) (fun a -> h a);
  pack_unpack i1;
  pack_unpack i2

let mem_ext (w1: premem) (w2: premem { level_ w1 == level_ w2 /\ snd w1 == snd w2 })
    (h: (a: address -> squash (read w1 a == read w2 a))) : squash (w1 == w2) =
  hogs_ext (fst w1) (fst w2) h

let mem_pred_ext (f g: mem_pred) (h: (w:premem -> squash (f w <==> g w))) : squash (f == g) =
  f_ext f g fun w ->
    h w;
    PropositionalExtensionality.apply (f w) (g w)

let approx_approx m n (p: mem_pred) : Lemma (approx m (approx n p) == approx (min m n) p) [SMTPat (approx m (approx n p))] =
  mem_pred_ext (approx m (approx n p)) (approx (min m n) p) fun w -> ()

let age_to_age_to (w: premem) (m n: erased nat) :
    Lemma (requires n <= m) (ensures age_to_ (age_to_ w m) n == age_to_ w n)
      [SMTPat (age_to_ (age_to_ w m) n)] =
  mem_ext (age_to_ (age_to_ w m) n) (age_to_ w n) fun a -> ()

let age_to_rest (w: mem) (n: erased nat) : Lemma ((age_to w n)._2 == w._2) = ()

let level (w: mem) : GTot nat = level_ w

irreducible [@@"opaque_to_smt"]
let reveal_hogs (is: erased hogs) : is':hogs { is' == reveal is } =
  pack_unpack is;
  pack (IT.level is) (unpack is)

let approx_read_hogs (is: hogs) a :
    Lemma (map_hogs_val (approx (level_hogs is)) (read_hogs is a) == read_hogs is a)
    [SMTPat (read_hogs is a)] =
  pack_unpack is; unpack_pack (level_hogs is) (unpack is)

let age1_hogs (is: hogs) : is':hogs { level_hogs is == 0 ==> is' == is } =
  hogs_ext (age_hogs_to is (level_hogs is)) is (fun _ -> ());
  age_hogs_to is (if level_hogs is > 0 then level_hogs is - 1 else 0)

let hogs_ok_age1 (is: hogs) :
    Lemma (requires hogs_ok is) (ensures hogs_ok (age1_hogs is)) [SMTPat (hogs_ok (age1_hogs is))] =
  ()

let age1_ (w: premem) : w':premem { if level_ w > 0 then w' == age_to_ w (level_ w - 1) else w' == w } =
  (age1_hogs (fst w), snd w)

let age1 (w: mem) : mem = age1_ w

let credits (w: mem) : GTot nat =
  w._2.saved_credits

let okay_hogs = is:hogs { hogs_ok is }

let eq_at (n:nat) (t0 t1:mem_pred) =
  approx n t0 == approx n t1

let eq_at_mono (p q: mem_pred) m n :
    Lemma (requires n <= m /\ eq_at m p q) (ensures eq_at n p q)
      [SMTPat (eq_at m p q); SMTPat (eq_at n p q)] =
  assert approx n p == approx n (approx m p);
  assert approx n q == approx n (approx m q)

let interp p w = p w

unfold
let hogs_val_compat (x y: hogs_val) =
  match x, y with
  | None, _ | _, None -> True
  | Pred p0, Pred p1 -> p0 == p1
  | Inv p0, Inv p1 -> p0 == p1
  | Inv _, Pred _ | Pred _, Inv _ -> False

let disjoint_hogs (is0 is1:hogs) =
  level_hogs is0 == level_hogs is1 /\
  (forall a. hogs_val_compat (read_hogs is0 a) (read_hogs is1 a))

let disjoint_hogs_read is0 is1 a :
    Lemma (requires disjoint_hogs is0 is1)
      (ensures hogs_val_compat (read_hogs is0 a) (read_hogs is1 a))
      [SMTPatOr [
        [SMTPat (disjoint_hogs is0 is1); SMTPat (read_hogs is0 a)];
        [SMTPat (disjoint_hogs is0 is1); SMTPat (read_hogs is1 a)];
      ]] =
  ()

let mk_hogs n (is: address -> hogs_val) : hogs =
  pack n (F.on_dom address is)

let level_mk_hogs (n: erased nat) is :
    Lemma (level_hogs (mk_hogs n is) == reveal n) [SMTPat (level_hogs (mk_hogs n is))] =
  unpack_pack #_ #functor_heap n (F.on_dom address is)

let read_mk_hogs (n: erased nat) is a :
    Lemma (read_hogs (mk_hogs n is) a == map_hogs_val (approx n) (is a))
      [SMTPat (read_hogs (mk_hogs n is) a)] =
  let is' = F.on_dom address is in
  unpack_pack #_ #functor_heap n is';
  assert_norm (fmap (approx n) is' a == map_hogs_val (approx n) (is' a))

let empty_hogs n : hogs = mk_hogs n fun _ -> None
let empty_rest : rest = { timeless_heap = timeless_heap_sig.sep.empty; saved_credits = 0 }
let empty n : mem = (empty_hogs n, empty_rest)

let age_to_empty (m n: erased nat) : Lemma (age_to (empty n) m == empty m) [SMTPat (age_to (empty n) m)] =
  mem_ext (age_to (empty n) m) (empty m) fun a -> read_age_to_ (empty n) m a

let emp : slprop =
  F.on_dom premem #(fun _ -> prop) fun w -> True

let pure p : slprop = F.on_dom _ fun w -> p

let join_hogs (is0:hogs) (is1:hogs { disjoint_hogs is0 is1 }) : hogs =
  mk_hogs (level_hogs is0) fun a ->
    match read_hogs is0 a, read_hogs is1 a with
    | None, None -> None
    | Pred p, _ | _, Pred p -> Pred p
    | Inv p, _ | _, Inv p -> Inv p

let read_join_hogs (is0:hogs) (is1:hogs { disjoint_hogs is0 is1 }) a :
  Lemma (read_hogs (join_hogs is0 is1) a ==
    (match read_hogs is0 a, read_hogs is1 a with
    | None, None -> None
    | Pred p, _ | _, Pred p -> Pred (approx (level_hogs is0) p)
    | Inv p, _ | _, Inv p -> Inv (approx (level_hogs is0) p))) =
  ()

let join_hogs_commutative (is0:hogs) (is1:hogs { disjoint_hogs is0 is1 }) :
    Lemma (join_hogs is0 is1 == join_hogs is1 is0) =
  hogs_ext (join_hogs is0 is1) (join_hogs is1 is0) fun a -> ()

let join_hogs_refl (is: hogs) : Lemma (disjoint_hogs is is /\ join_hogs is is == is) =
  hogs_ext (join_hogs is is) is fun a -> ()

let join_hogs_associative
    (is0:hogs)
    (is1:hogs)
    (is2:hogs { 
      disjoint_hogs is1 is2 /\
      disjoint_hogs is0 (join_hogs is1 is2)
    })
: Lemma (
    disjoint_hogs is0 is1 /\
    disjoint_hogs (join_hogs is0 is1) is2 /\
    join_hogs is0 (join_hogs is1 is2) ==
    join_hogs (join_hogs is0 is1) is2
  )
=
  hogs_ext (join_hogs is0 (join_hogs is1 is2)) (join_hogs (join_hogs is0 is1) is2) fun a -> ()

let hogs_le_iff (is1 is2: hogs) :
    Lemma (hogs_le is1 is2 <==> exists is3. join_hogs is1 is3 == is2) =
  introduce hogs_le is1 is2 ==> exists is3. join_hogs is1 is3 == is2 with _.
    hogs_ext (join_hogs is1 is2) is2 fun _ -> ()

let disjoint_mem (w0 w1:premem)
: prop 
= disjoint_hogs w0._1 w1._1 /\
  timeless_heap_sig.sep.disjoint w0._2.timeless_heap w1._2.timeless_heap

let disjoint_mem_sym (w0 w1:premem)
: Lemma 
  (ensures disjoint_mem w0 w1 <==> disjoint_mem w1 w0)
= timeless_heap_sig.sep.disjoint_sym w0._2.timeless_heap w1._2.timeless_heap

let join_mem (w0:premem) (w1:premem { disjoint_mem w0 w1 })
: premem
= (join_hogs w0._1 w1._1, ({
    timeless_heap = timeless_heap_sig.sep.join w0._2.timeless_heap w1._2.timeless_heap;
    saved_credits = w0._2.saved_credits + w1._2.saved_credits } <: rest))

open FStar.IndefiniteDescription { indefinite_description_ghost, strong_excluded_middle }

let mem_le_iff (w1 w2: premem) :
    Lemma (mem_le w1 w2 <==> exists w3. join_mem w1 w3 == w2) =
  hogs_le_iff (fst w1) (fst w2);
  introduce mem_le w1 w2 ==> exists w3. join_mem w1 w3 == w2 with _. (
    assert timeless_heap_le (snd w1).timeless_heap (snd w2).timeless_heap;
    let ph3 = indefinite_description_ghost _ fun ph3 ->
      (snd w2).timeless_heap == timeless_heap_sig.sep.join (snd w1).timeless_heap ph3 in
    let is3 = indefinite_description_ghost _ fun is3 ->
      fst w2 == join_hogs (fst w1) is3 in
    let sc3: nat = (snd w2).saved_credits - (snd w1).saved_credits in
    let w3: premem = (is3, ({ timeless_heap = ph3; saved_credits = sc3 } <: rest)) in
    assert join_mem w1 w3 == w2
  )

let join_mem_commutative (w0:premem) (w1:premem { disjoint_mem w0 w1 })
: Lemma (disjoint_mem w1 w0 /\ join_mem w0 w1 == join_mem w1 w0)
= disjoint_mem_sym w0 w1;
  join_hogs_commutative w0._1 w1._1;
  timeless_heap_sig.sep.join_commutative w0._2.timeless_heap w1._2.timeless_heap

let join_mem_associative
    (w0:premem)
    (w1:premem)
    (w2:premem { disjoint_mem w1 w2 /\ disjoint_mem w0 (join_mem w1 w2) })
: Lemma (
    disjoint_mem w0 w1 /\
    disjoint_mem (join_mem w0 w1) w2 /\
    join_mem w0 (join_mem w1 w2) ==
    join_mem (join_mem w0 w1) w2
  )
= join_hogs_associative w0._1 w1._1 w2._1;
  timeless_heap_sig.sep.join_associative w0._2.timeless_heap w1._2.timeless_heap w2._2.timeless_heap

let age_to_disjoint_mem (w1 w2: premem) n :
    Lemma (requires disjoint_mem w1 w2)
      (ensures disjoint_mem (age_to_ w1 n) (age_to_ w2 n)) =
  ()

let age_to_hogs_join (i1 i2: hogs) n :
    Lemma (requires disjoint_hogs i1 i2)
      (ensures disjoint_hogs (age_hogs_to i1 n) (age_hogs_to i2 n) /\
        age_hogs_to (join_hogs i1 i2) n == join_hogs (age_hogs_to i1 n) (age_hogs_to i2 n))
    [SMTPat (age_hogs_to (join_hogs i1 i2) n)] =
  hogs_ext (age_hogs_to (join_hogs i1 i2) n) (join_hogs (age_hogs_to i1 n) (age_hogs_to i2 n)) fun a -> ()

let age_to_join (w1 w2: premem) n :
    Lemma (requires disjoint_mem w1 w2)
      (ensures disjoint_mem (age_to_ w1 n) (age_to_ w2 n) /\
        age_to_ (join_mem w1 w2) n == join_mem (age_to_ w1 n) (age_to_ w2 n))
    [SMTPat (age_to_ (join_mem w1 w2) n)] =
  ()

let star_ (p1 p2: mem_pred) : mem_pred =
  F.on_dom premem #(fun _ -> prop)
    fun w -> (exists w1 w2.
      disjoint_mem w1 w2 /\ w == join_mem w1 w2 /\ p1 w1 /\ p2 w2)

[@@"opaque_to_smt"] irreducible
let indefinite_description_ghost2 (a b: Type) (p: (a -> b -> prop) { exists x y. p x y })
  : GTot (x: (a&b) { p x._1 x._2 }) =
  let x = indefinite_description_ghost a fun x -> exists y. p x y in
  let y = indefinite_description_ghost b fun y -> p x y in
  (x, y)

let star__elim (p1 p2: mem_pred) (w: premem { star_ p1 p2 w }) :
    GTot (w':(premem & premem) { disjoint_mem w'._1 w'._2 /\ w == join_mem w'._1 w'._2 /\ p1 w'._1 /\ p2 w'._2 }) =
  indefinite_description_ghost2 _ _ fun w1 w2 -> 
    disjoint_mem w1 w2 /\ w == join_mem w1 w2 /\ p1 w1 /\ p2 w2 

let star__intro (p1 p2: mem_pred) (w w1 w2: premem) :
    Lemma (requires disjoint_mem w1 w2 /\ w == join_mem w1 w2 /\ p1 w1 /\ p2 w2)
      (ensures star_ p1 p2 w) =
  ()

let star__commutative (p1 p2:mem_pred)
: Lemma (p1 `star_` p2 == p2 `star_` p1)
= FStar.Classical.forall_intro_2 disjoint_mem_sym;
  FStar.Classical.forall_intro_2 join_mem_commutative;
  mem_pred_ext (p1 `star_` p2) (p2 `star_` p1) fun w -> ()

let star__assoc (x y z:mem_pred)
: Lemma (star_ x (star_ y z) == star_ (star_ x y) z)
=
  introduce forall x y z w. star_ x (star_ y z) w ==> star_ (star_ x y) z w with introduce _ ==> _ with _. (
    let (w1, w23) = star__elim x (star_ y z) w in
    let (w2, w3) = star__elim y z w23 in
    join_mem_associative w1 w2 w3;
    let w12 = join_mem w1 w2 in
    assert star_ x y w12;
    let w' = join_mem w12 w3 in
    assert star_ (star_ x y) z w';
    assert w == w'
  );
  mem_pred_ext (star_ x (star_ y z)) (star_ (star_ x y) z) fun w ->
    star__commutative y z;
    star__commutative x y;
    star__commutative x (star_ y z);
    star__commutative (star_ x y) z;
    assert star_ x (star_ y z) == star_ (star_ z y) x;
    assert star_ (star_ x y) z == star_ z (star_ y x)

let star (p1 p2:slprop) : slprop =
  introduce forall a b. mem_le a b /\ star_ p1 p2 a ==> star_ p1 p2 b with introduce _ ==> _ with _. (
    mem_le_iff a b;
    let c = indefinite_description_ghost _ fun c -> b == join_mem a c in
    let (a1, a2) = star__elim p1 p2 a in
    assert b == join_mem (join_mem a1 a2) c;
    join_mem_commutative (join_mem a1 a2) c; 
    assert b == join_mem c (join_mem a1 a2);
    join_mem_associative c a1 a2; 
    assert b == join_mem (join_mem c a1) a2;
    join_mem_commutative c a1;
    assert b == join_mem (join_mem a1 c) a2;
    mem_le_iff a1 (join_mem a1 c);
    assert mem_le a1 (join_mem a1 c);
    assert p1 (join_mem a1 c)
  );
  star_ p1 p2

let star_elim (p1 p2: slprop) (w: premem { star p1 p2 w }) :
    GTot (w':(premem & premem) { disjoint_mem w'._1 w'._2 /\ w == join_mem w'._1 w'._2 /\ p1 w'._1 /\ p2 w'._2 }) =
  star__elim p1 p2 w

let star_elim' (p1 p2: slprop) (w: mem { star p1 p2 w }) :
    GTot (w':(mem & mem) { disjoint_mem w'._1 w'._2 /\ w == join_mem w'._1 w'._2 /\ p1 w'._1 /\ p2 w'._2 }) =
  let w1, w2 = star_elim p1 p2 w in
  w1, w2

let star_intro (p1 p2: slprop) (w w1 w2: premem) :
    Lemma (requires disjoint_mem w1 w2 /\ w == join_mem w1 w2 /\ p1 w1 /\ p2 w2)
      (ensures star p1 p2 w) = ()

let star_commutative (p1 p2:slprop)
: Lemma (p1 `star` p2 == p2 `star` p1)
= star__commutative p1 p2

let star_assoc (x y z:slprop)
: Lemma (star x (star y z) == star (star x y) z)
= star__assoc x y z

let disjoint_hogs_empty is : squash (disjoint_hogs (empty_hogs (level_hogs is)) is) = ()

let join_hogs_empty is : squash (join_hogs (empty_hogs (level_hogs is)) is == is) =
  hogs_ext (join_hogs (empty_hogs (level_hogs is)) is) is fun a -> ()

let disjoint_empty w : squash (disjoint_mem w (empty (level_ w)) /\ disjoint_mem (empty (level_ w)) w) =
  timeless_heap_sig.sep.join_empty w._2.timeless_heap;
  disjoint_mem_sym w (empty (level_ w))

let join_empty w : squash (disjoint_mem (empty (level_ w)) w /\ join_mem (empty (level_ w)) w == w) =
  disjoint_empty w;
  timeless_heap_sig.sep.join_empty w._2.timeless_heap;
  timeless_heap_sig.sep.join_commutative w._2.timeless_heap timeless_heap_sig.sep.empty;
  join_hogs_empty w._1;
  mem_ext (join_mem (empty (level_ w)) w) w fun a -> ()

let star_emp (x: slprop) : squash (star x emp == x) =
  mem_pred_ext (star x emp) x fun w ->
    introduce x w ==> star x emp w with _. (
      let w2 = empty (level_ w) in
      join_empty w;
      join_mem_commutative w2 w
    );
    introduce star x emp w ==> x w with _. (
      let (w1, w2) = star_elim x emp w in
      mem_le_iff w1 w
    )

let (exists*) #a f =
  F.on_dom premem #(fun _ -> prop) fun w ->
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
  F.on_dom premem fun w -> timeless_heap_sig.interp p ((snd w).timeless_heap)

let lift_emp_eq () =
  mem_pred_ext (lift PM.emp) emp fun w ->
    timeless_heap_sig.intro_emp (snd w).timeless_heap

let lift_pure_eq p =
  mem_pred_ext (lift (PM.pure p)) (pure p) fun w ->
    timeless_heap_sig.pure_interp p (snd w).timeless_heap

let lift_star_eq p q =
  mem_pred_ext (lift (PM.star p q)) (star (lift p) (lift q)) fun w ->
    timeless_heap_sig.star_equiv p q (snd w).timeless_heap;
    introduce
      forall (m0 m1 : timeless_mem).
          timeless_heap_sig.sep.disjoint m0 m1 /\
          (snd w).timeless_heap == timeless_heap_sig.sep.join m0 m1 /\
          timeless_heap_sig.interp p m0 /\
          timeless_heap_sig.interp q m1
        ==> star (lift p) (lift q) w with introduce _ ==> _ with _. (
      let w0: premem = (fst w, ({ snd w with timeless_heap = m0 } <: rest)) in
      let w1: premem = (fst w, ({ timeless_heap = m1; saved_credits = 0 } <: rest)) in
      assert disjoint_mem w0 w1;
      join_hogs_refl (fst w);
      assert join_mem w0 w1 == w;
      assert lift p w0;
      assert lift q w1;
      ()
    );
    introduce star (lift p) (lift q) w ==> lift (PM.star p q) w with _.
      let (w1, w2) = star_elim (lift p) (lift q) w in
      ()

// let lift_exists_eq a f =
//   mem_pred_ext (lift (PM.h_exists f)) (exists* x. lift (f x)) fun w ->
//     HS.interp_exists #timeless_heap_sig f

let later (p: slprop) : slprop =
  introduce forall (w: premem) (n: erased nat).
      n < level_ w /\ p (age1_ w) ==>
      p (age1_ (age_to_ w n)) with introduce _ ==> _ with _. (
    let n': erased nat = if n > 0 then n-1 else 0 in
    assert age_to_ (age1_ w) n' == age_to_ w n'
  );
  introduce forall a b. mem_le a b /\ p (age1_ a) ==> p (age1_ b) with (
    mem_le_iff a b;
    mem_le_iff (age1_ a) (age1_ b)
  );
  F.on_dom premem fun w -> p (age1_ w)

let timeless (p: slprop) = later p == p

let timeless_lift (p: PM.slprop) : squash (timeless (lift p)) =
  mem_pred_ext (later (lift p)) (lift p) fun w -> ()

let timeless_pure (p: prop) : squash (timeless (pure p)) =
  mem_pred_ext (later (pure p)) (pure p) fun w -> ()

let later_credit (n: nat) : slprop =
  F.on_dom premem #(fun _ -> prop) fun w -> (snd w).saved_credits >= n

let later_credit_zero () : squash (later_credit 0 == emp) =
  mem_pred_ext (later_credit 0) emp fun _ -> ()

let later_credit_add (m n: nat) : squash (later_credit (m + n) == later_credit m `star` later_credit n) =
  mem_pred_ext (later_credit (m+n)) (later_credit m `star` later_credit n) fun w ->
    introduce later_credit (m+n) w ==> (later_credit m `star` later_credit n) w with _. (
      let w1: premem = (fst w, ({ saved_credits = (snd w).saved_credits - n; timeless_heap = (snd w).timeless_heap } <: rest)) in
      let w2: premem = (fst w, ({ saved_credits = n; timeless_heap = timeless_heap_sig.sep.empty } <: rest)) in
      timeless_heap_sig.sep.join_empty (snd w).timeless_heap;
      assert disjoint_mem w1 w2;
      mem_ext w (join_mem w1 w2) fun _ -> ()
    )

let timeless_later_credit n : squash (timeless (later_credit n)) =
  mem_pred_ext (later (later_credit n)) (later_credit n) fun w -> ()

let equiv p q : slprop =
  F.on_dom premem #(fun _ -> prop) fun w -> eq_at (level_ w + 1) p q

let eq_at_elim n (p q: mem_pred) (w: premem) :
    Lemma (requires eq_at n p q /\ level_ w < n) (ensures p w <==> q w) =
  assert approx n p w == approx n q w

let equiv_comm (p q: slprop) : squash (equiv p q == equiv q p) =
  mem_pred_ext (equiv p q) (equiv q p) fun _ -> ()

let equiv_elim (p q: slprop) : squash (equiv p q `star` p == equiv p q `star` q) =
  let aux (p q: slprop) (w: premem) =
    introduce (equiv p q `star` p) w ==> (equiv p q `star` q) w with _. (
      let (w1, w2) = star_elim (equiv p q) p w in
      eq_at_elim (level_ w + 1) p q w2
    ) in
  mem_pred_ext (equiv p q `star` p) (equiv p q `star` q) fun w ->
    aux p q w; aux q p w

let equiv_trans (p q r: slprop) : squash (equiv p q `star` equiv q r == equiv p q `star` equiv p r) =
  mem_pred_ext (equiv p q `star` equiv q r) (equiv p q `star` equiv p r) fun w -> ()

irreducible [@@"opaque_to_smt"]
let empty_timeless_heap (w: premem) : v:premem { disjoint_mem w v /\ w == join_mem w v /\ fst w == fst v } =
  let v = (fst w, empty_rest) in
  timeless_heap_sig.sep.join_empty (snd w).timeless_heap;
  mem_ext w (join_mem w v) (fun _ -> ());
  v

let equiv_star_congr (p q r: slprop) =
  let aux (q r: slprop) (n: nat { eq_at n q r }) (w: premem) =
    introduce level_ w < n /\ star p q w ==> star p r w with _. (
      let (w1, w2) = star_elim p q w in
      eq_at_elim n q r w2;
      star_intro p r w w1 w2
    ) in
  mem_pred_ext (equiv q r) (equiv q r `star` equiv (star p q) (star p r)) fun w ->
    introduce equiv q r w ==> (equiv q r `star` equiv (star p q) (star p r)) w with _. (
      let w2 = empty_timeless_heap w in
      mem_pred_ext (approx (level_ w + 1) (star p q)) (approx (level_ w + 1) (star p r)) (fun w' ->
        aux q r (level_ w + 1) w';
        aux r q (level_ w + 1) w'
      );
      star_intro (equiv q r) (equiv (star p q) (star p r)) w w w2
    )

let timeless_emp () : squash (timeless emp) =
  mem_pred_ext (later emp) emp fun w -> ()

let age_to_zero (w: premem { level_ w == 0 }) : Lemma (age_to_ w 0 == w) [SMTPat (age_to_ w 0)] =
  mem_ext (age_to_ w 0) w fun i -> ()

let rec timeless_interp (a: slprop { timeless a }) (w: premem) :
    Lemma (ensures a w <==> a (age_to_ w 0)) (decreases level_ w) =
  if level_ w = 0 then () else timeless_interp a (age1_ w)

let timeless_ext (a b: (p:slprop {timeless p})) (h: (w: premem { level_ w == 0 } -> squash (a w <==> b w))) :
    squash (a == b) =
  mem_pred_ext a b fun w ->
    timeless_interp a w;
    timeless_interp b w;
    h (age_to_ w 0)

let equiv_timeless (a b: slprop) :
    Lemma (requires timeless a /\ timeless b)
      (ensures timeless (equiv a b) /\ equiv a b == pure (a == b)) =
  mem_pred_ext (equiv a b) (later (equiv a b)) (fun w ->
    introduce equiv a b (age1_ w) ==> equiv a b w with _.
      mem_pred_ext (approx (level_ w + 1) a) (approx (level_ w + 1) b) fun w' ->
        assert approx (level_ w) a (age1_ w') <==> approx (level_ w) b (age1_ w'));
  timeless_pure (a == b);
  timeless_ext (equiv a b) (pure (a == b)) fun w ->
    introduce equiv a b w ==> a == b with _.
      timeless_ext a b fun w' ->
        eq_at_elim 1 a b w'

let rejuvenate1_hogs (is: hogs) (is': hogs { hogs_le is' (age1_hogs is) }) :
    is'':hogs { age1_hogs is'' == is' /\ hogs_le is'' is } =
  let is'' = mk_hogs (level_hogs is) fun a -> if None? (read_hogs is' a) then None else read_hogs is a in
  hogs_ext (age1_hogs is'') is' (fun a -> ());
  is''

let rejuvenate1_hogs_sep (is is1': hogs) (is2': hogs { disjoint_hogs is1' is2' /\ age1_hogs is == join_hogs is1' is2' }) :
    is'':(hogs&hogs) { age1_hogs is''._1 == is1' /\ age1_hogs is''._2 == is2'
      /\ disjoint_hogs is''._1 is''._2 /\ is == join_hogs is''._1 is''._2 } =
  let is1'' = rejuvenate1_hogs is is1' in
  join_hogs_commutative is1' is2';
  let is2'' = rejuvenate1_hogs is is2' in
  assert disjoint_hogs is1'' is2'';
  hogs_ext is (join_hogs is1'' is2'') (fun a ->
    assert ~(None? (read_hogs is1'' a)) ==> read_hogs is a == read_hogs is1'' a);
  (is1'', is2'')

let rejuvenate1 (w: premem) (w': premem { mem_le w' (age1_ w) }) :
    w'':premem { age1_ w'' == w' /\ mem_le w'' w /\ snd w'' == snd w' } =
  (rejuvenate1_hogs (fst w) (fst w'), snd w')

let rejuvenate1_sep (w w1': premem) (w2': premem { disjoint_mem w1' w2' /\ age1_ w == join_mem w1' w2' }) :
    w'':(premem&premem) { age1_ w''._1 == w1' /\ age1_ w''._2 == w2'
      /\ disjoint_mem w''._1 w''._2 /\ w == join_mem w''._1 w''._2 } =
  let (is1'', is2'') = rejuvenate1_hogs_sep (fst w) (fst w1') (fst w2') in
  ((is1'', snd w1'), (is2'', snd w2'))

let later_star (p q: slprop) : squash (later (star p q) == star (later p) (later q)) =
  mem_pred_ext (later (star p q)) (star (later p) (later q)) fun w ->
    introduce star p q (age1_ w) ==> star (later p) (later q) w with _. (
      let (w1', w2') = star_elim p q (age1_ w) in
      let (w1, w2) = rejuvenate1_sep w w1' w2' in
      assert later p w1;
      assert later q w2
    )

let later_exists #t (f:t->slprop) : squash (later (exists* x. f x) == (exists* x. later (f x))) =
  mem_pred_ext _ _ fun w -> ()

let iref = address

let inv_prop (i:iref) (p:slprop) (is:hogs) : prop =
  exists p'.
    read_hogs is i == Inv p' /\
    eq_at (level_hogs is) p p'

let inv (i:iref) (p:slprop) : slprop =
  F.on_dom premem #(fun _ -> prop) fun w -> inv_prop i p (fst w)

module GS = FStar.GhostSet

let inames = GS.set iref
let inames_dec_eq : GS.decide_eq address = fun x y -> reveal x = reveal y
let single (i:iref) : inames = GS.singleton inames_dec_eq i
let add_inv (e:inames) (i:iref) : inames = GS.union (single i) e

let iname_ok (i: iref) (is: hogs) =
  Inv? (read_hogs is i)

let read_inv (i: iref) (is: okay_hogs { iname_ok i is }) : slprop =
  let Inv p = read_hogs is i in p

let read_inv_equiv i (w: mem { level_ w > 0 }) (p: slprop) :
    Lemma (requires inv i p w)
      (ensures eq_at (level_ w) (read_inv i (fst w)) p) =
  ()

let inames_ok (e: inames) (is: hogs) : prop =
  forall a. GS.mem a e ==> iname_ok a is

let hogs_dom (is: hogs) : inames =
  GS.comprehend fun a -> Inv? (read_hogs is a)

let rec hogs_invariant_ (ex: inames) (is: okay_hogs) (f: address) : slprop =
  if reveal f = 0 then
    emp
  else
    let f': address = f - 1 in
    if GS.mem f' ex then
      hogs_invariant_ ex is f'
    else
      match read_hogs is f' with
      | Inv p -> later p `star` hogs_invariant_ ex is f'
      | _ -> hogs_invariant_ ex is f'

let rec hogs_invariant__congr (ex: inames) (m: okay_hogs) (f1 f2: (f:address { fresh_addr m f })) :
    Lemma (ensures hogs_invariant_ ex m f1 == hogs_invariant_ ex m f2) (decreases f1+f2+f2) =
  if f1 < f2 then
    hogs_invariant__congr ex m f2 f1
  else if f1 > f2 then
    hogs_invariant__congr ex m (f1 - 1) f2
  else
    ()

[@@"opaque_to_smt"] irreducible let some_fresh_addr (is: okay_hogs) : a:address { fresh_addr is a } =
  indefinite_description_ghost address fun a -> fresh_addr is a

let hogs_invariant (ex: inames) (is: okay_hogs) : slprop =
  hogs_invariant_ ex is (some_fresh_addr is)

let rec hogs_invariant__equiv (ex: inames) (m: okay_hogs) (i:iref { iname_ok i m /\ ~(GS.mem i ex) }) (f: address) :
    Lemma (hogs_invariant_ ex m f ==
      (if i < f then
        hogs_invariant_ (add_inv ex i) m f `star` later (read_inv i m)
      else
        hogs_invariant_ (add_inv ex i) m f)) =
  if reveal f = 0 then
    ()
  else
    let f': address = f - 1 in
    hogs_invariant__equiv ex m i f';
    if GS.mem f' ex then
      ()
    else
      match read_hogs m f' with
      | Inv p -> sep_laws ()
      | _ -> ()

let hogs_invariant_equiv (ex: inames) (m: okay_hogs) (i:iref { iname_ok i m /\ ~(GS.mem i ex) }) :
    Lemma (hogs_invariant ex m ==
      hogs_invariant (add_inv ex i) m `star` later (read_inv i m)) =
  hogs_invariant__equiv ex m i (some_fresh_addr m)

let rec hogs_invariant__age (e:inames) (is: okay_hogs { level_hogs is > 0 }) (f: address) :
    Lemma (forall w. 1 < level_ w /\ level_ w <= level_hogs is /\ hogs_invariant_ e is f w ==>
        hogs_invariant_ e (age1_hogs is) f (age1_ w)) =
  if reveal f = 0 then
    ()
  else
    let f': address = f - 1 in
    hogs_invariant__age e is f';
    if GS.mem f' e then
      ()
    else
      match read_hogs is f' with
      | Inv p ->
        let Inv p' = read_hogs (age1_hogs is) f' in
        assert eq_at (level_hogs is - 1) p p';
        introduce forall (w:premem { 1 < level_ w /\ level_ w <= level_hogs is /\ hogs_invariant_ e is f w }).
            hogs_invariant_ e (age1_hogs is) f (age1_ w) with (
          let (w1, w2) = star_elim (later p) (hogs_invariant_ e is f') w in
          assert hogs_invariant_ e (age1_hogs is) f' (age1_ w2);
          assert p (age1_ w1);
          eq_at_elim (level_hogs is - 1) p p' (age1_ (age1_ w1));
          star_intro (later (later p')) (later (hogs_invariant_ e (age1_hogs is) f')) w w1 w2;
          later_star (later p') (hogs_invariant_ e (age1_hogs is) f');
          assert (later p' `star` hogs_invariant_ e (age1_hogs is) f') (age1_ w)
        )
      | _ ->
        ()

let hogs_invariant_age (e:inames) (is: okay_hogs { level_hogs is > 0 })
    (w: premem { 1 < level_ w /\ level_ w <= level_hogs is }) :
    Lemma (hogs_invariant e is w ==> hogs_invariant e (age1_hogs is) (age1_ w)) =
  introduce hogs_invariant e is w ==> hogs_invariant e (age1_hogs is) (age1_ w) with _. (
    hogs_invariant__age e is (some_fresh_addr is);
    hogs_invariant__congr e (age1_hogs is) (some_fresh_addr is) (some_fresh_addr (age1_hogs is))
  )

let gs_disjoint_elim #t (a: GS.set t) (b: GS.set t { GS.disjoint a b }) (x: t { GS.mem x a }) :
    Lemma (~(GS.mem x b)) =
  ()

let rec hogs_invariant__disjoint (e1 e2:inames) (m1 m2:okay_hogs) (f: iref) :
    Lemma (requires
      disjoint_hogs m1 m2 /\
      GS.disjoint (hogs_dom m1) (hogs_dom m2) /\
      GS.disjoint e1 (hogs_dom m2) /\ GS.disjoint e2 (hogs_dom m1))
    (ensures 
      hogs_invariant_ (GS.union e1 e2) (join_hogs m1 m2) f ==
        hogs_invariant_ e1 m1 f `star` hogs_invariant_ e2 m2 f) =
  if reveal f = 0 then
    sep_laws ()
  else
    let f': address = f - 1 in
    hogs_invariant__disjoint e1 e2 m1 m2 f';
    if GS.mem f' (GS.union e1 e2) then
      ()
    else
      match read_hogs (join_hogs m1 m2) f' with
      | Inv p -> 
        if Inv? (read_hogs m1 f') then (
          gs_disjoint_elim (hogs_dom m1) (hogs_dom m2) f';
          sep_laws ()
        ) else if Inv? (read_hogs m2 f') then (
          gs_disjoint_elim (hogs_dom m2) (hogs_dom m1) f';
          sep_laws ()
        ) else
          assert False
      | _ -> ()

let hogs_invariant_disjoint (e1 e2:inames) (m1 m2:okay_hogs) :
    Lemma (requires
      disjoint_hogs m1 m2 /\
      GS.disjoint (hogs_dom m1) (hogs_dom m2) /\
      GS.disjoint e1 (hogs_dom m2) /\ GS.disjoint e2 (hogs_dom m1))
    (ensures 
      hogs_invariant (GS.union e1 e2) (join_hogs m1 m2) ==
        hogs_invariant e1 m1 `star` hogs_invariant e2 m2) =
  let m = join_hogs m1 m2 in
  hogs_invariant__congr e1 m1 (some_fresh_addr m1) (some_fresh_addr m);
  hogs_invariant__congr e2 m2 (some_fresh_addr m2) (some_fresh_addr m);
  hogs_invariant__disjoint e1 e2 m1 m2 (some_fresh_addr m)

let rec hogs_invariant__mono (ex1: inames) (ex2: inames)
    (m: okay_hogs { forall i. GS.mem i (hogs_dom m) /\ GS.mem i ex1 ==> GS.mem i ex2 })
    (f: address) (w: premem) :
    squash (hogs_invariant_ ex1 m f w ==> hogs_invariant_ ex2 m f w) =
  introduce _ ==> _ with _.
  if reveal f = 0 then
    ()
  else
    let f': address = f - 1 in
    if GS.mem f' ex1 then
      hogs_invariant__mono ex1 ex2 m f' w
    else
      match read_hogs m f' with
      | Inv p ->
        let (w1, w2) = star_elim (later p) (hogs_invariant_ ex1 m f') w in
        hogs_invariant__mono ex1 ex2 m f' w2;
        join_mem_commutative w1 w2;
        assert mem_le w2 w
      | _ ->
        hogs_invariant__mono ex1 ex2 m f' w

let hogs_invariant_mono (ex1: inames) (ex2: inames)
    (m: okay_hogs { forall i. GS.mem i (hogs_dom m) /\ GS.mem i ex1 ==> GS.mem i ex2 })
    (w: premem) :
    squash (hogs_invariant ex1 m w ==> hogs_invariant ex2 m w) =
  hogs_invariant__mono ex1 ex2 m (some_fresh_addr m) w

let gs_diff #t (a b: GS.set t) : GS.set t =
  GS.comprehend fun i -> GS.mem i a && not (GS.mem i b)

let hogs_invariant_disjoint' (e f:inames) (p0 p1:slprop) (m0 m1:mem) :
    Lemma (requires
      disjoint_mem m0 m1 /\
      GS.disjoint (hogs_dom (fst m0)) (hogs_dom (fst m1)) /\
      (p0 `star` hogs_invariant e (fst m0)) m0 /\
      (p1 `star` hogs_invariant f (fst m1)) m1)
    (ensures (
      let m = join_mem m0 m1 in
      (p0 `star` p1 `star` hogs_invariant (GS.union e f) (fst m)) m)) =
  let e' = gs_diff e (hogs_dom (fst m1)) in
  let _ : squash ((p0 `star` hogs_invariant e' (fst m0)) m0) =
    let (w1, w2) = star_elim p0 (hogs_invariant e (fst m0)) m0 in
    hogs_invariant_mono e e' (fst m0) w2;
    star_intro p0 (hogs_invariant e' (fst m0)) m0 w1 w2 in
  let f' = gs_diff f (hogs_dom (fst m0)) in
  let _ : squash ((p1 `star` hogs_invariant f' (fst m1)) m1) =
    let (w1, w2) = star_elim p1 (hogs_invariant f (fst m1)) m1 in
    hogs_invariant_mono f f' (fst m1) w2;
    star_intro p1 (hogs_invariant f' (fst m1)) m1 w1 w2 in
  hogs_invariant_disjoint e' f' (fst m0) (fst m1);
  let g = GS.union e' f' in
  let m: mem = join_mem m0 m1 in
  star_intro
    (p0 `star` hogs_invariant e' (fst m0)) (p1 `star` hogs_invariant f' (fst m1))
    m m0 m1;
  let _ : squash (
    (p0 `star` hogs_invariant e' (fst m0)) `star` (p1 `star` hogs_invariant f' (fst m1)) ==
    (p0 `star` p1) `star` (hogs_invariant (GS.union e' f') (fst m))
  ) = sep_laws () in
  let (w1, w2) = star_elim (p0 `star` p1) (hogs_invariant (GS.union e' f') (fst m)) m in
  hogs_invariant_mono (GS.union e' f') (GS.union e f) (fst m) w2;
  star_intro (p0 `star` p1) (hogs_invariant (GS.union e f) (fst m)) m w1 w2

let max x y = if x > y then x else y

let hogs_single n (a: iref) (p: slprop) : okay_hogs =
  let is = mk_hogs n fun b -> if reveal a = reveal b then Inv p else None in
  assert fresh_addr is (a + 1);
  is

let rec hogs_single_invariant_ n a p f : squash (hogs_invariant_ (single a) (hogs_single n a p) f == emp) =
  if reveal f = 0 then
    ()
  else
    hogs_single_invariant_ n a p (f - 1)

let hogs_single_invariant n a p : Lemma (hogs_invariant (single a) (hogs_single n a p) == emp) =
  hogs_single_invariant_ n a p (some_fresh_addr (hogs_single n a p))

let fresh_inv (p: slprop) (is: okay_hogs) (a: iref { None? (read_hogs is a) }) :
    is':okay_hogs {
      disjoint_hogs is is' /\
      inv_prop a p is' /\
      hogs_invariant (single a) is' == emp /\
      GS.disjoint (hogs_dom is) (hogs_dom is')
    } =
  let is' = hogs_single (level_hogs is) a p in
  hogs_single_invariant (level_hogs is) a p;
  is'

let dup_inv_equiv i p : Lemma (inv i p == (inv i p `star` inv i p)) =
  mem_pred_ext (inv i p) (inv i p `star` inv i p) fun w ->
    introduce inv i p w ==> star (inv i p) (inv i p) w with _.
      let w2 = empty_timeless_heap w in ()

let invariant_name_identifies_invariant (i: iref) (p q: slprop) (w: premem { level_ w > 0 }) :
    squash (star (inv i p) (inv i q) w ==> later (equiv p q) w) =
  ()

// ----------------

// inv i p  @ w_n  // eq_at n p p'

// i -> Some p' /\ eq_at (n - 1) p p'   @ (agew1 w_n)

// p' (age1 w_n) ///because w_n is an imem

// have p (age1 w_n) because level (age1 w_n) = n - 1


