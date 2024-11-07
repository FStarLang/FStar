module PulseCore.IndirectionTheorySep
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
let hogvs (x:Type u#4) : Type u#4 = address ^-> hogs_val_ x

let map_hogvs #a #b (f:a -> b) : (hogvs a ^-> hogvs b) =
  F.on_dom (hogvs a) fun x -> F.on_dom address fun a -> map_hogs_val f (x a)

noeq type premem_ (x: Type u#4) : Type u#4 = {
  hogs: hogvs x;
  saved_credits: erased nat;
  timeless_heap: timeless_heap_sig.mem;
}

let map_premem #a #b (f: a->b) : (premem_ a ^-> premem_ b) =
  F.on_dom (premem_ a) fun m -> { m with hogs = map_hogvs f m.hogs }

let f_ext #t #s (f g: t ^-> s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x;
  F.extensionality _ _ f g

let map_hogvs_id (a:Type) (x:hogvs a) : squash (map_hogvs (id #a) == id #(hogvs a)) =
  f_ext (map_hogvs (id #a)) (id #(hogvs a)) fun x ->
    f_ext (map_hogvs (id #a) x) (id x) fun _ -> ()

let map_hogvs_comp (a:Type) (b:Type) (c:Type) (b2c:b -> c) (a2b:a -> b)
: (squash (compose (map_hogvs b2c) (map_hogvs a2b) ==
            map_hogvs (compose b2c a2b)))
= let lhs = compose (map_hogvs b2c) (map_hogvs a2b) in
  let rhs = map_hogvs (compose b2c a2b) in
  f_ext lhs rhs fun x -> f_ext (lhs x) (rhs x) fun _ -> ()

let map_premem_id (a:Type) (x:premem_ a) : squash (map_premem (id #a) == id #(premem_ a)) =
  f_ext (map_premem (id #a)) (id #(premem_ a)) fun x -> map_hogvs_id a x.hogs

let map_premem_comp (a:Type) (b:Type) (c:Type) (b2c:b -> c) (a2b:a -> b)
: (squash (compose (map_premem b2c) (map_premem a2b) ==
            map_premem (compose b2c a2b)))
= let lhs = compose (map_premem b2c) (map_premem a2b) in
  let rhs = map_premem (compose b2c a2b) in
  f_ext lhs rhs fun x -> map_hogvs_comp a b c b2c a2b

let functor_heap : functor u#3 premem_ = {
  fmap = map_premem;
  fmap_id = map_premem_id;
  fmap_comp = map_premem_comp;
}

let premem: Type u#4 = knot_t functor_heap
let mem_pred : Type u#4 = IT.predicate functor_heap

let approx (n: erased nat) : (mem_pred ^-> mem_pred) = approx #_ #functor_heap n

let timeless_heap_le (a b: timeless_heap_sig.mem) : prop =
  exists c. timeless_heap_sig.sep.disjoint a c /\ b == timeless_heap_sig.sep.join a c

let hogs_val = hogs_val_ mem_pred

let read (m: premem) (a: address) : hogs_val = (unpack m).hogs a

let level_ (w: premem) : GTot nat = IT.level w

let credits_ (m: premem) : GTot nat = (unpack m).saved_credits
let timeless_heap_of (m: premem) = (unpack m).timeless_heap

// This is the essentially the same as `premem_ mem_pred` but SMT patterns utterly fail with that type.
noeq type premem' : Type u#4 = {
  hogs: address -> hogs_val;
  saved_credits: erased nat;
  timeless_heap: timeless_heap_sig.mem;
}
let premem_of' (x: premem') : premem_ mem_pred =
  { hogs = F.on _ x.hogs; saved_credits = x.saved_credits; timeless_heap = x.timeless_heap }
let premem'of_ (x: premem_ mem_pred) : premem' =
  { hogs = x.hogs; saved_credits = x.saved_credits; timeless_heap = x.timeless_heap }

let pack (n: erased nat) (x: premem') : premem = pack n (premem_of' x)
let unpack (x: premem) : premem' = premem'of_ (unpack x)

let read_pack n x a :
    Lemma (read (pack n x) a == map_hogs_val (approx n) (x.hogs a))
      [SMTPat (read (pack n x) a)] =
  let x' = premem_of' x in
  unpack_pack n x';
  assert_norm ((map_premem (approx n) x').hogs a == map_hogs_val (approx n) (x'.hogs a))
let timeless_heap_of_pack n x :
    Lemma (timeless_heap_of (pack n x) == x.timeless_heap)
      [SMTPat (timeless_heap_of (pack n x))] =
  unpack_pack n (premem_of' x)
let credits_pack n x :
    Lemma (credits_ (pack n x) == reveal x.saved_credits)
      [SMTPat (credits_ (pack n x))] =
  unpack_pack n (premem_of' x)
let level_pack n x :
    Lemma (level_ (pack n x) == reveal n)
      [SMTPat (IT.level (pack n x))] =
  unpack_pack n (premem_of' x)

let approx_def (n: erased nat) (p: mem_pred) w :
    Lemma (approx n p w == (if level_ w >= n then False else p w))
      [SMTPat (approx n p w)] =
  assert_norm (approx n p w == (if level_ w >= n then False else p w))

let mem_le (a b: premem) : prop =
  level_ a == level_ b /\
  (forall i. hogs_val_le (read a i) (read b i)) /\
  timeless_heap_le (timeless_heap_of a) (timeless_heap_of b) /\
  credits_ a <= credits_ b

let mem_pred_affine (p: mem_pred) : prop =
  forall a b. mem_le a b /\ p a ==> p b

let age_to_ (m: premem) (n: erased nat) :
    n:premem { credits_ n == credits_ m /\ timeless_heap_of n == timeless_heap_of m } =
  pack n (unpack m)

let hereditary (p: mem_pred) : prop =
  forall (w: premem) (n: erased nat).
    n < level_ w /\ p w ==>
    p (age_to_ w n)

let slprop_ok (p: mem_pred) = hereditary p /\ mem_pred_affine p

let fresh_addr (m: premem) (a: address) =
  forall (b: address). b >= a ==> None? (read m b)

let hogs_bounded (m: premem) =
  exists a. fresh_addr m a

let hogs_val_ok (v: hogs_val) =
  match v with
  | None -> True
  | Pred p -> slprop_ok p
  | Inv p -> slprop_ok p

let hogs_ok (m: premem) : prop =
  hogs_bounded m /\
  forall a. hogs_val_ok (read m a)

let mem_ok (w: premem) : prop =
  hogs_ok w

let mem = w:premem { mem_ok w }

let timeless_mem_of m = timeless_heap_of m
let level (w: mem) : GTot nat = level_ w
let credits (w: mem) : GTot nat = credits_ w

let update_timeless_mem m p =
  pack (level m) { unpack m with timeless_heap = p }

let update_credits m c =
  pack (level m) { unpack m with saved_credits = c }

let slprop = p:mem_pred { slprop_ok p }

let read_age_to_ (m: premem) (n: erased nat) a :
    Lemma (read (age_to_ m n) a == (map_hogs_val (approx n) (read m a)))
    [SMTPat (read (age_to_ m n) a)] =
  ()

let level_age_to_ m (n: erased nat) :
    Lemma (level_ (age_to_ m n) == reveal n) [SMTPat (level_ (age_to_ m n))] =
  ()

let approx_read (m: premem) a :
    Lemma (map_hogs_val (approx (level_ m)) (read m a) == read m a)
    [SMTPat (read m a)] =
  pack_unpack m;
  unpack_pack (level_ m) (premem_of' (unpack m))

let age_to (m: mem) (n: erased nat) : mem =
  age_to_ m n

let mem_ext (w1: premem) (w2: premem { level_ w1 == level_ w2 /\ credits_ w1 == credits_ w2 /\ timeless_heap_of w1 == timeless_heap_of w2 })
    (h: (a: address -> squash (read w1 a == read w2 a))) : squash (w1 == w2) =
  pack_unpack w1;
  pack_unpack w2;
  f_ext (unpack w1).hogs (unpack w2).hogs fun a -> h a

let mem_pred_ext (f g: mem_pred) (h: (w:premem -> squash (f w <==> g w))) : squash (f == g) =
  f_ext f g fun w ->
    h w;
    PropositionalExtensionality.apply (f w) (g w)

let approx_approx (m n: erased nat) (p: mem_pred) : Lemma (approx m (approx n p) == approx (min m n) p) [SMTPat (approx m (approx n p))] =
  mem_pred_ext (approx m (approx n p)) (approx (min m n) p) fun w -> ()

let age_to_age_to (w: premem) (m n: erased nat) :
    Lemma (requires n <= m) (ensures age_to_ (age_to_ w m) n == age_to_ w n)
      [SMTPat (age_to_ (age_to_ w m) n)] =
  mem_ext (age_to_ (age_to_ w m) n) (age_to_ w n) fun a -> ()

irreducible [@@"opaque_to_smt"]
let reveal_mem (m: erased premem) (h: timeless_heap_sig.mem { h == timeless_heap_of m }) : m': premem { m' == reveal m } =
  pack_unpack m;
  pack (level_ m) { timeless_heap = h; saved_credits = (unpack m).saved_credits; hogs = (unpack m).hogs }

let age1_ (w: premem) : w':premem { level_ w == 0 ==> w' == w } =
  mem_ext (age_to_ w (level_ w)) w (fun _ -> ());
  age_to_ w (if level_ w > 0 then level_ w - 1 else 0)

let age1 (w: mem) : mem = age1_ w

let eq_at (n:nat) (t0 t1:mem_pred) =
  approx n t0 == approx n t1

let eq_at_mono (p q: mem_pred) m n :
    Lemma (requires n <= m /\ eq_at m p q) (ensures eq_at n p q)
      [SMTPat (eq_at m p q); SMTPat (eq_at n p q)] =
  assert approx n p == approx n (approx m p);
  assert approx n q == approx n (approx m q)

let is_ghost_action =
  PM.ghost_action_preorder ();
  fun i1 i2 -> PM.is_ghost_action (timeless_mem_of i1) (timeless_mem_of i2)

let lift_ghost_action m p = ()

let update_ghost m1 m2 =
  reveal_mem (hide (reveal m2))
    (PM.pulse_heap_sig.update_ghost (timeless_mem_of m1) (timeless_mem_of m2))

unfold
let hogs_val_compat (x y: hogs_val) =
  match x, y with
  | None, _ | _, None -> True
  | Pred p0, Pred p1 -> p0 == p1
  | Inv p0, Inv p1 -> p0 == p1
  | Inv _, Pred _ | Pred _, Inv _ -> False

let disjoint_hogs (is0 is1:premem) =
  level_ is0 == level_ is1 /\
  (forall a. hogs_val_compat (read is0 a) (read is1 a))

let disjoint_hogs_read is0 is1 a :
    Lemma (requires disjoint_hogs is0 is1)
      (ensures hogs_val_compat (read is0 a) (read is1 a))
      [SMTPatOr [
        [SMTPat (disjoint_hogs is0 is1); SMTPat (read is0 a)];
        [SMTPat (disjoint_hogs is0 is1); SMTPat (read is1 a)];
      ]] =
  ()

let disjoint_hogs_of_le (m1 m2: premem) :
    Lemma (requires mem_le m1 m2) (ensures disjoint_hogs m1 m2) =
  ()

let empty n : mem =
  pack n {
    timeless_heap = timeless_heap_sig.sep.empty;
    saved_credits = 0;
    hogs = (fun _ -> None);
  }

let age_to_empty (m n: erased nat) : Lemma (age_to (empty n) m == empty m) [SMTPat (age_to (empty n) m)] =
  mem_ext (age_to (empty n) m) (empty m) fun a -> read_age_to_ (empty n) m a

let emp : slprop =
  F.on_dom premem #(fun _ -> prop) fun w -> True

let pure p : slprop = F.on_dom _ fun w -> p

let disjoint_mem (w0 w1:premem)
: prop 
= disjoint_hogs w0 w1 /\
  timeless_heap_sig.sep.disjoint (timeless_heap_of w0) (timeless_heap_of w1)

let join_premem (is0:premem) (is1:premem { disjoint_mem is0 is1 }) =
  pack (level_ is0) {
    saved_credits = credits_ is0 + credits_ is1;
    timeless_heap = timeless_heap_sig.sep.join (timeless_heap_of is0) (timeless_heap_of is1);
    hogs = on _ (fun a ->
      match read is0 a, read is1 a with
      | None, None -> None
      | Pred p, _ | _, Pred p -> Pred p
      | Inv p, _ | _, Inv p -> Inv p)
  }

let read_join_premem (is0:premem) (is1:premem { disjoint_mem is0 is1 }) a :
  Lemma (read (join_premem is0 is1) a ==
    (match read is0 a, read is1 a with
    | None, None -> None
    | Pred p, _ | _, Pred p -> Pred (approx (level_ is0) p)
    | Inv p, _ | _, Inv p -> Inv (approx (level_ is0) p))) =
  ()

let join_premem_commutative (is0:premem) (is1:premem { disjoint_mem is0 is1 }) :
    Lemma (disjoint_mem is1 is0 /\ join_premem is0 is1 == join_premem is1 is0) =
  timeless_heap_sig.sep.disjoint_sym (timeless_heap_of is0) (timeless_heap_of is1);
  timeless_heap_sig.sep.join_commutative (timeless_heap_of is0) (timeless_heap_of is1);
  mem_ext (join_premem is0 is1) (join_premem is1 is0) fun a -> ()

let join_premem_associative
    (is0:premem)
    (is1:premem)
    (is2:premem { 
      disjoint_mem is1 is2 /\
      disjoint_mem is0 (join_premem is1 is2)
    })
: Lemma (
    disjoint_mem is0 is1 /\
    disjoint_mem (join_premem is0 is1) is2 /\
    join_premem is0 (join_premem is1 is2) ==
    join_premem (join_premem is0 is1) is2
  )
=
  timeless_heap_sig.sep.join_associative (timeless_heap_of is0) (timeless_heap_of is1) (timeless_heap_of is2);
  assert disjoint_mem is0 is1;
  assert disjoint_mem (join_premem is0 is1) is2;
  mem_ext (join_premem is0 (join_premem is1 is2)) (join_premem (join_premem is0 is1) is2) (fun a -> ())

open FStar.IndefiniteDescription { indefinite_description_ghost, strong_excluded_middle }

let mem_le_iff (w1 w2: premem) :
    Lemma (mem_le w1 w2 <==> exists w3. join_premem w1 w3 == w2) =
  introduce mem_le w1 w2 ==> exists w3. join_premem w1 w3 == w2 with _. (
    assert timeless_heap_le (timeless_heap_of w1) (timeless_heap_of w2);
    let ph3 = indefinite_description_ghost _ fun ph3 ->
      (timeless_heap_of w2) == timeless_heap_sig.sep.join (timeless_heap_of w1) ph3 in
    let sc3: nat = credits_ w2 - credits_ w1 in
    let w3 = pack (level_ w2) {
      timeless_heap = ph3;
      saved_credits = sc3;
      hogs = (fun a -> read w2 a);
    } in
    mem_ext (join_premem w1 w3) w2 fun a -> ()
  )

let age_to_disjoint_mem (w1 w2: premem) n :
    Lemma (requires disjoint_mem w1 w2)
      (ensures disjoint_mem (age_to_ w1 n) (age_to_ w2 n)) =
  ()

let age_to_join (w1 w2: premem) n :
    Lemma (requires disjoint_mem w1 w2)
      (ensures disjoint_mem (age_to_ w1 n) (age_to_ w2 n) /\
        age_to_ (join_premem w1 w2) n == join_premem (age_to_ w1 n) (age_to_ w2 n))
    [SMTPat (age_to_ (join_premem w1 w2) n)] =
  mem_ext (age_to_ (join_premem w1 w2) n) (join_premem (age_to_ w1 n) (age_to_ w2 n)) fun a -> ()

let star_ (p1 p2: mem_pred) : mem_pred =
  F.on_dom premem #(fun _ -> prop)
    fun w -> (exists w1 w2.
      disjoint_mem w1 w2 /\ w == join_premem w1 w2 /\ p1 w1 /\ p2 w2)

[@@"opaque_to_smt"] irreducible
let indefinite_description_ghost2 (a b: Type) (p: (a -> b -> prop) { exists x y. p x y })
  : GTot (x: (a&b) { p x._1 x._2 }) =
  let x = indefinite_description_ghost a fun x -> exists y. p x y in
  let y = indefinite_description_ghost b fun y -> p x y in
  (x, y)

let star__elim (p1 p2: mem_pred) (w: premem { star_ p1 p2 w }) :
    GTot (w':(premem & premem) { disjoint_mem w'._1 w'._2 /\ w == join_premem w'._1 w'._2 /\ p1 w'._1 /\ p2 w'._2 }) =
  indefinite_description_ghost2 _ _ fun w1 w2 -> 
    disjoint_mem w1 w2 /\ w == join_premem w1 w2 /\ p1 w1 /\ p2 w2 

let star__intro (p1 p2: mem_pred) (w w1 w2: premem) :
    Lemma (requires disjoint_mem w1 w2 /\ w == join_premem w1 w2 /\ p1 w1 /\ p2 w2)
      (ensures star_ p1 p2 w) =
  ()

let star__commutative (p1 p2:mem_pred)
: Lemma (p1 `star_` p2 == p2 `star_` p1)
= FStar.Classical.forall_intro_2 join_premem_commutative;
  mem_pred_ext (p1 `star_` p2) (p2 `star_` p1) fun w -> ()

let star__assoc (x y z:mem_pred)
: Lemma (star_ x (star_ y z) == star_ (star_ x y) z)
=
  introduce forall x y z w. star_ x (star_ y z) w ==> star_ (star_ x y) z w with introduce _ ==> _ with _. (
    let (w1, w23) = star__elim x (star_ y z) w in
    let (w2, w3) = star__elim y z w23 in
    join_premem_associative w1 w2 w3;
    let w12 = join_premem w1 w2 in
    assert star_ x y w12;
    let w' = join_premem w12 w3 in
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
    let c = indefinite_description_ghost _ fun c -> b == join_premem a c in
    let (a1, a2) = star__elim p1 p2 a in
    assert b == join_premem (join_premem a1 a2) c;
    join_premem_commutative (join_premem a1 a2) c; 
    assert b == join_premem c (join_premem a1 a2);
    join_premem_associative c a1 a2; 
    assert b == join_premem (join_premem c a1) a2;
    join_premem_commutative c a1;
    assert b == join_premem (join_premem a1 c) a2;
    mem_le_iff a1 (join_premem a1 c);
    assert mem_le a1 (join_premem a1 c);
    assert p1 (join_premem a1 c)
  );
  star_ p1 p2

let star_elim (p1 p2: slprop) (w: premem { star p1 p2 w }) :
    GTot (w':(premem & premem) { disjoint_mem w'._1 w'._2 /\ w == join_premem w'._1 w'._2 /\ p1 w'._1 /\ p2 w'._2 }) =
  star__elim p1 p2 w

let star_elim' (p1 p2: slprop) (w: mem { star p1 p2 w }) :
    GTot (w':(mem & mem) { disjoint_mem w'._1 w'._2 /\ w == join_premem w'._1 w'._2 /\ p1 w'._1 /\ p2 w'._2 }) =
  let w1, w2 = star_elim p1 p2 w in
  w1, w2

let star_intro (p1 p2: slprop) (w w1 w2: premem) :
    Lemma (requires disjoint_mem w1 w2 /\ w == join_premem w1 w2 /\ p1 w1 /\ p2 w2)
      (ensures star p1 p2 w) = ()

let star_commutative (p1 p2:slprop)
: Lemma (p1 `star` p2 == p2 `star` p1)
= star__commutative p1 p2

let star_assoc (x y z:slprop)
: Lemma (star x (star y z) == star (star x y) z)
= star__assoc x y z

let disjoint_empty w : squash (disjoint_mem w (empty (level_ w)) /\ disjoint_mem (empty (level_ w)) w) =
  timeless_heap_sig.sep.join_empty (timeless_heap_of w);
  join_premem_commutative w (empty (level_ w))

let join_empty w : squash (disjoint_mem (empty (level_ w)) w /\ join_premem (empty (level_ w)) w == w) =
  disjoint_empty w;
  timeless_heap_sig.sep.join_empty (timeless_heap_of w);
  timeless_heap_sig.sep.join_commutative (timeless_heap_of w) timeless_heap_sig.sep.empty;
  mem_ext (join_premem (empty (level_ w)) w) w fun a -> ()

let star_emp (x: slprop) : squash (star x emp == x) =
  mem_pred_ext (star x emp) x fun w ->
    introduce x w ==> star x emp w with _. (
      let w2 = empty (level_ w) in
      join_empty w;
      join_premem_commutative w2 w
    );
    introduce star x emp w ==> x w with _. (
      let (w1, w2) = star_elim x emp w in
      mem_le_iff w1 w
    )

let (exists*) #a f =
  F.on_dom premem #(fun _ -> prop) fun w ->
    exists (x:a). f x w

let exists_ext p q =
  mem_pred_ext (op_exists_Star p) (op_exists_Star q) fun _ -> ()

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

let disjoint m0 m1 = disjoint_mem m0 m1
let join m0 m1 = join_premem m0 m1

let clear_except_hogs i = pack (level_ i) { unpack i with saved_credits = 0; timeless_heap = timeless_heap_sig.sep.empty }
let join_refl i =
  PM.pulse_heap_sig.sep.join_empty (timeless_heap_of i);
  mem_ext i (join i (clear_except_hogs i)) fun _ -> ()

let disjoint_join_levels i0 i1 = ()

let interp p =
  introduce forall (m0 m1:mem). p m0 /\ disjoint m0 m1 ==> p (join m0 m1) with
    introduce _ ==> _ with _.  assert mem_le m0 (join m0 m1);
  p

let update_timeless_mem_id m =
  mem_ext (update_timeless_mem m (timeless_mem_of m)) m fun _ -> ()
let join_update_timeless_mem m1 m2 p1 p2 =
  mem_ext (join_mem (update_timeless_mem m1 p1) (update_timeless_mem m2 p2))
        (update_timeless_mem (join_mem m1 m2) (PM.pulse_heap_sig.sep.join p1 p2))
    fun _ -> ()

let star_equiv p q m =
  introduce
    forall m0 m1. 
      disjoint m0 m1 /\
      m == join m0 m1 /\
      interp p m0 /\
      interp q m1
      ==> interp (p `star` q) m
    with introduce _ ==> _ with _. (
    assert disjoint_mem m0 m1;
    assert m == join_mem m0 m1
  );
  introduce
    interp (p `star` q) m ==>
    exists m0 m1. 
      disjoint m0 m1 /\
      m == join m0 m1 /\
      interp p m0 /\
      interp q m1
    with _. (
    assert star p q m;
    let (m1, m2) = star_elim p q m in
    assert disjoint m1 m2;
    assert m == join m1 m2
  )

let erase_pair #t #s (p: erased (t & s)) : erased t & erased s =
  (hide (fst p), hide (snd p))

let split_mem (p:slprop) (q:slprop) (m:erased mem { interp (p `star` q) m })
: res:(erased mem & erased mem) {
    let l, r = res in
    disjoint l r /\
    reveal m == join l r /\
    interp p l /\
    interp q r
  }
= erase_pair (star_elim' p q m)
  
let intro_star (p q:slprop) (m0 m1:mem)
: Lemma
  (requires disjoint m0 m1 /\ interp p m0 /\ interp q m1)
  (ensures interp (p `star` q) (join m0 m1))
= star_equiv p q (join m0 m1)

let emp_equiv m = ()

let interp_exists p = ()

let interp_pure p m = ()

let lift (p: PM.slprop) : slprop =
  F.on_dom premem fun w -> timeless_heap_sig.interp p (timeless_heap_of w)

let lift_eq p = ()

let lift_emp_eq () =
  mem_pred_ext (lift PM.emp) emp fun w ->
    timeless_heap_sig.intro_emp (timeless_heap_of w)

let lift_pure_eq p =
  mem_pred_ext (lift (PM.pure p)) (pure p) fun w ->
    timeless_heap_sig.pure_interp p (timeless_heap_of w)

let lift_star_eq p q =
  mem_pred_ext (lift (PM.star p q)) (star (lift p) (lift q)) fun w ->
    timeless_heap_sig.star_equiv p q (timeless_heap_of w);
    introduce
      forall (m0 m1 : timeless_mem).
          timeless_heap_sig.sep.disjoint m0 m1 /\
          (timeless_heap_of w) == timeless_heap_sig.sep.join m0 m1 /\
          timeless_heap_sig.interp p m0 /\
          timeless_heap_sig.interp q m1
        ==> star (lift p) (lift q) w with introduce _ ==> _ with _. (
      let w0 = pack (level_ w) { unpack w with timeless_heap = m0 } in
      let w1 = pack (level_ w) { unpack w with timeless_heap = m1; saved_credits = 0 } in
      assert disjoint_mem w0 w1;
      // join_refl (fst w);
      mem_ext (join_premem w0 w1) w (fun _ -> ());
      assert lift p w0;
      assert lift q w1;
      ()
    );
    introduce star (lift p) (lift q) w ==> lift (PM.star p q) w with _.
      let (w1, w2) = star_elim (lift p) (lift q) w in
      ()

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

let later_credit (n: nat) : slprop =
  F.on_dom premem #(fun _ -> prop) fun w -> credits_ w >= n

let later_credit_zero () : squash (later_credit 0 == emp) =
  mem_pred_ext (later_credit 0) emp fun _ -> ()

let later_credit_add (m n: nat) : squash (later_credit (m + n) == later_credit m `star` later_credit n) =
  mem_pred_ext (later_credit (m+n)) (later_credit m `star` later_credit n) fun w ->
    introduce later_credit (m+n) w ==> (later_credit m `star` later_credit n) w with _. (
      let w1 = pack (level_ w) { unpack w with saved_credits = credits_ w - n } in
      let w2 = pack (level_ w) { unpack w with saved_credits = n; timeless_heap = timeless_heap_sig.sep.empty } in
      timeless_heap_sig.sep.join_empty (timeless_heap_of w);
      assert disjoint_mem w1 w2;
      mem_ext w (join_premem w1 w2) fun _ -> ()
    );
    introduce (later_credit m `star` later_credit n) w ==> later_credit (m+n) w with _.
      let (w1, w2) = star_elim (later_credit m) (later_credit n) w in ()

let timeless_lift (p: PM.slprop) : squash (timeless (lift p)) =
  mem_pred_ext (later (lift p)) (lift p) fun w -> ()

let timeless_pure (p: prop) : squash (timeless (pure p)) =
  mem_pred_ext (later (pure p)) (pure p) fun w -> ()

let timeless_emp () : squash (timeless emp) =
  mem_pred_ext (later emp) emp fun w -> ()

let timeless_later_credit n : squash (timeless (later_credit n)) =
  mem_pred_ext (later (later_credit n)) (later_credit n) fun w -> ()

let rejuvenate1 (m: premem) (m': premem { mem_le m' (age1_ m) }) :
    m'':premem { age1_ m'' == m' /\ mem_le m'' m } =
  pack (level_ m) {
    saved_credits = credits_ m';
    timeless_heap = timeless_heap_of m';
    hogs = (fun a -> if None? (read m' a) then None else read m a)
  }

let rejuvenate1_sep (m m1': premem) (m2': premem { disjoint_mem m1' m2' /\ age1_ m == join_premem m1' m2' }) :
    m'':(premem&premem) { age1_ m''._1 == m1' /\ age1_ m''._2 == m2'
      /\ disjoint_mem m''._1 m''._2 /\ m == join_premem m''._1 m''._2 } =
  let m1'' = rejuvenate1 m m1' in
  join_premem_commutative m1' m2';
  let m2'' = rejuvenate1 m m2' in
  assert disjoint_mem m1'' m2'';
  mem_ext m (join_premem m1'' m2'') (fun a ->
    assert ~(None? (read m1'' a)) ==> read m a == read m1'' a);
  (m1'', m2'')

let later_star (p q: slprop) : squash (later (star p q) == star (later p) (later q)) =
  mem_pred_ext (later (star p q)) (star (later p) (later q)) fun w ->
    introduce star p q (age1_ w) ==> star (later p) (later q) w with _. (
      let (w1', w2') = star_elim p q (age1_ w) in
      let (w1, w2) = rejuvenate1_sep w w1' w2' in
      assert later p w1;
      assert later q w2
    )

let later_exists #t (f:t->slprop) : squash (later (exists* x. f x) == (exists* x. later (f x))) =
  mem_pred_ext (later (exists* x. f x)) (exists* x. later (f x)) fun w -> ()

let equiv p q : slprop =
  F.on_dom premem #(fun _ -> prop) fun w -> eq_at (level_ w + 1) p q

let eq_at_elim n (p q: mem_pred) (w: premem) :
    Lemma (requires eq_at n p q /\ level_ w < n) (ensures p w <==> q w) =
  assert approx n p w == approx n q w

let intro_equiv p m = ()

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
let empty_timeless_heap (w: premem) : v:premem { disjoint_mem w v /\ w == join_premem w v /\ (forall a. read v a == read w a) } =
  let v = pack (level_ w) {
    saved_credits = 0;
    timeless_heap = timeless_heap_sig.sep.empty;
    hogs = (fun a -> read w a);
  } in
  timeless_heap_sig.sep.join_empty (timeless_heap_of w);
  mem_ext w (join_premem w v) (fun _ -> ());
  v

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

let age_to_zero (w: premem { level_ w == 0 }) : Lemma (age_to_ w 0 == w) [SMTPat (age_to_ w 0)] =
  mem_ext (age_to_ w 0) w fun i -> ()

let intro_later p m = ()

let iref = address

let inv (i:iref) (p:slprop) : slprop =
  F.on_dom premem #(fun _ -> prop) fun m ->
    exists p'.
      read m i == Inv p' /\
      eq_at (level_ m) p p'

let deq_iref = fun x y -> reveal x = reveal y


module GS = FStar.GhostSet

let lower_inames i = GS.empty

let hogs_iname_ok (i: iref) (is: premem) =
  Inv? (read is i)

let hogs_inames_ok (e: inames) (is: premem) : prop =
  forall a. GS.mem a e ==> hogs_iname_ok a is

let inames_ok_empty m = ()
let inames_ok_union i j m =
  assert (hogs_inames_ok (GS.union i j) m <==> hogs_inames_ok i m /\ hogs_inames_ok j m)

let rec hogs_invariant_ (ex: inames) (is: mem) (f: address) : slprop =
  if reveal f = 0 then
    emp
  else
    let f': address = f - 1 in
    if GS.mem f' ex then
      hogs_invariant_ ex is f'
    else
      match read is f' with
      | Inv p -> later p `star` hogs_invariant_ ex is f'
      | _ -> hogs_invariant_ ex is f'

let rec hogs_invariant__congr (ex: inames) (m: mem) (f1 f2: (f:address { fresh_addr m f })) :
    Lemma (ensures hogs_invariant_ ex m f1 == hogs_invariant_ ex m f2) (decreases f1+f2+f2) =
  if f1 < f2 then
    hogs_invariant__congr ex m f2 f1
  else if f1 > f2 then
    hogs_invariant__congr ex m (f1 - 1) f2
  else
    ()

[@@"opaque_to_smt"] irreducible let some_fresh_addr (is: mem) : a:address { fresh_addr is a } =
  indefinite_description_ghost address fun a -> fresh_addr is a

let hogs_invariant (ex: inames) (is: mem) : slprop =
  hogs_invariant_ ex is (some_fresh_addr is)

let inames_ok_update_timeless_mem m p ex = ()
let hogs_invariant_update_timeless_mem m p ex = ()

let hogs_dom (is: premem) : inames =
  GS.comprehend fun a -> Inv? (read is a)

let age_mem m =
  let m' = age1 m in
  PM.ghost_action_preorder ();
  GS.lemma_equal_intro (hogs_dom m) (hogs_dom m'); assert hogs_dom m == hogs_dom m';
  m'

let age_level m = ()
let age_disjoint m0 m1 = ()
let age_hereditary m0 m1 = ()
let age_later m0 m1 = ()

let spend_mem m =
  PM.ghost_action_preorder ();
  pack (level m) {
    unpack m with
    saved_credits = if credits_ m > 0 then credits_ m - 1 else 0;
  }
let interp_later_credit n m = ()
let spend_lemma m = ()
let spend_disjoint m0 m1 = ()

let buy_mem n m =
  PM.ghost_action_preorder ();
  pack (level m) {
    unpack m with
    saved_credits = credits_ m + n;
  }
let buy_lemma n m = ()
let buy_disjoint n m0 m1 = ()

let iname_ok i m = hogs_iname_ok i m
let inames_ok_single i p m = ()
let iname_ok_inames_ok i m = ()

let read_inv (i: iref) (is: mem { hogs_iname_ok i is }) : slprop =
  let Inv p = read is i in p

let read_inv_equiv i m p = ()
let read_inv_disjoint i m0 m1 = ()

let rec hogs_invariant__equiv (ex: inames) (m: mem) (i:iref { hogs_iname_ok i m /\ ~(GS.mem i ex) }) (f: address) :
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
      match read m f' with
      | Inv p -> sep_laws ()
      | _ -> ()

let hogs_invariant_equiv (ex: inames) (m: mem) (i:iref { hogs_iname_ok i m /\ ~(GS.mem i ex) }) :
    Lemma (hogs_invariant ex m ==
      hogs_invariant (add_inv ex i) m `star` later (read_inv i m)) =
  hogs_invariant__equiv ex m i (some_fresh_addr m)

let mem_invariant_equiv e m i = 
  hogs_invariant_equiv e m i;
  sep_laws()

let inames_ok_hogs_dom e m = ()

let inames_ok_update e m0 m1 =
  assert forall i. GS.mem i (hogs_dom m0) <==> GS.mem i (hogs_dom m1)

let rec hogs_invariant__age (e:inames) (is: mem { level_ is > 0 }) (f: address) :
    Lemma (forall w. 1 < level_ w /\ level_ w <= level_ is /\ hogs_invariant_ e is f w ==>
        hogs_invariant_ e (age1_ is) f (age1_ w)) =
  if reveal f = 0 then
    ()
  else
    let f': address = f - 1 in
    hogs_invariant__age e is f';
    if GS.mem f' e then
      ()
    else
      match read is f' with
      | Inv p ->
        let Inv p' = read (age1_ is) f' in
        assert eq_at (level_ is - 1) p p';
        introduce forall (w:premem { 1 < level_ w /\ level_ w <= level_ is /\ hogs_invariant_ e is f w }).
            hogs_invariant_ e (age1_ is) f (age1_ w) with (
          let (w1, w2) = star_elim (later p) (hogs_invariant_ e is f') w in
          assert hogs_invariant_ e (age1_ is) f' (age1_ w2);
          assert p (age1_ w1);
          eq_at_elim (level_ is - 1) p p' (age1_ (age1_ w1));
          star_intro (later (later p')) (later (hogs_invariant_ e (age1_ is) f')) w w1 w2;
          later_star (later p') (hogs_invariant_ e (age1_ is) f');
          assert (later p' `star` hogs_invariant_ e (age1_ is) f') (age1_ w)
        )
      | _ ->
        ()

let hogs_invariant_age (e:inames) (is: mem { level_ is > 0 })
    (w: premem { 1 < level_ w /\ level_ w <= level_ is }) :
    Lemma (hogs_invariant e is w ==> hogs_invariant e (age1_ is) (age1_ w)) =
  introduce hogs_invariant e is w ==> hogs_invariant e (age1_ is) (age1_ w) with _. (
    hogs_invariant__age e is (some_fresh_addr is);
    hogs_invariant__congr e (age1_ is) (some_fresh_addr is) (some_fresh_addr (age1_ is))
  )

let gs_disjoint_elim #t (a: GS.set t) (b: GS.set t { GS.disjoint a b }) (x: t { GS.mem x a }) :
    Lemma (~(GS.mem x b)) =
  ()

let rec hogs_invariant__disjoint (e1 e2:inames) (m1 m2:mem) (f: iref) :
    Lemma (requires
      disjoint m1 m2 /\
      GS.disjoint (hogs_dom m1) (hogs_dom m2) /\
      GS.disjoint e1 (hogs_dom m2) /\ GS.disjoint e2 (hogs_dom m1))
    (ensures 
      hogs_invariant_ (GS.union e1 e2) (join m1 m2) f ==
        hogs_invariant_ e1 m1 f `star` hogs_invariant_ e2 m2 f) =
  if reveal f = 0 then
    sep_laws ()
  else
    let f': address = f - 1 in
    hogs_invariant__disjoint e1 e2 m1 m2 f';
    if GS.mem f' (GS.union e1 e2) then
      ()
    else
      match read (join m1 m2) f' with
      | Inv p -> 
        if Inv? (read m1 f') then (
          gs_disjoint_elim (hogs_dom m1) (hogs_dom m2) f';
          sep_laws ()
        ) else if Inv? (read m2 f') then (
          gs_disjoint_elim (hogs_dom m2) (hogs_dom m1) f';
          sep_laws ()
        ) else
          assert False
      | _ -> ()

let hogs_invariant_disjoint (e1 e2:inames) (m1 m2:mem) :
    Lemma (requires
      disjoint m1 m2 /\
      GS.disjoint (hogs_dom m1) (hogs_dom m2) /\
      GS.disjoint e1 (hogs_dom m2) /\ GS.disjoint e2 (hogs_dom m1))
    (ensures 
      hogs_invariant (GS.union e1 e2) (join m1 m2) ==
        hogs_invariant e1 m1 `star` hogs_invariant e2 m2) =
  let m = join m1 m2 in
  hogs_invariant__congr e1 m1 (some_fresh_addr m1) (some_fresh_addr m);
  hogs_invariant__congr e2 m2 (some_fresh_addr m2) (some_fresh_addr m);
  hogs_invariant__disjoint e1 e2 m1 m2 (some_fresh_addr m)

let rec hogs_invariant__mono (ex1: inames) (ex2: inames)
    (m: mem { forall i. GS.mem i (hogs_dom m) /\ GS.mem i ex1 ==> GS.mem i ex2 })
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
      match read m f' with
      | Inv p ->
        let (w1, w2) = star_elim (later p) (hogs_invariant_ ex1 m f') w in
        hogs_invariant__mono ex1 ex2 m f' w2;
        join_premem_commutative w1 w2;
        assert mem_le w2 w
      | _ ->
        hogs_invariant__mono ex1 ex2 m f' w

let hogs_invariant_mono (ex1: inames) (ex2: inames)
    (m: mem { forall i. GS.mem i (hogs_dom m) /\ GS.mem i ex1 ==> GS.mem i ex2 })
    (w: premem) :
    squash (hogs_invariant ex1 m w ==> hogs_invariant ex2 m w) =
  hogs_invariant__mono ex1 ex2 m (some_fresh_addr m) w

let gs_diff #t (a b: GS.set t) : GS.set t =
  GS.comprehend fun i -> GS.mem i a && not (GS.mem i b)

let hogs_invariant_disjoint' (e f:inames) (p0 p1:slprop) (m0 m1:mem) :
    Lemma (requires
      disjoint_mem m0 m1 /\
      GS.disjoint (hogs_dom m0) (hogs_dom m1) /\
      (p0 `star` hogs_invariant e m0) m0 /\
      (p1 `star` hogs_invariant f m1) m1)
    (ensures (
      let m = join_premem m0 m1 in
      (p0 `star` p1 `star` hogs_invariant (GS.union e f) m) m)) =
  let e' = gs_diff e (hogs_dom m1) in
  let _ : squash ((p0 `star` hogs_invariant e' m0) m0) =
    let (w1, w2) = star_elim p0 (hogs_invariant e m0) m0 in
    hogs_invariant_mono e e' m0 w2;
    star_intro p0 (hogs_invariant e' m0) m0 w1 w2 in
  let f' = gs_diff f (hogs_dom m0) in
  let _ : squash ((p1 `star` hogs_invariant f' m1) m1) =
    let (w1, w2) = star_elim p1 (hogs_invariant f m1) m1 in
    hogs_invariant_mono f f' m1 w2;
    star_intro p1 (hogs_invariant f' m1) m1 w1 w2 in
  hogs_invariant_disjoint e' f' m0 m1;
  let g = GS.union e' f' in
  let m: mem = join_premem m0 m1 in
  star_intro
    (p0 `star` hogs_invariant e' m0) (p1 `star` hogs_invariant f' m1)
    m m0 m1;
  let _ : squash (
    (p0 `star` hogs_invariant e' m0) `star` (p1 `star` hogs_invariant f' m1) ==
    (p0 `star` p1) `star` (hogs_invariant (GS.union e' f') m)
  ) = sep_laws () in
  let (w1, w2) = star_elim (p0 `star` p1) (hogs_invariant (GS.union e' f') m) m in
  hogs_invariant_mono (GS.union e' f') (GS.union e f) m w2;
  star_intro (p0 `star` p1) (hogs_invariant (GS.union e f) m) m w1 w2

let inames_ok_disjoint i j mi mj = ()

let pm_mem_invariant_empty ()
: Lemma (lift (PM.mem_invariant GhostSet.empty PM.pulse_heap_sig.sep.empty) == emp)
= PM.pulse_heap_sig.empty_mem_invariant GhostSet.empty;
  lift_emp_eq ()


let mem_invariant_disjoint (e f:inames) (p0 p1:slprop) (m0 m1:mem) =
  sep_laws ();
  let p0' = (p0 `star` lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m0))) in
  let p1' = (p1 `star` lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m1))) in
  hogs_invariant_disjoint' e f p0' p1' m0 m1;
  let m = join_mem m0 m1 in
  let cm = m in
  Classical.forall_intro (PM.pulse_heap_sig.sep.join_empty);
  pm_mem_invariant_empty()

let mem_invariant_age e m0 m1 = 
  introduce interp (mem_invariant e m0) m1 ==>
            interp (mem_invariant e (age_mem m0)) (age1 m1)
  with _ . (
    let m10, m11 =
      split_mem (lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m0)))
                (hogs_invariant e m0) m1
    in
    hogs_invariant_age e m0 (m11);
    age_hereditary (lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m0))) m10;
    assert (interp (hogs_invariant e (age_mem m0)) (age1 m11));
    age_disjoint m10 m11;
    intro_star (lift (PM.mem_invariant GhostSet.empty (timeless_mem_of m0)))
                (hogs_invariant e (age_mem m0)) 
                (age1 m10)
                (age1 m11)
  )

let mem_invariant_spend e m = ()

let mem_invariant_buy e n m = ()

let hogs_single n (a: iref) (p: slprop) : mem =
  pack n {
    saved_credits = 0;
    timeless_heap = timeless_heap_sig.sep.empty;
    hogs = (fun b -> if reveal a = reveal b then Inv p else None)
  }

let rec hogs_single_invariant_ n a p f : squash (hogs_invariant_ (single a) (hogs_single n a p) f == emp) =
  if reveal f = 0 then
    ()
  else
    hogs_single_invariant_ n a p (f - 1)

let hogs_single_invariant n a p : Lemma (hogs_invariant (single a) (hogs_single n a p) == emp) =
  hogs_single_invariant_ n a p (some_fresh_addr (hogs_single n a p))

let hogs_fresh_inv (p: slprop) (is: mem) (a: iref { None? (read is a) }) :
    is':mem {
      disjoint_hogs is is' /\
      inv a p is' /\
      hogs_invariant (single a) is' == emp /\
      GS.disjoint (hogs_dom is) (hogs_dom is')
    } =
  let is' = hogs_single (level_ is) a p in
  hogs_single_invariant (level_ is) a p;
  is'

let max x y = if x > y then x else y
let rec mk_fresh (i: iref) (ctx: list iref) :
    Tot (j:iref { j >= i /\ fresh_wrt ctx j }) (decreases ctx) =
  match ctx with
  | [] -> i
  | c::cs -> mk_fresh (max i (c+1)) cs

let fresh_inv p m ctx =
  let f = IndefiniteDescription.indefinite_description_ghost iref fun f ->
    fresh_addr m f in
  let i: iref = mk_fresh f ctx in
  let m': mem = hogs_fresh_inv p m i in
  let _: squash (inv i p `star` mem_invariant (single i) m' == inv i p) =
    pm_mem_invariant_empty();
    hogs_single_invariant (level m) i p;
    sep_laws () in
  Classical.forall_intro (PM.pulse_heap_sig.sep.join_empty);
  PM.ghost_action_preorder ();
  (| i, m' |)

let dup_inv_equiv i p =
  mem_pred_ext (inv i p) (inv i p `star` inv i p) fun w ->
    introduce inv i p w ==> star (inv i p) (inv i p) w with _.
      (let w2 = empty_timeless_heap w in ());
    introduce star (inv i p) (inv i p) w ==> inv i p w with _.
      let (w1, w2) = star_elim (inv i p) (inv i p) w in ()

let invariant_name_identifies_invariant i p q w = ()

let slprop_ref = erased <| admit()
let slprop_ref_pts_to = admit()
let fresh_slprop_ref = admit()
let slprop_ref_pts_to_share = admit()
let slprop_ref_pts_to_gather = admit()