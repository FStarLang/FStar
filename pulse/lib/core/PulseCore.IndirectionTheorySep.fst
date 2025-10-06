(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module PulseCore.IndirectionTheorySep
open PulseCore.KnotInstantiation
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module PM = PulseCore.MemoryAlt
module H2 = PulseCore.Heap2
open FStar.Ghost {erased, hide, reveal}

let timeless_heap_le (a b: B.mem) : prop =
  exists c. B.disjoint_mem a c /\ b == B.join_mem a c

let hogs_val = hogs_val_ mem_pred

let approx_approx (m n: erased nat) (p: mem_pred) : Lemma (approx m (approx n p) == approx (min m n) p) [SMTPat (approx m (approx n p))] =
  mem_pred_ext (approx m (approx n p)) (approx (min m n) p) fun w -> ()

let mem_le' (a b: premem) : prop =
  level_ a == level_ b /\
  (forall i. hogs_val_le (read a i) (read b i)) /\
  timeless_heap_le (timeless_heap_of a) (timeless_heap_of b) /\
  credits_ a <= credits_ b

[@@"opaque_to_smt"] let mem_le = mem_le'
let reveal_mem_le () : squash (mem_le == mem_le') = reveal_opaque (`%mem_le) mem_le

let mem_pred_affine (p: premem -> prop) : prop =
  forall a b. mem_le a b /\ p a ==> p b

let max x y = if x > y then x else y

let age_to_age_to (w: premem) (m n: erased nat) :
    Lemma (requires n <= m) (ensures age_to_ (age_to_ w m) n == age_to_ w n)
      [SMTPat (age_to_ (age_to_ w m) n)] =
  mem_ext (age_to_ (age_to_ w m) n) (age_to_ w n) fun a -> ()

let age1_ (w: premem) : w':premem { level_ w == 0 ==> w' == w } =
  mem_ext (age_to_ w (level_ w)) w (fun _ -> ());
  age_to_ w (max 0 (level_ w - 1))

let hereditary (p: premem -> prop) : prop =
  forall h. p h ==> p (age1_ h)

let slprop_ok' (p: premem -> prop) : prop = hereditary p /\ mem_pred_affine p
[@@"opaque_to_smt"] let slprop_ok : mem_pred -> prop = slprop_ok'
let reveal_slprop_ok () : squash (forall (p: mem_pred).  slprop_ok p == slprop_ok' p) =
  reveal_opaque (`%slprop_ok) slprop_ok

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

let unpack (x: premem) : premem2 = {
  saved_credits = credits_ x;
  timeless_heap = timeless_heap_of x;
  hogs = read x;
}

let update_timeless_mem m p =
  pack (level m) { unpack m with timeless_heap = p }

let update_credits m c =
  pack (level m) { unpack m with saved_credits = c }

let slprop = p:mem_pred { slprop_ok p }
let mk_slprop (p: premem -> prop { slprop_ok' p }) : slprop =
  reveal_slprop_ok (); F.on_dom _ p

let age_to (m: mem) (n: erased nat) : mem =
  reveal_mem_le (); reveal_slprop_ok ();
  age_to_ m n

irreducible [@@"opaque_to_smt"]
let reveal_mem (m: erased premem) (h: B.mem { h == timeless_heap_of m }) : m': premem { m' == reveal m } =
  let m' = pack (level_ m) {
    timeless_heap = h;
    saved_credits = (unpack m).saved_credits;
    hogs = (unpack m).hogs
  } in
  mem_ext m m' (fun _ -> ());
  m'

let age1 (w: mem) : mem =
  reveal_mem_le (); reveal_slprop_ok ();
  age1_ w

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
    (B.update_ghost (timeless_mem_of m1) (timeless_mem_of m2))

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
  reveal_mem_le ()

let empty n : mem =
  pack n {
    timeless_heap = B.empty_mem;
    saved_credits = 0;
    hogs = (fun _ -> None);
  }

let age_to_empty (m n: erased nat) : Lemma (age_to (empty n) m == empty m) [SMTPat (age_to (empty n) m)] =
  mem_ext (age_to (empty n) m) (empty m) fun a -> read_age_to_ (empty n) m a

let emp : slprop =
  mk_slprop fun w -> True

let pure p : slprop =
  mk_slprop fun w -> p

let disjoint_mem (w0 w1:premem)
: prop 
= disjoint_hogs w0 w1 /\
  B.disjoint_mem (timeless_heap_of w0) (timeless_heap_of w1)

let join_premem (is0:premem) (is1:premem { disjoint_mem is0 is1 }) =
  pack (level_ is0) {
    saved_credits = credits_ is0 + credits_ is1;
    timeless_heap = B.join_mem (timeless_heap_of is0) (timeless_heap_of is1);
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
  H2.disjoint_sym (timeless_heap_of is0) (timeless_heap_of is1);
  H2.join_commutative (timeless_heap_of is0) (timeless_heap_of is1);
  mem_ext (join_premem is0 is1) (join_premem is1 is0) fun a -> ()

#push-options "--split_queries always"
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
  H2.join_associative (timeless_heap_of is0) (timeless_heap_of is1) (timeless_heap_of is2);
  assert disjoint_mem is0 is1;
  assert disjoint_mem (join_premem is0 is1) is2;
  mem_ext (join_premem is0 (join_premem is1 is2)) (join_premem (join_premem is0 is1) is2) (fun a -> ())
#pop-options

open FStar.IndefiniteDescription { indefinite_description_ghost, strong_excluded_middle }

#push-options "--z3rlimit 10"
let mem_le_iff (w1 w2: premem) :
    Lemma (mem_le w1 w2 <==> exists w3. join_premem w1 w3 == w2) =
  reveal_mem_le ();
  introduce mem_le w1 w2 ==> exists w3. join_premem w1 w3 == w2 with _. (
    assert timeless_heap_le (timeless_heap_of w1) (timeless_heap_of w2);
    let ph3 = indefinite_description_ghost _ fun ph3 ->
      (timeless_heap_of w2) == B.join_mem (timeless_heap_of w1) ph3 in
    let sc3: nat = credits_ w2 - credits_ w1 in
    let w3 = pack (level_ w2) {
      timeless_heap = ph3;
      saved_credits = sc3;
      hogs = (fun a -> read w2 a);
    } in
    mem_ext (join_premem w1 w3) w2 fun a -> ()
  )
#pop-options

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

[@@"opaque_to_smt"]
let star_ (p1 p2: mem_pred) : mem_pred =
  F.on_dom premem #(fun _ -> prop)
    fun w -> (exists w1 w2.
      disjoint_mem w1 w2 /\ w == join_premem w1 w2 /\ p1 w1 /\ p2 w2)

irreducible
let indefinite_description_ghost2 (a b: Type) (p: (a -> b -> prop) { exists x y. p x y })
  : GTot (x: (a&b) { p x._1 x._2 }) =
  let x = indefinite_description_ghost a fun x -> exists y. p x y in
  let y = indefinite_description_ghost b fun y -> p x y in
  (x, y)

let star__elim (p1 p2: mem_pred) (w: premem { star_ p1 p2 w }) :
    GTot (w':(premem & premem) { disjoint_mem w'._1 w'._2 /\ w == join_premem w'._1 w'._2 /\ p1 w'._1 /\ p2 w'._2 }) =
  reveal_opaque (`%star_) (star_ p1 p2);
  indefinite_description_ghost2 _ _ fun w1 w2 -> 
    disjoint_mem w1 w2 /\ w == join_premem w1 w2 /\ p1 w1 /\ p2 w2 

let star__intro (p1 p2: mem_pred) (w w1 w2: premem) :
    Lemma (requires disjoint_mem w1 w2 /\ w == join_premem w1 w2 /\ p1 w1 /\ p2 w2)
      (ensures star_ p1 p2 w) =
  reveal_opaque (`%star_) (star_ p1 p2)

let star__commutative (p1 p2:mem_pred)
: Lemma (p1 `star_` p2 == p2 `star_` p1)
= mem_pred_ext (p1 `star_` p2) (p2 `star_` p1) fun w ->
    introduce star_ p1 p2 w ==> star_ p2 p1 w with _. (
      let (w1, w2) = star__elim p1 p2 w in
      join_premem_commutative w1 w2;
      star__intro p2 p1 w w2 w1
    );
    introduce star_ p2 p1 w ==> star_ p1 p2 w with _. (
      let (w2, w1) = star__elim p2 p1 w in
      join_premem_commutative w2 w1;
      star__intro p1 p2 w w1 w2
    )

let star__assoc (x y z:mem_pred)
: Lemma (star_ x (star_ y z) == star_ (star_ x y) z)
=
  introduce forall x y z w. star_ x (star_ y z) w ==> star_ (star_ x y) z w with introduce _ ==> _ with _. (
    let (w1, w23) = star__elim x (star_ y z) w in
    let (w2, w3) = star__elim y z w23 in
    join_premem_associative w1 w2 w3;
    let w12 = join_premem w1 w2 in
    star__intro x y w12 w1 w2;
    let w' = join_premem w12 w3 in
    star__intro (star_ x y) z w' w12 w3;
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
  reveal_slprop_ok ();
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
    assert p1 (join_premem a1 c);
    star__intro p1 p2 b (join_premem a1 c) a2
  );
  introduce forall a. star_ p1 p2 a ==> star_ p1 p2 (age1_ a) with introduce _ ==> _ with _. (
    let (a1, a2) = star__elim p1 p2 a in
    star__intro p1 p2 (age1_ a) (age1_ a1) (age1_ a2)
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
      (ensures star p1 p2 w) =
  star__intro p1 p2 w w1 w2

let star_commutative (p1 p2:slprop)
: Lemma (p1 `star` p2 == p2 `star` p1)
= star__commutative p1 p2

let star_assoc (x y z:slprop)
: Lemma (star x (star y z) == star (star x y) z)
= star__assoc x y z

let disjoint_empty w : squash (disjoint_mem w (empty (level_ w)) /\ disjoint_mem (empty (level_ w)) w) =
  H2.join_empty (timeless_heap_of w);
  join_premem_commutative w (empty (level_ w))

let join_empty w : squash (disjoint_mem (empty (level_ w)) w /\ join_premem (empty (level_ w)) w == w) =
  disjoint_empty w;
  H2.join_empty (timeless_heap_of w);
  H2.join_commutative (timeless_heap_of w) B.empty_mem;
  mem_ext (join_premem (empty (level_ w)) w) w fun a -> ()

let star_emp (x: slprop) : squash (star x emp == x) =
  mem_pred_ext (star x emp) x fun w ->
    introduce x w ==> star x emp w with _. (
      let w2 = empty (level_ w) in
      join_empty w;
      join_premem_commutative w2 w;
      star__intro x emp w w w2
    );
    introduce star x emp w ==> x w with _. (
      let (w1, w2) = star_elim x emp w in
      reveal_slprop_ok ();
      mem_le_iff w1 w
    )

let (exists*) #a f =
  reveal_slprop_ok ();
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

irreducible
let clear_except_hogs_ (w: premem) : v:premem { disjoint_mem w v /\ w == join_premem w v /\ (forall a. read v a == read w a) } =
  let v = pack (level_ w) {
    saved_credits = 0;
    timeless_heap = B.empty_mem;
    hogs = (fun a -> read w a);
  } in
  H2.join_empty (timeless_heap_of w);
  mem_ext w (join_premem w v) (fun _ -> ());
  v

let clear_except_hogs m = clear_except_hogs_ m
let join_refl m = ()

let disjoint_join_levels i0 i1 = ()

let interp p =
  introduce forall (m0 m1:mem). p m0 /\ disjoint m0 m1 ==> p (join m0 m1) with (
    reveal_slprop_ok ();
    introduce _ ==> _ with _.  mem_le_iff m0 (join m0 m1)
  );
  p

let update_timeless_mem_id m =
  mem_ext (update_timeless_mem m (timeless_mem_of m)) m fun _ -> ()
let join_update_timeless_mem m1 m2 p1 p2 =
  mem_ext (join_mem (update_timeless_mem m1 p1) (update_timeless_mem m2 p2))
        (update_timeless_mem (join_mem m1 m2) (B.join_mem p1 p2))
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
    star_intro p q m m0 m1
  );
  introduce
    interp (p `star` q) m ==>
    exists m0 m1. 
      disjoint m0 m1 /\
      m == join m0 m1 /\
      interp p m0 /\
      interp q m1
    with _. (
    let (m1, m2) = star_elim p q m in
    introduce exists m0 m1. 
      disjoint m0 m1 /\
      m == join m0 m1 /\
      interp p m0 /\
      interp q m1
    with m1 m2 and ()
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
  reveal_mem_le ();
  mk_slprop fun w -> B.interp p (timeless_heap_of w)

let lift_eq p = ()

let lift_emp_eq () =
  mem_pred_ext (lift PM.emp) emp fun w ->
    B.intro_emp (timeless_heap_of w)

let lift_pure_eq p =
  mem_pred_ext (lift (PM.pure p)) (pure p) fun w ->
    B.pure_interp p (timeless_heap_of w)

let lift_star_eq p q =
  mem_pred_ext (lift (PM.star p q)) (star (lift p) (lift q)) fun w ->
    B.star_equiv p q (timeless_heap_of w);
    introduce
      forall (m0 m1 : timeless_mem).
          B.disjoint_mem m0 m1 /\
          (timeless_heap_of w) == B.join_mem m0 m1 /\
          B.interp p m0 /\
          B.interp q m1
        ==> star (lift p) (lift q) w with introduce _ ==> _ with _. (
      let w0 = pack (level_ w) { unpack w with timeless_heap = m0 } in
      let w1 = pack (level_ w) { unpack w with timeless_heap = m1; saved_credits = 0 } in
      assert disjoint_mem w0 w1;
      mem_ext (join_premem w0 w1) w (fun _ -> ());
      assert lift p w0;
      assert lift q w1;
      star_intro (lift p) (lift q) w w0 w1
    );
    introduce star (lift p) (lift q) w ==> lift (PM.star p q) w with _.
      let (w1, w2) = star_elim (lift p) (lift q) w in
      ()

let later_pred (p: slprop) (w: premem) : prop =
  level_ w > 0 ==> p (age1_ w)
let later (p: slprop) : slprop =
  reveal_slprop_ok ();
  introduce forall a b. mem_le a b /\ later_pred p a ==> later_pred p b with (
    mem_le_iff a b;
    mem_le_iff (age1_ a) (age1_ b)
  );
  mk_slprop (later_pred p)

let later_credit (n: nat) : slprop =
  reveal_mem_le ();
  mk_slprop fun w -> credits_ w >= n

let later_credit_zero () : squash (later_credit 0 == emp) =
  mem_pred_ext (later_credit 0) emp fun _ -> ()

let later_credit_add (m n: nat) : squash (later_credit (m + n) == later_credit m `star` later_credit n) =
  mem_pred_ext (later_credit (m+n)) (later_credit m `star` later_credit n) fun w ->
    introduce later_credit (m+n) w ==> (later_credit m `star` later_credit n) w with _. (
      let w1 = pack (level_ w) { unpack w with saved_credits = credits_ w - n } in
      let w2 = pack (level_ w) { unpack w with saved_credits = n; timeless_heap = B.empty_mem } in
      H2.join_empty (timeless_heap_of w);
      mem_ext w (join_premem w1 w2) (fun _ -> ());
      star_intro (later_credit m) (later_credit n) w w1 w2
    );
    introduce (later_credit m `star` later_credit n) w ==> later_credit (m+n) w with _.
      let (w1, w2) = star_elim (later_credit m) (later_credit n) w in ()

let implies (p q: slprop) : prop =
  forall (m: premem). level_ m > 0 ==> (p m ==> q m)

let elim_implies p q m = ()

let timeless_intro (p: slprop) (h: (m:premem { level_ m > 0 /\ later p m } -> squash (p m))) : squash (timeless p) =
  introduce forall (m: premem). level_ m > 0 /\ later p m ==> p m with
  introduce level_ m > 0 /\ later p m ==> p m with _. h m

let timeless_intro' (#p: slprop { forall (m:premem). level_ m > 0 ==> (later p m ==> p m) }) : squash (timeless p) =
  timeless_intro p fun m -> ()

let timeless_lift (p: PM.slprop) : squash (timeless (lift p)) = timeless_intro'
let timeless_pure (p: prop) : squash (timeless (pure p)) = timeless_intro'
let timeless_emp () : squash (timeless emp) = timeless_intro'
let timeless_later_credit n : squash (timeless (later_credit n)) = timeless_intro'

irreducible
let rejuvenate1 (m: premem) (m': premem { mem_le m' (age1_ m) }) :
    m'':premem { age1_ m'' == m' /\ mem_le m'' m } =
  reveal_mem_le ();
  let m'' = pack (level_ m) {
    saved_credits = credits_ m';
    timeless_heap = timeless_heap_of m';
    hogs = (fun a -> if None? (read m' a) then None else read m a)
  } in
  mem_ext (age1_ m'') m' (fun _ -> ());
  m''

#push-options "--z3rlimit 100 --query_stats"
#restart-solver
irreducible
let rejuvenate1_sep (m m1': premem) (m2': premem { disjoint_mem m1' m2' /\ age1_ m == join_premem m1' m2' }) :
    m'':(premem&premem) { age1_ m''._1 == m1' /\ age1_ m''._2 == m2'
      /\ disjoint_mem m''._1 m''._2 /\ m == join_premem m''._1 m''._2 } =
  reveal_mem_le ();
  let m1'' = rejuvenate1 m m1' in
  join_premem_commutative m1' m2';
  let m2'' = rejuvenate1 m m2' in
  assert disjoint_mem m1'' m2'';
  mem_ext m (join_premem m1'' m2'') (fun a -> ());
  (m1'', m2'')
#pop-options

let later_star (p q: slprop) : squash (later (star p q) == star (later p) (later q)) =
  mem_pred_ext (later (star p q)) (star (later p) (later q)) fun w ->
    if level_ w > 0 then (
      introduce star p q (age1_ w) ==> star (later p) (later q) w with _. (
        let (w1', w2') = star_elim p q (age1_ w) in
        let (w1, w2) = rejuvenate1_sep w w1' w2' in
        star_intro (later p) (later q) w w1 w2
      );
      introduce star (later p) (later q) w ==> star p q (age1_ w) with _. (
        let (w1, w2) = star_elim (later p) (later q) w in
        star_intro p q (age1_ w) (age1_ w1) (age1_ w2)
      )
    ) else (
      assert later (star p q) w;
      join_empty w;
      star_intro (later p) (later q) w (empty (level_ w)) w
    )

let timeless_star p q =
  later_star p q;
  timeless_intro (star p q) fun m ->
    introduce star (later p) (later q) m ==> star p q m with _. (
      let (m1, m2) = star__elim (later p) (later q) m in
      star__intro p q m m1 m2
    )

let later_exists #t (f:t->slprop) : squash (later (exists* x. f x) `implies` exists* x. later (f x)) = ()

let timeless_exists (#t: Type) (f: t->slprop) :
    Lemma (requires forall x. timeless (f x)) (ensures timeless (exists* x. f x)) =
  timeless_intro (exists* x. f x) fun m ->
    assert (exists x. (f x) m) <==> (exists x. later (f x) m)

let equiv p q : slprop =
  reveal_mem_le ();
  mk_slprop fun w -> eq_at (level_ w + 1) p q

let eq_at_elim n (p q: mem_pred) (w: premem) :
    Lemma (requires eq_at n p q /\ level_ w < n) (ensures p w <==> q w) =
  assert approx n p w == approx n q w

let eq_at_intro (n: nat) (p q: mem_pred)
    (h: (m: premem { level_ m < n } -> squash (p m <==> q m))) :
    Lemma (eq_at n p q) =
  mem_pred_ext (approx n p) (approx n q) fun m ->
    if level_ m < n then h m else ()

let intro_equiv p m = ()

let equiv_comm (p q: slprop) : squash (equiv p q == equiv q p) =
  mem_pred_ext (equiv p q) (equiv q p) fun _ -> ()

let interp_equiv_star (p q r: slprop) m :
    Lemma (star (equiv p q) r m <==> equiv p q m /\ r m)
      [SMTPat (star (equiv p q) r m)] =
  introduce star (equiv p q) r m ==> equiv p q m /\ r m with _. (
    let (m1, m2) = star_elim (equiv p q) r m in
    join_premem_commutative m1 m2;
    reveal_slprop_ok ();
    mem_le_iff m2 m
  );
  introduce equiv p q m /\ r m ==> star (equiv p q) r m with _. (
    join_empty m;
    star_intro (equiv p q) r m (empty (level_ m)) m
  )

let equiv_elim (p q: slprop) : squash (equiv p q `star` p == equiv p q `star` q) =
  mem_pred_ext (equiv p q `star` p) (equiv p q `star` q) fun m ->
    introduce equiv p q m ==> (p m <==> q m) with _.
      eq_at_elim (level_ m + 1) p q m

let equiv_trans (p q r: slprop) : squash (equiv p q `star` equiv q r == equiv p q `star` equiv p r) =
  mem_pred_ext (equiv p q `star` equiv q r) (equiv p q `star` equiv p r) fun w -> ()

let later_equiv (p q: slprop) =
  mem_pred_ext (later (equiv p q)) (equiv (later p) (later q)) fun m ->
    introduce later (equiv p q) m ==> equiv (later p) (later q) m with _. (
      mem_pred_ext (approx (level_ m + 1) (later p)) (approx (level_ m + 1) (later q)) fun m' ->
        if level_ m' >= level_ m + 1 then () else
          if level_ m = 0 then
            ()
          else
            eq_at_elim (level_ m) p q (age1_ m')
    );
    introduce equiv (later p) (later q) m ==> later (equiv p q) m with _. (
      if level_ m = 0 then
        ()
      else
        mem_pred_ext (approx (level_ m) p) (approx (level_ m) q) fun m' ->
          if level_ m' >= level_ m then () else (
            let m'': premem = age_to_ m' (level_ m' + 1) in
            mem_ext (age1_ m'') m' (fun a -> ());
            eq_at_elim (level_ m + 1) (later p) (later q) m''
          )
    )

let rec timeless_interp (a: slprop { timeless a }) (w: premem) :
    Lemma (ensures a w <==> a (age_to_ w 0)) (decreases level_ w) =
  if level_ w = 0 then (mem_ext w (age_to_ w 0) fun a -> ()) else (
    timeless_interp a (age1_ w);
    reveal_slprop_ok ()
  )

let timeless_ext (a b: (p:slprop {timeless p})) (h: (w: premem { level_ w == 0 } -> squash (a w <==> b w))) :
    squash (a == b) =
  mem_pred_ext a b fun w ->
    timeless_interp a w;
    timeless_interp b w;
    h (age_to_ w 0)

let equiv_timeless (a b: slprop) :
    Lemma (requires timeless a /\ timeless b)
      (ensures timeless (equiv a b) /\ equiv a b == pure (a == b)) =
  later_equiv a b;
  timeless_pure (a == b);
  timeless_intro (equiv a b) (fun m ->
    introduce later (equiv a b) m ==> equiv a b m with _.
      eq_at_intro (level_ m + 1) a b fun m' ->
        reveal_slprop_ok ();
        eq_at_elim (level_ m) a b (age1_ m'));
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
  mem_pred_ext (equiv q r) (equiv q r `star` equiv (star p q) (star p r)) fun m ->
    introduce equiv q r m ==> equiv (star p q) (star p r) m with _.
      mem_pred_ext (approx (level_ m + 1) (star p q)) (approx (level_ m + 1) (star p r)) (fun m' ->
        aux q r (level_ m + 1) m';
        aux r q (level_ m + 1) m'
      )

let age_to_zero (w: premem { level_ w == 0 }) : Lemma (age_to_ w 0 == w) [SMTPat (age_to_ w 0)] =
  mem_ext (age_to_ w 0) w fun i -> ()

let intro_later p m = reveal_slprop_ok ()

let elim_later_timeless p m = ()

let iref = address

let inv (i:iref) (p:slprop) : slprop =
  reveal_mem_le ();
  mk_slprop fun m ->
    exists p'.
      read m i == Inv p' /\
      eq_at (level_ m) p p'

module GS = Pulse.Lib.GhostSet

let deq_iref = GS.decide_eq_f

let lower_inames i = GS.empty

let hogs_iname_ok (i: iref) (is: premem) =
  Inv? (read is i)

let hogs_inames_ok_internal (e: inames) (is: premem) : prop =
  forall a. GS.mem a e ==> hogs_iname_ok a is
let hogs_inames_ok (e: inames) (is: mem) : prop =
  hogs_inames_ok_internal e is

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

irreducible let some_fresh_addr (is: mem) : a:address { fresh_addr is a } =
  indefinite_description_ghost address fun a -> fresh_addr is a

let hogs_invariant (ex: inames) (is: mem) : slprop =
  hogs_invariant_ ex is (some_fresh_addr is)

let inames_ok_update_timeless_mem m p ex = ()

let rec hogs_invariant__congr2 (ex: inames) (m1 m2: mem) (f:address) :
    Lemma (requires forall a. read m1 a == read m2 a)
      (ensures hogs_invariant_ ex m1 f == hogs_invariant_ ex m2 f) =
  if reveal f = 0 then
    ()
  else
    let f': address = f - 1 in
    hogs_invariant__congr2 ex m1 m2 f'
let hogs_invariant_congr2 (ex: inames) (m1 m2: mem) :
    Lemma (requires forall a. read m1 a == read m2 a)
      (ensures hogs_invariant ex m1 == hogs_invariant ex m2) =
  hogs_invariant__congr ex m2 (some_fresh_addr m2) (some_fresh_addr m1);
  hogs_invariant__congr2 ex m1 m2 (some_fresh_addr m1)

let hogs_invariant_update_timeless_mem m p ex =
  hogs_invariant_congr2 ex m (update_timeless_mem m p)

let hogs_dom (is: premem) : inames =
  GS.comprehend fun a -> Inv? (read is a)

let age_mem m =
  let m' = age1 m in
  PM.ghost_action_preorder ();
  GS.lemma_equal_intro (hogs_dom m) (hogs_dom m'); assert hogs_dom m == hogs_dom m';
  m'

let age_level m = ()
let age_disjoint m0 m1 = ()
let age_hereditary m0 m1 = reveal_slprop_ok ()
let age_later m0 m1 = ()

let spend_mem m =
  PM.ghost_action_preorder ();
  let m' = pack (level m) {
    hogs = (fun a -> read m a);
    timeless_heap = timeless_heap_of m;
    saved_credits = if credits_ m > 0 then credits_ m - 1 else 0;
  } in
  GS.lemma_equal_intro (hogs_dom m) (hogs_dom m');
  m'
let interp_later_credit n m = ()
let spend_lemma m = ()
let spend_disjoint m0 m1 =
  mem_ext (spend (join m0 m1)) (join (spend m0) m1) fun _ -> ()

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

#push-options "--split_queries always"
let rec hogs_invariant__age (e:inames) (is: mem { level_ is > 0 }) (f: address) :
    Lemma (forall w. 1 < level_ w /\ level_ w <= level_ is /\ hogs_invariant_ e is f w ==>
        hogs_invariant_ e (age1 is) f (age1_ w)) =
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
            hogs_invariant_ e (age1 is) f (age1_ w) with (
          let (w1, w2) = star_elim (later p) (hogs_invariant_ e is f') w in
          assert hogs_invariant_ e (age1 is) f' (age1_ w2);
          assert p (age1_ w1);
          eq_at_elim (level_ is - 1) p p' (age1_ (age1_ w1));
          reveal_slprop_ok ();
          star_intro (later (later p')) (later (hogs_invariant_ e (age1 is) f')) w w1 w2;
          later_star (later p') (hogs_invariant_ e (age1 is) f');
          assert (later p' `star` hogs_invariant_ e (age1 is) f') (age1_ w)
        )
      | _ ->
        ()
#pop-options

let hogs_invariant_age (e:inames) (is: mem { level_ is > 0 })
    (w: premem { 1 < level_ w /\ level_ w <= level_ is }) :
    Lemma (hogs_invariant e is w ==> hogs_invariant e (age1 is) (age1_ w)) =
  introduce hogs_invariant e is w ==> hogs_invariant e (age1 is) (age1_ w) with _. (
    hogs_invariant__age e is (some_fresh_addr is);
    hogs_invariant__congr e (age1 is) (some_fresh_addr is) (some_fresh_addr (age1 is))
  )

let gs_disjoint_elim #t (a: GS.set t) (b: GS.set t { GS.disjoint a b }) (x: t { GS.mem x a }) :
    Lemma (~(GS.mem x b)) =
  ()

#push-options "--split_queries always"
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
#pop-options

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

#push-options "--split_queries always"
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
        mem_le_iff w2 w;
        reveal_slprop_ok ();
        star_intro (later p) (hogs_invariant_ ex2 m f') w w1 w2
      | _ ->
        hogs_invariant__mono ex1 ex2 m f' w
#pop-options

let hogs_invariant_mono (ex1: inames) (ex2: inames)
    (m: mem { forall i. GS.mem i (hogs_dom m) /\ GS.mem i ex1 ==> GS.mem i ex2 })
    (w: premem) :
    squash (hogs_invariant ex1 m w ==> hogs_invariant ex2 m w) =
  hogs_invariant__mono ex1 ex2 m (some_fresh_addr m) w

let gs_diff #t (a b: GS.set t) : GS.set t =
  GS.comprehend fun i -> GS.mem i a && not (GS.mem i b)

#push-options "--split_queries always"
let hogs_invariant_disjoint' (e f:inames) (p0 p1:slprop) (m0 m1:mem) :
    Lemma (requires
      disjoint_mem m0 m1 /\
      GS.disjoint (hogs_dom m0) (hogs_dom m1) /\
      (p0 `star` hogs_invariant e m0) m0 /\
      (p1 `star` hogs_invariant f m1) m1)
    (ensures (
      let m = join_premem m0 m1 in
      mem_ok m /\
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
#pop-options

let inames_ok_disjoint i j mi mj = ()

let mem_invariant_disjoint (e f:inames) (p0 p1:slprop) (m0 m1:mem) =
  hogs_invariant_disjoint' e f p0 p1 m0 m1

let mem_invariant_age e m0 m1 = 
  introduce interp (mem_invariant e m0) m1 ==>
            interp (mem_invariant e (age_mem m0)) (age1 m1)
  with _ . hogs_invariant_age e m0 m1
  

let mem_invariant_spend e m =
  hogs_invariant_congr2 e m (spend m)

let hogs_single n (a: iref) (p: slprop) : mem =
  let m = pack n {
    saved_credits = 0;
    timeless_heap = B.empty_mem;
    hogs = (fun b -> if reveal a = reveal b then Inv p else None)
  } in
  assert fresh_addr m (a+1);
  reveal_mem_le (); reveal_slprop_ok ();
  m

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

let buy1_mem m =
  PM.ghost_action_preorder ();
  join_empty m;
  let m' = update_credits (empty (level m)) 1 in
  introduce forall (e: inames). mem_invariant e m == mem_invariant e (join_mem m' m) with
    hogs_invariant_congr2 e m (join_mem m' m);
  m'

let inames_live (e:inames) : slprop =
  reveal_mem_le ();
  mk_slprop fun m ->
    hogs_inames_ok_internal e m

let inames_live_empty () : squash (inames_live GS.empty == emp) =
  mem_pred_ext (inames_live GS.empty) emp fun w -> ()

let inames_live_union (e1 e2:inames) 
: Lemma (inames_live (GS.union e1 e2) == inames_live e1 `star` inames_live e2)
= mem_pred_ext (inames_live (GS.union e1 e2)) (inames_live e1 `star` inames_live e2) fun w ->
    introduce inames_live (GS.union e1 e2) w ==> star (inames_live e1) (inames_live e2) w with _.
      star_intro (inames_live e1) (inames_live e2) w w (clear_except_hogs_ w);
    introduce star (inames_live e1) (inames_live e2) w ==> inames_live (GS.union e1 e2) w with _.
      let (w1, w2) = star_elim (inames_live e1) (inames_live e2) w in (
        assert inames_live e1 w;
        assert inames_live e2 w
      )

let inames_live_inv (i:iref) (p:slprop) (m:mem)
: Lemma ((inv i p) m ==> inames_live (FStar.GhostSet.singleton deq_iref i) m)
= ()

let rec max_inames (xs: list iref) : y:iref { forall x. List.memP x xs ==> reveal x <= y } =
  match xs with
  | [] -> 0
  | x::xs -> max x (max_inames xs)

let fresh_inv_name (m:mem) (ctx:inames { GS.is_finite ctx }) : i:iref { None? (read m i) /\ not (GS.mem i ctx) } =
  let i = IndefiniteDescription.indefinite_description_ghost iref fun f ->
    fresh_addr m f in
  let ctx = GS.is_finite_elim ctx in
  max i (max_inames ctx + 1)

let fresh_inv p m ctx =
  let i = fresh_inv_name m ctx in
  let m': mem = hogs_fresh_inv p m i in
  let _: squash (inv i p `star` mem_invariant (single i) m' == inv i p) =
    hogs_single_invariant (level m) i p;
    sep_laws () in
  Classical.forall_intro (H2.join_empty u#3);
  PM.ghost_action_preorder u#3 ();
  (| i, m' |)

let dup_inv_equiv i p =
  mem_pred_ext (inv i p) (inv i p `star` inv i p) fun w ->
    introduce inv i p w ==> star (inv i p) (inv i p) w with _.
      star_intro (inv i p) (inv i p) w w (clear_except_hogs_ w);
    introduce star (inv i p) (inv i p) w ==> inv i p w with _.
      let (w1, w2) = star_elim (inv i p) (inv i p) w in ()

let implies_intro (p q: slprop) (h: (m:premem { level_ m > 0 /\ p m } -> squash (q m))) : squash (implies p q) =
  introduce forall m. level_ m > 0 /\ p m ==> q m with introduce _ ==> _ with _. h m

let invariant_name_identifies_invariant i p q =
  implies_intro _ _ fun m ->
    let (w1, w2) = star_elim (inv i p) (inv i q) m in
    assert later (equiv p q) m

let slprop_ref = address

let null_slprop_ref = 0

let slprop_ref_pts_to x y =
  reveal_mem_le ();
  mk_slprop fun m ->
    exists y'.
      read m x == Pred y' /\
      eq_at (level_ m) y y'

let single_slprop_pts_to n (i: slprop_ref) (p: slprop) : mem =
  let m = pack n {
    timeless_heap = B.empty_mem;
    saved_credits = 0;
    hogs = (fun a -> if reveal a = reveal i then Pred p else None);
  } in
  assert fresh_addr m (i+1);
  reveal_mem_le (); reveal_slprop_ok ();
  m

let rec hogs_invariant__single_slprop_pts_to ex (n: nat) i p f :
    squash (hogs_invariant_ ex (single_slprop_pts_to n i p) f == emp) =
  if reveal f = 0 then
    ()
  else
    let f': nat = f - 1 in
    sep_laws ();
    hogs_invariant__single_slprop_pts_to ex n i p f'
let hogs_invariant_single_slprop_pts_to ex (n: nat) i p :
    squash (hogs_invariant ex (single_slprop_pts_to n i p) == emp) =
  hogs_invariant__single_slprop_pts_to ex n i p (some_fresh_addr (single_slprop_pts_to n i p))

let fresh_slprop_ref p m =
  let i = indefinite_description_ghost slprop_ref fun i -> fresh_addr m i in
  let m' = single_slprop_pts_to (level_ m) i p in
  assert slprop_ref_pts_to i p m';
  let _: squash (slprop_ref_pts_to i p `star` mem_invariant GS.empty m' == slprop_ref_pts_to i p) =
    hogs_invariant_single_slprop_pts_to GS.empty (level_ m) i p;
    star_emp emp;
    star_emp (slprop_ref_pts_to i p) in
  Classical.forall_intro (H2.join_empty u#3);
  GS.lemma_equal_intro (hogs_dom m') GS.empty;
  PM.ghost_action_preorder u#3 ();
  (| i, m' |)

let slprop_ref_pts_to_share x y =
  mem_pred_ext (slprop_ref_pts_to x y) (slprop_ref_pts_to x y `star` slprop_ref_pts_to x y) fun m ->
    introduce slprop_ref_pts_to x y m ==> (slprop_ref_pts_to x y `star` slprop_ref_pts_to x y) m with _.
      star_intro (slprop_ref_pts_to x y) (slprop_ref_pts_to x y) m m (clear_except_hogs_ m);
    introduce (slprop_ref_pts_to x y `star` slprop_ref_pts_to x y) m ==> slprop_ref_pts_to x y m with _.
      let (m1, m2) = star_elim (slprop_ref_pts_to x y) (slprop_ref_pts_to x y) m in ()

let slprop_ref_pts_to_gather x y1 y2 =
  implies_intro
      (slprop_ref_pts_to x y1 `star` slprop_ref_pts_to x y2) 
      (slprop_ref_pts_to x y1 `star` later (equiv y1 y2)) fun m ->
    let (m1, m2) = star_elim (slprop_ref_pts_to x y1) (slprop_ref_pts_to x y2) m in
    star_intro (slprop_ref_pts_to x y1) (later (equiv y1 y2)) m m1 m2

let implies' (p q: slprop) : prop =
  forall (m: premem). p m ==> q m

let loeb (p: slprop { implies' (later p) p }) : squash (implies' emp p) =
  let rec aux (m: premem) : Lemma (ensures p m) (decreases level_ m) =
    if level_ m > 0 then aux (age1_ m) else () in
  introduce forall m. p m with aux m