module LListWithTail
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module LL = LList
module L = FStar.List.Tot.Base

noeq
type t (a: Type0) = {
  head: ref (LL.cell a);
  tail: ref (LL.cell a);
}

let null_llist (#a:Type) : Tot (t a) = {
  head = null;
  tail = null;
}

let rec llist_with_tail_fragment (#a: Type0) (x: t a) (hd: Ghost.erased (LL.cell a)) (tl: Ghost.erased (list (LL.cell a))) : Tot slprop (decreases (Ghost.reveal tl)) =
  pts_to x.head full_perm hd `star`
  begin match Ghost.reveal tl with
  | [] -> pure (x.tail == x.head)
  | a' :: q -> llist_with_tail_fragment ({ head = LL.next hd; tail = x.tail }) a' q
  end

let llist_with_tail_fragment_cons
  (#a: Type0) (x: t a) (hd: Ghost.erased (LL.cell a)) (tl: Ghost.erased (list (LL.cell a)))
: Lemma
  (requires (Cons? tl))
  (ensures (llist_with_tail_fragment x hd tl == (pts_to x.head full_perm hd `star` llist_with_tail_fragment ({ head = LL.next hd; tail = x.tail }) (L.hd tl) (L.tl tl))))
=
  ()

let llist_with_tail (#a: Type0) (x: t a) (l: Ghost.erased (list (LL.cell a))) : Tot slprop =
  match Ghost.reveal l with
  | [] -> pure (is_null x.head == true) `star` pure (is_null x.tail == true)
  | hd :: tl -> llist_with_tail_fragment x hd tl `star` pure (is_null (LL.next (L.last l)) == true)

let llist_with_tail_cons
  (#a: Type0) (x: t a) (l: Ghost.erased (list (LL.cell a)))
: Lemma
  (requires (Cons? l))
  (ensures (llist_with_tail x l == llist_with_tail_fragment x (L.hd l) (L.tl l) `star` pure (is_null (LL.next (L.last l)) == true)))
= ()

val pure_star_interp (p:slprop u#a) (q:prop) (m:mem)
   : Lemma (interp (p `star` pure q) m <==>
            interp p m /\ q)

let pure_star_interp p q m =
  pure_star_interp p q m;
  emp_unit p

val intro_llist_nil (a:Type)
   : SteelT unit emp (fun _ -> llist_with_tail (null_llist #a) [])

let intro_llist_nil a =
  change_slprop emp (llist_with_tail (null_llist #a) [])
    (fun m ->
      pure_interp (is_null (null_llist #a).head == true) m;
      pure_star_interp (pure (is_null (null_llist #a).head == true)) (is_null (null_llist #a).tail == true) m;
      norm_spec [delta; zeta] ((llist_with_tail (null_llist #a) [])))

val intro_llist_cons_nil'
  (a: Type)
  (ptr: t a)
  (x: LL.cell a)
  (m: mem)
: Lemma
  (requires (
    interp (pts_to ptr.head full_perm x `star` pure (is_null (LL.next x) == true) `star` pure (ptr.tail == ptr.head)) m
  ))
  (ensures (interp (llist_with_tail ptr [x]) m))

let intro_llist_cons_nil'
  a ptr x m
=
  pure_star_interp (pts_to ptr.head full_perm x `star` pure (is_null (LL.next x) == true)) (ptr.tail == ptr.head) m;
  pure_star_interp (pts_to ptr.head full_perm x) (is_null (LL.next x) == true) m;
  norm_spec [delta; zeta] (llist_with_tail ptr [x]);
  pure_star_interp (llist_with_tail_fragment ptr x []) (is_null (LL.next (L.last [x])) == true) m;
  norm_spec [delta; zeta] (llist_with_tail_fragment ptr x []);
  pure_star_interp (pts_to ptr.head full_perm x) (ptr.tail == ptr.head) m

let intro_llist_cons_nil
  (a: Type)
  (ptr: t a)
  (x: LL.cell a)
: SteelT unit
    (pts_to ptr.head full_perm x `star` pure (is_null (LL.next x) == true) `star` pure (ptr.tail == ptr.head))
    (fun _ -> llist_with_tail ptr [x])
=
  change_slprop
    (pts_to ptr.head full_perm x `star` pure (is_null (LL.next x) == true) `star` pure (ptr.tail == ptr.head))
    (llist_with_tail ptr [x])
    (fun m -> intro_llist_cons_nil' a ptr x m)

let pts_to_not_null_intro
  (#a:Type u#0)
  (x:ref a)
  (p:perm)
  (v: Ghost.erased a)
: SteelT unit (pts_to x p v) (fun _ -> pts_to x p v `star` pure (is_null x == false))
=
  change_slprop  (pts_to x p v) (pts_to x p v `star` pure (is_null x == false))
  (fun m ->
    pts_to_not_null x p v m;
    pure_star_interp (pts_to x p v) (is_null x == false) m
  )

val intro_llist_cons_cons'
  (a: Type)
  (ptr: t a)
  (ptr0 : t a)
  (x: LL.cell a)
  (q:  (list (LL.cell a)))
  (m: mem)
: Lemma
  (requires (interp
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x `star` pure (ptr0.head == LL.next x) `star` pure (ptr0.tail == ptr.tail) `star` pure (Cons? q == true))
    m
  ))
  (ensures (interp
    (llist_with_tail ptr (x :: q))
  ) m)
  (decreases q)

let intro_llist_cons_cons'
  a ptr ptr0 x q m
=
  (* destruct the hypothesis *)
  pure_star_interp
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x `star` pure (ptr0.head == LL.next x) `star` pure (ptr0.tail == ptr.tail))
    (Cons? q == true)
    m;
  pure_star_interp
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x `star` pure (ptr0.head == LL.next x))
    (ptr0.tail == ptr.tail)
    m;
  pure_star_interp
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x)
    (ptr0.head == LL.next x)
    m;
  star_commutative
    (llist_with_tail ptr0 q)
    (pts_to ptr.head full_perm x);
  llist_with_tail_cons ptr0 q;
  star_associative
    (pts_to ptr.head full_perm x)
    (llist_with_tail_fragment ptr0 (L.hd q) (L.tl q))
    (pure (is_null (LL.next (L.last q)) == true));
  pure_star_interp
    (pts_to ptr.head full_perm x `star` llist_with_tail_fragment ptr0 (L.hd q) (L.tl q))
    (is_null (LL.next (L.last q)) == true)
    m;
  (* construct the conclusion *)
  assert (ptr0 == ({ head = LL.next x; tail = ptr.tail }));
  assert (L.last (x :: q) == L.last q);
  llist_with_tail_fragment_cons ptr x q;
  pure_star_interp
    (llist_with_tail_fragment ptr x q)
    (is_null (LL.next (L.last (x :: q))) == true)
    m;
  llist_with_tail_cons ptr (x :: q)

let intro_llist_cons_cons
  (a: Type)
  (ptr: t a)
  (ptr0 : t a)
  (x: LL.cell a)
  (q:  (list (LL.cell a)))
: SteelT
    unit
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x `star` pure (ptr0.head == LL.next x) `star` pure (ptr0.tail == ptr.tail) `star` pure (Cons? q == true))
    (fun _ -> llist_with_tail ptr (x :: q))
=
  change_slprop
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x `star` pure (ptr0.head == LL.next x) `star` pure (ptr0.tail == ptr.tail) `star` pure (Cons? q == true))
    (llist_with_tail ptr (x :: q))
    (fun m -> intro_llist_cons_cons' a ptr ptr0 x q m)

val push_cons_cons
  (a: Type)
  (ptr: t a)
  (x: a)
  (q: (list (LL.cell a)))
: SteelT
    (t a & (list (LL.cell a)))
    (llist_with_tail ptr q `star` pure (Cons? q == true))
    (fun z -> llist_with_tail (fst z) (snd z))

#push-options "--ide_id_info_off"

let push_cons_cons
  a ptr0 e q
=
  let x = LL.mk_cell ptr0.head e in
  let px = alloc x in
  let ptr = {head = px ; tail = ptr0.tail} in
  change_slprop
    (pts_to px full_perm x)
    (pts_to ptr.head full_perm x)
    (fun _ -> ());
  intro_pure (ptr0.head == LL.next x);
  intro_pure (ptr0.tail == ptr.tail);
  intro_llist_cons_cons a ptr ptr0 x q;
  let z = (ptr, x :: q) in
  z

