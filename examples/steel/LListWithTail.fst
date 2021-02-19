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

let (==) (#a:_) (x y: a) : prop = x == y

let rec llist_with_tail_fragment (#a: Type0) (x: t a) (hd: Ghost.erased (LL.cell a)) (tl: Ghost.erased (list (LL.cell a))) : Tot slprop (decreases (Ghost.reveal tl)) =
  pts_to x.head full_perm hd `star`
  begin match Ghost.reveal tl with
  | [] -> pure (x.tail == x.head)
  | a' :: q -> llist_with_tail_fragment ({ head = LL.next hd; tail = x.tail }) a' q
  end

let llist_with_tail_fragment_aux (#a: Type0) (x: t a) (hd: Ghost.erased (LL.cell a)) (tl: Ghost.erased (list (LL.cell a))) : Tot slprop =
  match Ghost.reveal tl with
  | [] -> pure (x.tail == x.head)
  | a' :: q -> llist_with_tail_fragment ({ head = LL.next hd; tail = x.tail }) a' q

let llist_with_tail_fragment_unfold
(#a: Type0) (x: t a) (hd: Ghost.erased (LL.cell a)) (tl: Ghost.erased (list (LL.cell a))) : Lemma
  (llist_with_tail_fragment x hd tl ==
  pts_to x.head full_perm hd `star` llist_with_tail_fragment_aux x hd tl
)
= ()

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

let llist_with_tail_nil
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list (LL.cell a)))
: Lemma
  (requires (Nil? l))
  (ensures (llist_with_tail x l == pure (is_null x.head == true) `star` pure (is_null x.tail == true)))
= ()

let llist_with_tail_cons
  (#a: Type0) (x: t a) (l: Ghost.erased (list (LL.cell a)))
: Lemma
  (requires (Cons? l))
  (ensures (llist_with_tail x l == llist_with_tail_fragment x (L.hd l) (L.tl l) `star` pure (is_null (LL.next (L.last l)) == true)))
= ()

let pure_star_interp (p:slprop u#a) (q:prop) (m:mem)
   : Lemma (interp (p `star` pure q) m <==>
            interp p m /\ q)
=
  pure_star_interp p q m;
  emp_unit p

let pure_cut
  (p: slprop)
  (q: prop)
  (f: (m: mem) -> Lemma (requires (interp p m)) (ensures q))
: Steel unit
    p
    (fun _ -> p)
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> q))
=
  change_slprop p (p `star` pure q) (fun m -> f m; pure_star_interp p q m);
  let _ : squash q = elim_pure q in
  noop ()

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
    is_null (LL.next x) == true /\ ptr.tail == ptr.head /\
    interp (pts_to ptr.head full_perm x) m
  ))
  (ensures (interp (llist_with_tail ptr [x]) m))

let intro_llist_cons_nil'
  a ptr x m
=
  norm_spec [delta; zeta] (llist_with_tail ptr [x]);
  pure_star_interp (llist_with_tail_fragment ptr x []) (is_null (LL.next (L.last [x])) == true) m;
  norm_spec [delta; zeta] (llist_with_tail_fragment ptr x []);
  pure_star_interp (pts_to ptr.head full_perm x) (ptr.tail == ptr.head) m

let intro_llist_cons_nil
  (a: Type)
  (ptr: t a)
  (x: LL.cell a)
: Steel unit
    (pts_to ptr.head full_perm x)
    (fun _ -> llist_with_tail ptr [x])
    (requires (fun _ -> is_null (LL.next x) == true /\ ptr.tail == ptr.head))
    (ensures (fun _ _ _ -> True))
=
  change_slprop
    (pts_to ptr.head full_perm x)
    (llist_with_tail ptr [x])
    (fun m -> intro_llist_cons_nil' a ptr x m)

val push_nil
  (a: Type)
  (x: a)
: Steel
    (t a & Ghost.erased (list (LL.cell a)))
    (emp)
    (fun z -> llist_with_tail (fst z) (snd z))
    (requires (fun _ -> True))
    (ensures (fun _ z _ -> LL.datas (snd z) == [x]))

#push-options "--ide_id_info_off"

let push_nil
  a e
=
  let x = LL.mk_cell null e in
  let px = alloc x in
  let ptr = {head = px ; tail = px} in
  change_slprop
    (pts_to px full_perm x)
    (pts_to ptr.head full_perm x)
    (fun _ -> ());
  intro_llist_cons_nil a ptr x;
  let z = (ptr, Ghost.hide [x]) in
  change_slprop
    (llist_with_tail ptr [x])
    (llist_with_tail (fst z) (snd z))
    (fun _ -> ());
  z

let pts_to_not_null_intro
  (#a:Type u#0)
  (x:ref a)
  (p:perm)
  (v: Ghost.erased a)
: Steel unit (pts_to x p v) (fun _ -> pts_to x p v)
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> is_null x == false))
=
  pure_cut (pts_to x p v) (is_null x == false) (fun m ->
    pts_to_not_null x p v m
  )

let llist_is_nil_intro
  (a: Type)
  (ptr: t a)
  (l: Ghost.erased (list (LL.cell a)))
  (m: mem)
: Lemma
  (requires (interp (llist_with_tail ptr l) m))
  (ensures (Nil? l == is_null ptr.head))
=
  match Ghost.reveal l with
  | [] ->
    llist_with_tail_nil ptr l;
    pure_star_interp (pure (is_null ptr.head == true)) (is_null ptr.tail == true) m;
    pure_interp (is_null ptr.head == true) m
  | hd :: tl ->
    llist_with_tail_cons ptr l;
    pure_star_interp (llist_with_tail_fragment ptr (L.hd l) (L.tl l)) (is_null (LL.next (L.last l)) == true) m;
    llist_with_tail_fragment_unfold ptr hd tl;
    elim_star (pts_to ptr.head full_perm hd) (llist_with_tail_fragment_aux ptr hd tl) m;
    pts_to_not_null ptr.head full_perm hd m

val llist_is_nil
  (a: Type)
  (ptr: t a)
  (l: Ghost.erased (list (LL.cell a)))
: Steel
    bool
    (llist_with_tail ptr l)
    (fun _ -> llist_with_tail ptr l)
    (requires (fun _ -> True))
    (ensures (fun _ b _ -> Nil? l == b))

let llist_is_nil
  a ptr l
=
  let res = (is_null ptr.head) in
  pure_cut (llist_with_tail ptr l) (Nil? l == res) (fun m ->
    llist_is_nil_intro a ptr l m
  );
  res

val intro_llist_cons_cons'
  (a: Type)
  (ptr: t a)
  (ptr0 : t a)
  (x: LL.cell a)
  (q: Ghost.erased (list (LL.cell a)))
  (m: mem)
: Lemma
  (requires (interp
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x)
    m /\
    ptr0.head == LL.next x /\ ptr0.tail == ptr.tail /\ Cons? q == true
  ))
  (ensures (interp
    (llist_with_tail ptr (x :: q))
  ) m)

let intro_llist_cons_cons'
  a ptr ptr0 x q m
=
  (* destruct the hypothesis *)
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
  (q: Ghost.erased (list (LL.cell a)))
: Steel
    unit
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x)
    (fun _ -> llist_with_tail ptr (x :: q))
    (requires (fun _ -> ptr0.head == LL.next x /\ ptr0.tail == ptr.tail /\ Cons? q == true))
    (ensures (fun _ _ _ -> True))
=
  change_slprop
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x)
    (llist_with_tail ptr (x :: q))
    (fun m -> intro_llist_cons_cons' a ptr ptr0 x q m)

val push_cons
  (a: Type)
  (ptr: t a)
  (x: a)
  (q: Ghost.erased (list (LL.cell a)))
: Steel
    (t a & Ghost.erased (list (LL.cell a)))
    (llist_with_tail ptr q)
    (fun z -> llist_with_tail (fst z) (snd z))
    (requires (fun _ -> Cons? q == true))
    (ensures (fun _ z _ -> LL.datas (snd z) == x :: LL.datas q))

let push_cons
  a ptr0 e q
=
  let x = LL.mk_cell ptr0.head e in
  let px = alloc x in
  let ptr = {head = px ; tail = ptr0.tail} in
  change_slprop
    (pts_to px full_perm x)
    (pts_to ptr.head full_perm x)
    (fun _ -> ());
  intro_llist_cons_cons a ptr ptr0 x q;
  let z = (ptr, Ghost.hide (x :: q)) in
  change_slprop
    (llist_with_tail ptr (Ghost.hide (x :: q)))
    (llist_with_tail (fst z) (snd z))
    (fun _ -> ());
  z

val push
  (a: Type)
  (ptr: t a)
  (x: a)
  (q: Ghost.erased (list (LL.cell a)))
: Steel
    (t a & Ghost.erased (list (LL.cell a)))
    (llist_with_tail ptr q)
    (fun z -> llist_with_tail (fst z) (snd z))
    (requires (fun _ -> True))
    (ensures (fun _ z _ -> LL.datas (snd z) == x :: LL.datas q))

let push
  a ptr x q
=
  let is_nil = llist_is_nil a ptr q in
  if is_nil
  then begin
    drop (llist_with_tail ptr q);
    push_nil a x
  end
  else begin
    noop (); // FIXME: WHY WHY WHY? (Alternatively, let res = push_cons ... in res will also work, but still, WHY?)
    push_cons a ptr x q
  end
