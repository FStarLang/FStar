module CQueue
open CQueue.LList

(* BEGIN library *)

let intro_vrewrite_no_norm (#opened:inames)
  (v: vprop) (#t: Type) (f: (t_of v) -> GTot t)
: SteelGhost unit opened v (fun _ -> vrewrite v f)
                (fun _ -> True) (fun h _ h' -> h' (vrewrite v f) == f (h v))
=
  intro_vrewrite v f

let elim_vrewrite_no_norm (#opened:inames)
  (v: vprop)
  (#t: Type)
  (f: ((t_of v) -> GTot t))
: SteelGhost unit opened (vrewrite v f) (fun _ -> v)
    (fun _ -> True)
    (fun h _ h' -> h (vrewrite v f) == f (h' v))
=
  elim_vrewrite v f

let vconst_sel
  (#a: Type)
  (x: a)
: Tot (selector a (hp_of emp))
= fun _ -> x

[@@ __steel_reduce__]
let vconst'
  (#a: Type)
  (x: a)
: GTot vprop'
= {
  hp = hp_of emp;
  t = a;
  sel = vconst_sel x;
}

[@@ __steel_reduce__]
let vconst (#a: Type) (x: a) : Tot vprop = VUnit (vconst' x)

let intro_vconst
  (#opened: _)
  (#a: Type)
  (x: a)
: SteelGhost unit opened
    emp
    (fun _ -> vconst x)
    (fun _ -> True)
    (fun _ _ h' -> h' (vconst x) == x)
=
  change_slprop_rel
    emp
    (vconst x)
    (fun _ y -> y == x)
    (fun _ -> ())

let elim_vconst
  (#opened: _)
  (#a: Type)
  (x: a)
: SteelGhost unit opened
    (vconst x)
    (fun _ -> emp)
    (fun _ -> True)
    (fun h _ _ -> h (vconst x) == x)
=
  change_slprop_rel
    (vconst x)
    emp
    (fun y _ -> y == x)
    (fun _ -> ())

let vpure_sel'
  (p: prop)
: Tot (selector' (squash p) (Steel.Memory.pure p))
= fun (m: hmem (Steel.Memory.pure p)) -> pure_interp p m

let vpure_sel
  (p: prop)
: Tot (selector (squash p) (Steel.Memory.pure p))
= vpure_sel' p

[@@ __steel_reduce__]
let vpure'
  (p: prop)
: GTot vprop'
= {
  hp = Steel.Memory.pure p;
  t = squash p;
  sel = vpure_sel p;
}

[@@ __steel_reduce__]
let vpure (p: prop) : Tot vprop = VUnit (vpure' p)

let intro_vpure
  (#opened: _)
  (p: prop)
: SteelGhost unit opened
    emp
    (fun _ -> vpure p)
    (fun _ -> p)
    (fun _ _ h' -> p)
=
  change_slprop_rel
    emp
    (vpure p)
    (fun _ _ -> p)
    (fun m -> pure_interp p m)

let elim_vpure
  (#opened: _)
  (p: prop)
: SteelGhost unit opened
    (vpure p)
    (fun _ -> emp)
    (fun _ -> True)
    (fun _ _ _ -> p)
=
  change_slprop_rel
    (vpure p)
    emp
    (fun _ _ -> p)
    (fun m -> pure_interp p m; reveal_emp (); intro_emp m)

val intro_vdep2 (#opened:inames)
  (v: vprop)
  (q: vprop)
  (x: t_of v)
  (p: (t_of v -> Tot vprop))
: SteelGhost unit opened
    (v `star` q)
    (fun _ -> vdep v p)
    (requires (fun h ->
      q == p x /\
      x == h v
    ))
    (ensures (fun h _ h' ->
      let x2 = h' (vdep v p) in
      q == p (h v) /\
      dfst x2 == (h v) /\
      dsnd x2 == (h q)
    ))

let intro_vdep2
  v q x p
=
  intro_vdep v q p

let vbind0_payload
  (a: vprop)
  (t: Type0)
  (b: (t_of a -> Tot vprop))
  (x: t_of a)
: Tot vprop
= vpure (t == t_of (b x)) `star` b x

let vbind0_rewrite
  (a: vprop)
  (t: Type0)
  (b: (t_of a -> Tot vprop))
  (x: normal (t_of (vdep a (vbind0_payload a t b))))
: Tot t
= snd (dsnd x)

[@@__steel_reduce__; __reduce__]
let vbind0
  (a: vprop)
  (t: Type0)
  (b: (t_of a -> Tot vprop))
: Tot vprop
= a `vdep` vbind0_payload a t b `vrewrite` vbind0_rewrite a t b

let vbind_hp // necessary to hide the attribute on hp_of
  (a: vprop)
  (t: Type0)
  (b: (t_of a -> Tot vprop))
: Tot (slprop u#1)
= hp_of (vbind0 a t b)

let vbind_sel // same for hp_sel
  (a: vprop)
  (t: Type0)
  (b: (t_of a -> Tot vprop))
: GTot (selector t (vbind_hp a t b))
= sel_of (vbind0 a t b)

[@@__steel_reduce__]
let vbind'
  (a: vprop)
  (t: Type0)
  (b: (t_of a -> Tot vprop))
: GTot vprop'
= {
  hp = vbind_hp a t b;
  t = t;
  sel = vbind_sel a t b;
}

[@@__steel_reduce__]
let vbind
  (a: vprop)
  (t: Type0)
  (b: (t_of a -> Tot vprop))
: Tot vprop
= VUnit (vbind' a t b)

let intro_vbind
  (#opened: _)
  (a: vprop)
  (b' : vprop)
  (t: Type0)
  (b: (t_of a -> Tot vprop))
: SteelGhost unit opened
    (a `star` b')
    (fun _ -> vbind a t b)
    (fun h -> t_of b' == t /\ b' == b (h a))
    (fun h _ h' ->
      t_of b' == t /\
      b' == b (h a) /\
      h' (vbind a t b) == h b'
    )
=
  intro_vpure (t == t_of b');
  reveal_star (vpure (t == t_of b')) b';
  intro_vdep
    a
    (vpure (t == t_of b') `star` b')
    (vbind0_payload a t b);
  intro_vrewrite
    (a `vdep` vbind0_payload a t b)
    (vbind0_rewrite a t b);
  change_slprop_rel
    (vbind0 a t b)
    (vbind a t b)
    (fun x y -> x == y)
    (fun _ -> ())

let elim_vbind
  (#opened: _)
  (a: vprop)
  (t: Type0)
  (b: (t_of a -> Tot vprop))
: SteelGhost (Ghost.erased (t_of a)) opened
    (vbind a t b)
    (fun res -> a `star` b (Ghost.reveal res))
    (fun h -> True)
    (fun h res h' ->
      h' a == Ghost.reveal res /\
      t == t_of (b (Ghost.reveal res)) /\
      h' (b (Ghost.reveal res)) == h (vbind a t b)
    )
=
  change_slprop_rel
    (vbind a t b)
    (vbind0 a t b)
    (fun x y -> x == y)
    (fun _ -> ());
  elim_vrewrite
    (a `vdep` vbind0_payload a t b)
    (vbind0_rewrite a t b);
  let res = elim_vdep a (vbind0_payload a t b) in
  change_equal_slprop
    (vbind0_payload a t b (Ghost.reveal res))
    (vpure (t == t_of (b (Ghost.reveal res))) `star` b (Ghost.reveal res));
  reveal_star (vpure (t == t_of (b (Ghost.reveal res)))) (b (Ghost.reveal res));
  elim_vpure (t == t_of (b (Ghost.reveal res)));
  res

let (==) (#a:_) (x y: a) : prop = x == y

let snoc_inj (#a: Type) (hd1 hd2: list a) (tl1 tl2: a) : Lemma
  (requires (hd1 `L.append` [tl1] == hd2 `L.append` [tl2]))
  (ensures (hd1 == hd2 /\ tl1 == tl2))
  [SMTPat (hd1 `L.append` [tl1]); SMTPat (hd2 `L.append` [tl2])]
= L.lemma_snoc_unsnoc (hd1, tl1);
  L.lemma_snoc_unsnoc (hd2, tl2)

[@"opaque_to_smt"]
let unsnoc (#a: Type) (l: list a) : Pure (list a & a)
  (requires (Cons? l))
  (ensures (fun (hd, tl) -> l == hd `L.append` [tl] /\ L.length hd < L.length l))
=
  L.lemma_unsnoc_snoc l;
  L.append_length (fst (L.unsnoc l)) [snd (L.unsnoc l)];
  L.unsnoc l

let unsnoc_hd (#a: Type) (l: list a) : Pure (list a) (requires (Cons? l)) (ensures (fun l' -> L.length l' < 
L.length l)) = fst (unsnoc l)
let unsnoc_tl (#a: Type) (l: list a) : Pure (a) (requires (Cons? l)) (ensures (fun _ -> True)) = snd (unsnoc l)

[@@"opaque_to_smt"]
let snoc (#a: Type) (l: list a) (x: a) : Pure (list a)
  (requires True)
  (ensures (fun l' ->
    Cons? l' /\
    unsnoc_hd l' == l /\
    unsnoc_tl l' == x
  ))
=
  let l' = L.snoc (l, x) in
  L.append_length l [x];
  snoc_inj l (unsnoc_hd l') x (unsnoc_tl l');
  l'

let snoc_unsnoc
  (#a: Type)
  (l: list a)
: Lemma
  (requires (Cons? l))
  (ensures (snoc (unsnoc_hd l) (unsnoc_tl l) == l))
= ()

unfold
let coerce
  (#a: Type)
  (x: a)
  (b: Type)
: Pure b
  (requires (a == b))
  (ensures (fun y -> a == b /\ x == y))
= x

(* END library *)

let t a = cllist_lvalue a

let v (a: Type0) = list a

let datas
  (#a: Type0)
  (l: v a)
: Tot (list a)
= l

(* view from the tail *)

let llist_fragment_tail_cons_data_refine
  (#a: Type)
  (l: Ghost.erased (list a) { Cons? (Ghost.reveal l) })
  (d: a)
: Tot prop
= d == unsnoc_tl (Ghost.reveal l)

[@@ __steel_reduce__]
let llist_fragment_tail_cons_lvalue_payload
  (#a: Type)
  (l: Ghost.erased (list a) { Cons? (Ghost.reveal l) })
  (c: ccell_lvalue a)
: Tot vprop
= vptr (ccell_data c) `vrefine` llist_fragment_tail_cons_data_refine l

let ccell_is_lvalue_refine
  (a: Type)
  (c: ccell_ptrvalue a)
: Tot prop
= ccell_ptrvalue_is_null c == false

[@@ __steel_reduce__ ]
let llist_fragment_tail_cons_next_payload
  (#a: Type)
  (l: Ghost.erased (list a) { Cons? (Ghost.reveal l) })
  (ptail: ref (ccell_ptrvalue a))
: Tot vprop
= vptr ptail `vrefine` ccell_is_lvalue_refine a `vdep` llist_fragment_tail_cons_lvalue_payload l

[@@ __steel_reduce__ ]
let llist_fragment_tail_cons_rewrite
  (#a: Type)
  (l: Ghost.erased (list a) { Cons? (Ghost.reveal l) })
  (llist_fragment_tail: vprop { t_of llist_fragment_tail == ref (ccell_ptrvalue a) })
  (x: normal (t_of (llist_fragment_tail `vdep` (llist_fragment_tail_cons_next_payload l))))
: Tot (ref (ccell_ptrvalue a))
= let (| _, (| c, _ |) |) = x in
  ccell_next c

let rec llist_fragment_tail (#a: Type) (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a)) : Pure vprop
  (requires True)
  (ensures (fun v -> t_of v == ref (ccell_ptrvalue a)))
  (decreases (Ghost.reveal (L.length l)))
= if Nil? l
  then vconst phead
  else llist_fragment_tail (Ghost.hide (unsnoc_hd (Ghost.reveal l))) phead `vdep` llist_fragment_tail_cons_next_payload l `vrewrite` llist_fragment_tail_cons_rewrite l (llist_fragment_tail (Ghost.hide (unsnoc_hd (Ghost.reveal l))) phead)

let llist_fragment_tail_eq
  (#a: Type) (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a))
: Lemma
  (llist_fragment_tail l phead == (
    if Nil? l
    then vconst phead
    else llist_fragment_tail (Ghost.hide (unsnoc_hd (Ghost.reveal l))) phead `vdep` llist_fragment_tail_cons_next_payload l `vrewrite` llist_fragment_tail_cons_rewrite l (llist_fragment_tail (Ghost.hide (unsnoc_hd (Ghost.reveal l))) phead)
  ))
= assert_norm
  (llist_fragment_tail l phead == (
    if Nil? l
    then vconst phead
    else llist_fragment_tail (Ghost.hide (unsnoc_hd (Ghost.reveal l))) phead `vdep` llist_fragment_tail_cons_next_payload l `vrewrite` llist_fragment_tail_cons_rewrite l (llist_fragment_tail (Ghost.hide (unsnoc_hd (Ghost.reveal l))) phead)
  ))

let llist_fragment_tail_eq_cons
  (#a: Type) (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a))
: Lemma
  (requires (Cons? l))
  (ensures (Cons? l /\
    llist_fragment_tail l phead == (
    llist_fragment_tail (Ghost.hide (unsnoc_hd (Ghost.reveal l))) phead `vdep` llist_fragment_tail_cons_next_payload l `vrewrite` llist_fragment_tail_cons_rewrite l (llist_fragment_tail (Ghost.hide (unsnoc_hd (Ghost.reveal l))) phead)
  )))
= llist_fragment_tail_eq l phead

unfold
let sel_llist_fragment_tail
  (#a:Type) (#p:vprop)
  (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a))
  (h: rmem p { (* FStar.Tactics.with_tactic selector_tactic *) (can_be_split p (llist_fragment_tail l phead)) })
: GTot (ref (ccell_ptrvalue a))
=
  coerce (h (llist_fragment_tail l phead)) (ref (ccell_ptrvalue a))

val intro_llist_fragment_tail_nil
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
: SteelGhost unit opened
    emp
    (fun _ -> llist_fragment_tail l phead)
    (fun _ -> Nil? l)
    (fun _ _ h' -> sel_llist_fragment_tail l phead h' == phead)

let intro_llist_fragment_tail_nil
  l phead
=
  intro_vconst phead;
  change_equal_slprop
    (vconst phead)
    (llist_fragment_tail l phead)

val elim_llist_fragment_tail_nil
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
: SteelGhost unit opened
    (llist_fragment_tail l phead)
    (fun _ -> emp)
    (fun _ -> Nil? l)
    (fun h _ _ -> sel_llist_fragment_tail l phead h == phead)

let elim_llist_fragment_tail_nil
  l phead
=
  change_equal_slprop
    (llist_fragment_tail l phead)
    (vconst phead);
  elim_vconst phead

val intro_llist_fragment_tail_snoc
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
  (ptail: Ghost.erased (ref (ccell_ptrvalue a)))
  (tail: Ghost.erased (ccell_lvalue a))
: SteelGhost (Ghost.erased (list a)) opened
    (llist_fragment_tail l phead `star` vptr ptail `star` vptr (ccell_data tail))
    (fun res -> llist_fragment_tail res phead)
    (fun h -> (
      can_be_split (llist_fragment_tail l phead `star` vptr ptail `star` vptr (ccell_data tail)) (llist_fragment_tail l phead) /\
      can_be_split (llist_fragment_tail l phead `star` vptr ptail `star` vptr (ccell_data tail)) (vptr ptail)) ==> (
      sel_llist_fragment_tail l phead h == Ghost.reveal ptail /\
      h (vptr ptail) == Ghost.reveal tail
    ))
    (fun h res h' ->
      Ghost.reveal res == snoc (Ghost.reveal l) (h (vptr (ccell_data tail))) /\
      sel_llist_fragment_tail res phead h' == ccell_next tail
    )

#push-options "--z3rlimit 16"

let intro_llist_fragment_tail_snoc
  #_ #a l phead ptail tail
=
  reveal_star_3 (llist_fragment_tail l phead) (vptr ptail) (vptr (ccell_data tail));
  let d = gget (vptr (ccell_data tail)) in
  let l' : (l' : Ghost.erased (list a) { Cons? (Ghost.reveal l') }) = Ghost.hide (snoc (Ghost.reveal l) (Ghost.reveal d)) in
  intro_vrefine (vptr (ccell_data tail)) (llist_fragment_tail_cons_data_refine l');
  intro_vrefine (vptr ptail) (ccell_is_lvalue_refine a);
  intro_vdep
    (vptr ptail `vrefine` ccell_is_lvalue_refine a)
    (vptr (ccell_data tail) `vrefine` llist_fragment_tail_cons_data_refine l')
    (llist_fragment_tail_cons_lvalue_payload l');
  change_equal_slprop
    (llist_fragment_tail l phead)
    (llist_fragment_tail (Ghost.hide (unsnoc_hd l')) phead);
  intro_vdep
    (llist_fragment_tail (Ghost.hide (unsnoc_hd l')) phead)
    (vptr ptail `vrefine` ccell_is_lvalue_refine a `vdep` llist_fragment_tail_cons_lvalue_payload l')
    (llist_fragment_tail_cons_next_payload l');
  intro_vrewrite_no_norm
    (llist_fragment_tail (Ghost.hide (unsnoc_hd l')) phead `vdep` llist_fragment_tail_cons_next_payload l')
    (llist_fragment_tail_cons_rewrite l' (llist_fragment_tail (Ghost.hide (unsnoc_hd l')) phead));
  llist_fragment_tail_eq_cons l' phead;
  change_equal_slprop
    (llist_fragment_tail (Ghost.hide (unsnoc_hd l')) phead `vdep` llist_fragment_tail_cons_next_payload l' `vrewrite` llist_fragment_tail_cons_rewrite l' (llist_fragment_tail (Ghost.hide (unsnoc_hd l')) phead))
    (llist_fragment_tail l' phead);
  let g' = gget (llist_fragment_tail l' phead) in
  assert (Ghost.reveal g' == ccell_next tail);
  noop ();
  l'

#pop-options

[@@erasable]
noeq
type ll_unsnoc_t (a: Type) = {
  ll_unsnoc_l: Ghost.erased (list a);
  ll_unsnoc_ptail: Ghost.erased (ref (ccell_ptrvalue a));
  ll_unsnoc_tail: Ghost.erased (ccell_lvalue a);
}

val elim_llist_fragment_tail_snoc
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
: SteelGhost (ll_unsnoc_t a) opened
    (llist_fragment_tail l phead)
    (fun res -> llist_fragment_tail res.ll_unsnoc_l phead `star` vptr res.ll_unsnoc_ptail `star` vptr (ccell_data res.ll_unsnoc_tail))
    (fun _ -> Cons? l)
    (fun h res h' ->
      can_be_split (llist_fragment_tail res.ll_unsnoc_l phead `star` vptr res.ll_unsnoc_ptail `star` vptr (ccell_data res.ll_unsnoc_tail)) (llist_fragment_tail res.ll_unsnoc_l phead) /\
      can_be_split (llist_fragment_tail res.ll_unsnoc_l phead `star` vptr res.ll_unsnoc_ptail `star` vptr (ccell_data res.ll_unsnoc_tail)) (vptr res.ll_unsnoc_ptail) /\
      Cons? l /\
      Ghost.reveal res.ll_unsnoc_l == unsnoc_hd l /\
      h' (vptr res.ll_unsnoc_ptail) == Ghost.reveal res.ll_unsnoc_tail /\
      h' (vptr (ccell_data res.ll_unsnoc_tail)) == unsnoc_tl l /\
      sel_llist_fragment_tail res.ll_unsnoc_l phead h' == Ghost.reveal res.ll_unsnoc_ptail /\
      sel_llist_fragment_tail l phead h == (ccell_next res.ll_unsnoc_tail)
    )

#push-options "--z3rlimit 32"
#restart-solver

let elim_llist_fragment_tail_snoc
  #_ #a l phead
=
  let l0 : (l0: Ghost.erased (list a) { Cons? l0 }) = Ghost.hide (Ghost.reveal l) in
  llist_fragment_tail_eq_cons l0 phead;
  change_equal_slprop
    (llist_fragment_tail l phead)
    (llist_fragment_tail (Ghost.hide (unsnoc_hd l0)) phead `vdep` llist_fragment_tail_cons_next_payload l0 `vrewrite` llist_fragment_tail_cons_rewrite l0 (llist_fragment_tail (Ghost.hide (unsnoc_hd l0)) phead));
  elim_vrewrite_no_norm
    (llist_fragment_tail (Ghost.hide (unsnoc_hd l0)) phead `vdep` llist_fragment_tail_cons_next_payload l0)
    (llist_fragment_tail_cons_rewrite l0 (llist_fragment_tail (Ghost.hide (unsnoc_hd l0)) phead));
  let ptail = elim_vdep
    (llist_fragment_tail (Ghost.hide (unsnoc_hd l0)) phead)
    (llist_fragment_tail_cons_next_payload l0)
  in
  let ptail0 : Ghost.erased (ref (ccell_ptrvalue a)) = ptail in
  change_equal_slprop
    (llist_fragment_tail_cons_next_payload l0 (Ghost.reveal ptail))
    (vptr (Ghost.reveal ptail0) `vrefine` ccell_is_lvalue_refine a `vdep` llist_fragment_tail_cons_lvalue_payload l0);
  let tail = elim_vdep
    (vptr (Ghost.reveal ptail0) `vrefine` ccell_is_lvalue_refine a)
    (llist_fragment_tail_cons_lvalue_payload l0)
  in
  elim_vrefine (vptr (Ghost.reveal ptail0)) (ccell_is_lvalue_refine a);
  let tail0 : Ghost.erased (ccell_lvalue a) = Ghost.hide (Ghost.reveal tail) in
  let res = {
    ll_unsnoc_l = Ghost.hide (unsnoc_hd l0);
    ll_unsnoc_ptail = ptail0;
    ll_unsnoc_tail = tail0;
  } in
  change_equal_slprop
    (vptr (Ghost.reveal ptail0))
    (vptr res.ll_unsnoc_ptail);
  change_equal_slprop
    (llist_fragment_tail_cons_lvalue_payload l0 (Ghost.reveal tail))
    (vptr (ccell_data res.ll_unsnoc_tail) `vrefine` llist_fragment_tail_cons_data_refine l0);
  elim_vrefine
    (vptr (ccell_data res.ll_unsnoc_tail))
    (llist_fragment_tail_cons_data_refine l0);
  change_equal_slprop
    (llist_fragment_tail (Ghost.hide (unsnoc_hd l0)) phead)
    (llist_fragment_tail res.ll_unsnoc_l phead);
  reveal_star_3 (llist_fragment_tail res.ll_unsnoc_l phead) (vptr res.ll_unsnoc_ptail) (vptr (ccell_data res.ll_unsnoc_tail));
  res

#pop-options
  
let rec llist_fragment_tail_append
  (#opened: _)
  (#a: Type)
  (phead0: ref (ccell_ptrvalue a))
  (l1: Ghost.erased (list a))
  (phead1: Ghost.erased (ref (ccell_ptrvalue a)))
  (l2: Ghost.erased (list a))
: SteelGhost (Ghost.erased (list a)) opened
    (llist_fragment_tail l1 phead0 `star` llist_fragment_tail l2 phead1)
    (fun res -> llist_fragment_tail res phead0)
    (fun h ->
      Ghost.reveal phead1 == (sel_llist_fragment_tail l1 phead0) h
    )
    (fun h res h' ->
      Ghost.reveal res == Ghost.reveal l1 `L.append` Ghost.reveal l2 /\
      (sel_llist_fragment_tail res phead0) h' == (sel_llist_fragment_tail l2 phead1) h
    )
    (decreases (L.length (Ghost.reveal l2)))
=
  let g1 = gget (llist_fragment_tail l1 phead0) in
  assert (Ghost.reveal phead1 == Ghost.reveal g1);
  if Nil? l2
  then begin
    L.append_l_nil (Ghost.reveal l1);
    elim_llist_fragment_tail_nil l2 phead1;
    l1
  end else begin
    let res = elim_llist_fragment_tail_snoc l2 (Ghost.reveal phead1) in
    let d = gget (vptr (ccell_data res.ll_unsnoc_tail)) in
    L.append_assoc (Ghost.reveal l1) (Ghost.reveal res.ll_unsnoc_l) [Ghost.reveal d];
    let l3 = llist_fragment_tail_append phead0 l1 phead1 res.ll_unsnoc_l in
    intro_llist_fragment_tail_snoc l3 phead0 res.ll_unsnoc_ptail res.ll_unsnoc_tail
  end

let queue_tail_refine
  (#a: Type)
  (tail1: ref (ccell_ptrvalue a))
  (tail2: ref (ccell_ptrvalue a))
  (tl: normal (t_of (vptr tail2)))
: Tot prop
= ccell_ptrvalue_is_null tl == true /\ tail1 == tail2

[@@__steel_reduce__]
let queue_tail_dep2
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
  (tail1: t_of (llist_fragment_tail l (cllist_head x)))
  (tail2: ref (ccell_ptrvalue a))
: Tot vprop
= vptr tail2 `vrefine` queue_tail_refine tail1 tail2

[@@__steel_reduce__]
let queue_tail_dep1
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
  (tail1: t_of (llist_fragment_tail l (cllist_head x)))
: Tot vprop
= vptr (cllist_tail x) `vdep` queue_tail_dep2 x l tail1

[@@__steel_reduce__; __reduce__]
let queue_tail
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
: Tot vprop
=
  llist_fragment_tail l (cllist_head x) `vdep` queue_tail_dep1 x l

val intro_queue_tail
  (#opened: _)
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
  (tail: ref (ccell_ptrvalue a))
: SteelGhost unit opened
    (llist_fragment_tail l (cllist_head x) `star` vptr (cllist_tail x) `star` vptr tail)
    (fun _ -> queue_tail x l)
    (fun h -> (
      can_be_split 
        (llist_fragment_tail l (cllist_head x) `star` vptr (cllist_tail x) `star` vptr tail)
        (llist_fragment_tail l (cllist_head x)) /\
      can_be_split 
        (llist_fragment_tail l (cllist_head x) `star` vptr (cllist_tail x) `star` vptr tail)
        (vptr (cllist_tail x))
      ) ==> (
      sel_llist_fragment_tail l (cllist_head x) h == tail /\
      h (vptr (cllist_tail x)) == tail /\
      ccell_ptrvalue_is_null (h (vptr tail))
    ))
    (fun _ _ _ -> True)

let intro_queue_tail
  x l tail
=
  reveal_star_3 (llist_fragment_tail l (cllist_head x)) (vptr (cllist_tail x)) (vptr tail);
  intro_vrefine (vptr tail) (queue_tail_refine tail tail);
  intro_vdep2
    (vptr (cllist_tail x))
    (vptr tail `vrefine` queue_tail_refine tail tail)
    tail
    (queue_tail_dep2 x l tail);
  intro_vdep2
    (llist_fragment_tail l (cllist_head x))
    (vptr (cllist_tail x) `vdep` queue_tail_dep2 x l tail)
    tail
    (queue_tail_dep1 x l)

val elim_queue_tail
  (#opened: _)
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
: SteelGhost (Ghost.erased (ref (ccell_ptrvalue a))) opened
    (queue_tail x l)
    (fun tail -> llist_fragment_tail l (cllist_head x) `star` vptr (cllist_tail x) `star` vptr tail)
    (fun h -> True)
    (fun _ tail h ->
      can_be_split 
        (llist_fragment_tail l (cllist_head x) `star` vptr (cllist_tail x) `star` vptr tail)
        (llist_fragment_tail l (cllist_head x)) /\
      can_be_split 
        (llist_fragment_tail l (cllist_head x) `star` vptr (cllist_tail x) `star` vptr tail)
        (vptr (cllist_tail x)) /\
      sel_llist_fragment_tail l (cllist_head x) h == Ghost.reveal tail /\
      h (vptr (cllist_tail x)) == Ghost.reveal tail /\
      ccell_ptrvalue_is_null (h (vptr tail))
    )

let elim_queue_tail
  #_ #a x l
=
  let tail0 = elim_vdep
    (llist_fragment_tail l (cllist_head x))
    (queue_tail_dep1 x l)
  in
  let tail : Ghost.erased (ref (ccell_ptrvalue a)) = tail0 in
  change_equal_slprop
    (queue_tail_dep1 x l (Ghost.reveal tail0))
    (vptr (cllist_tail x) `vdep` queue_tail_dep2 x l tail0);
  let tail2 = elim_vdep
    (vptr (cllist_tail x))
    (queue_tail_dep2 x l tail0)
  in
  let tail3 : Ghost.erased (ref (ccell_ptrvalue a)) = tail2 in
  change_equal_slprop
    (queue_tail_dep2 x l tail0 (Ghost.reveal tail2))
    (vptr tail3 `vrefine` queue_tail_refine tail0 tail3);
  elim_vrefine (vptr tail3) (queue_tail_refine tail0 tail3);
  change_equal_slprop
    (vptr tail3)
    (vptr tail);
  reveal_star_3 (llist_fragment_tail l (cllist_head x)) (vptr (cllist_tail x)) (vptr tail);  
  tail


(* view from the head *)

let llist_fragment_head_data_refine
  (#a: Type)
  (d: a)
  (c: vcell a)
: Tot prop
= c.vcell_data == d

let llist_fragment_head_payload
  (#a: Type)
  (head: ccell_ptrvalue a)
  (d: a)
  (llist_fragment_head: (ref (ccell_ptrvalue a) -> ccell_ptrvalue a -> Tot vprop))
  (x: t_of (ccell_is_lvalue head `star` (ccell head `vrefine` llist_fragment_head_data_refine d)))
: Tot vprop
=
  llist_fragment_head (ccell_next (fst x)) (snd x).vcell_next

let rec llist_fragment_head (#a: Type) (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a)) (head: ccell_ptrvalue a) : Tot vprop
  (decreases (Ghost.reveal l))
=
  if Nil? l
  then vconst (phead, head)
  else
    vbind
      (ccell_is_lvalue head `star` (ccell head `vrefine` llist_fragment_head_data_refine (L.hd (Ghost.reveal l))))
      (ref (ccell_ptrvalue a) & ccell_ptrvalue a)
      (llist_fragment_head_payload head (L.hd (Ghost.reveal l)) (llist_fragment_head (L.tl (Ghost.reveal l))))

let t_of_llist_fragment_head
  (#a: Type) (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a)) (head: ccell_ptrvalue a)
: Lemma
  (t_of (llist_fragment_head l phead head) == ref (ccell_ptrvalue a) & ccell_ptrvalue a)
= ()

unfold
let sel_llist_fragment_head
  (#a:Type) (#p:vprop)
  (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a)) (head: ccell_ptrvalue a)
  (h: rmem p { (* FStar.Tactics.with_tactic selector_tactic *) (can_be_split p (llist_fragment_head l phead head)) })
: GTot (ref (ccell_ptrvalue a) & ccell_ptrvalue a)
=
  coerce (h (llist_fragment_head l phead head)) (ref (ccell_ptrvalue a) & ccell_ptrvalue a)

val intro_llist_fragment_head_nil
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
  (head: ccell_ptrvalue a)
: SteelGhost unit opened
    emp
    (fun _ -> llist_fragment_head l phead head)
    (fun _ -> Nil? l)
    (fun _ _ h' -> sel_llist_fragment_head l phead head h' == (phead, head))

let intro_llist_fragment_head_nil
  l phead head
=
  intro_vconst (phead, head);
  change_equal_slprop
    (vconst (phead, head))
    (llist_fragment_head l phead head)

val elim_llist_fragment_head_nil
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
  (head: ccell_ptrvalue a)
: SteelGhost unit opened
    (llist_fragment_head l phead head)
    (fun _ -> emp)
    (fun _ -> Nil? l)
    (fun h _ _ -> sel_llist_fragment_head l phead head h == (phead, head))

let elim_llist_fragment_head_nil
  l phead head
=
  change_equal_slprop
    (llist_fragment_head l phead head)
    (vconst (phead, head));
  elim_vconst (phead, head)

let llist_fragment_head_eq_cons
  (#a: Type) (l: Ghost.erased (list a)) (phead: ref (ccell_ptrvalue a)) (head: ccell_ptrvalue a)
: Lemma
  (requires (Cons? (Ghost.reveal l)))
  (ensures (
    llist_fragment_head l phead head ==
    vbind
      (ccell_is_lvalue head `star` (ccell head `vrefine` llist_fragment_head_data_refine (L.hd (Ghost.reveal l))))
      (ref (ccell_ptrvalue a) & ccell_ptrvalue a)
      (llist_fragment_head_payload head (L.hd (Ghost.reveal l)) (llist_fragment_head (L.tl (Ghost.reveal l))))    
  ))
= assert_norm
    (llist_fragment_head l phead head == (
      if Nil? l
      then vconst (phead, head)
      else
        vbind
          (ccell_is_lvalue head `star` (ccell head `vrefine` llist_fragment_head_data_refine (L.hd (Ghost.reveal l))))
          (ref (ccell_ptrvalue a) & ccell_ptrvalue a)
          (llist_fragment_head_payload head (L.hd (Ghost.reveal l)) (llist_fragment_head (L.tl (Ghost.reveal l))))
    ))

assume
val intro_llist_fragment_head_cons
  (#opened: _)
  (#a: Type) (phead: ref (ccell_ptrvalue a)) (head: ccell_lvalue a) (next: (ccell_ptrvalue a)) (tl: Ghost.erased (list a))
: SteelGhost (Ghost.erased (list a)) opened
    (ccell head `star` llist_fragment_head tl (ccell_next head) next)
    (fun res -> llist_fragment_head res phead head)
    (fun h -> (h (ccell head)).vcell_next == next)
    (fun h res h' ->
      Ghost.reveal res == (h (ccell head)).vcell_data :: Ghost.reveal tl /\
      h' (llist_fragment_head res phead head) == h (llist_fragment_head tl (ccell_next head) next)
    )

[@@erasable]
noeq
type ll_uncons_t
  (a: Type)
= {
  ll_uncons_pnext: Ghost.erased (ref (ccell_ptrvalue a));
  ll_uncons_next: Ghost.erased (ccell_ptrvalue a);
  ll_uncons_tl: Ghost.erased (list a);
}

assume
val elim_llist_fragment_head_cons
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
  (head: ccell_ptrvalue a)
: SteelGhost (ll_uncons_t a) opened
    (llist_fragment_head l phead head)
    (fun res -> ccell head `star` llist_fragment_head res.ll_uncons_tl res.ll_uncons_pnext res.ll_uncons_next)
    (fun _ -> Cons? (Ghost.reveal l))
    (fun h res h' ->
      ccell_ptrvalue_is_null head == false /\
      Ghost.reveal l == (h' (ccell head)).vcell_data :: Ghost.reveal res.ll_uncons_tl /\
      Ghost.reveal res.ll_uncons_pnext == ccell_next head /\
      Ghost.reveal res.ll_uncons_next == (h' (ccell head)).vcell_next /\
      h' (llist_fragment_head res.ll_uncons_tl res.ll_uncons_pnext res.ll_uncons_next) == h (llist_fragment_head l phead head)
    )

assume
val llist_fragment_head_append
  (#opened: _)
  (#a: Type)
  (l1: Ghost.erased (list a))
  (phead1: ref (ccell_ptrvalue a))
  (head1: ccell_ptrvalue a)
  (l2: Ghost.erased (list a))
  (phead2: ref (ccell_ptrvalue a))
  (head2: ccell_ptrvalue a)
: SteelGhost (Ghost.erased (list a)) opened
    (llist_fragment_head l1 phead1 head1 `star` llist_fragment_head l2 phead2 head2)
    (fun l -> llist_fragment_head l phead1 head1)
    (fun h -> sel_llist_fragment_head l1 phead1 head1 h == (Ghost.reveal phead2, Ghost.reveal head2))
    (fun h l h' ->
      Ghost.reveal l == Ghost.reveal l1 `L.append` Ghost.reveal l2 /\
      h' (llist_fragment_head l phead1 head1) == h (llist_fragment_head l2 phead2 head2)
    )

let rec llist_fragment_head_to_tail
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
  (head: ccell_ptrvalue a)
: SteelGhost (Ghost.erased (ref (ccell_ptrvalue a))) opened
    (vptr phead `star` llist_fragment_head l phead head)
    (fun res -> llist_fragment_tail l phead `star` vptr res) 
    (fun h -> h (vptr phead) == head)
    (fun h res h' ->
      let v = sel_llist_fragment_head l phead head h in
      fst v == Ghost.reveal res /\
      fst v == sel_llist_fragment_tail l phead h' /\
      snd v == h' (vptr res)
    )
    (decreases (L.length (Ghost.reveal l)))
=
  if Nil? l
  then begin
    let ptail = Ghost.hide phead in
    let gh = gget (vptr phead) in
    assert (Ghost.reveal gh == head);
    elim_llist_fragment_head_nil l phead head;
    intro_llist_fragment_tail_nil l phead;
    change_equal_slprop
      (vptr phead)
      (vptr ptail);
    ptail
  end else begin
    intro_llist_fragment_tail_nil [] phead;
    change_equal_slprop
      (vptr phead)
      (vptr (Ghost.reveal (Ghost.hide phead)));
    let uc = elim_llist_fragment_head_cons l phead head in
    let head' = elim_ccell_ghost head in
    change_equal_slprop
      (vptr (ccell_next head'))
      (vptr uc.ll_uncons_pnext);
    let lc = intro_llist_fragment_tail_snoc [] phead phead head' in
    let ptail = llist_fragment_head_to_tail
      uc.ll_uncons_tl
      uc.ll_uncons_pnext
      uc.ll_uncons_next
    in
    let l' = llist_fragment_tail_append phead lc uc.ll_uncons_pnext uc.ll_uncons_tl in
    change_equal_slprop
      (llist_fragment_tail l' phead)
      (llist_fragment_tail l phead);
    ptail
  end

#push-options "--z3rlimit 16"
#restart-solver

let rec llist_fragment_tail_to_head
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
  (ptail: ref (ccell_ptrvalue a))
: SteelGhost (Ghost.erased (ccell_ptrvalue a)) opened
    (llist_fragment_tail l phead `star` vptr ptail) 
    (fun head -> vptr phead `star` llist_fragment_head l phead (Ghost.reveal head))
    (fun h -> Ghost.reveal ptail == sel_llist_fragment_tail l phead h)
    (fun h head h' ->
      let v = sel_llist_fragment_head l phead head h' in
      fst v == ptail /\
      snd v == h (vptr ptail) /\
      h' (vptr phead) == Ghost.reveal head
    )
    (decreases (L.length (Ghost.reveal l)))
=
  if Nil? l
  then begin
    let g = gget (llist_fragment_tail l phead) in
    assert (Ghost.reveal g == ptail);
    elim_llist_fragment_tail_nil l phead;
    change_equal_slprop
      (vptr ptail)
      (vptr phead);
    let head = gget (vptr phead) in
    intro_llist_fragment_head_nil l phead head;
    head
  end else begin
    let us = elim_llist_fragment_tail_snoc l phead in
    let tail = gget (vptr ptail) in
    assert (ccell_next us.ll_unsnoc_tail == ptail);
    intro_llist_fragment_head_nil [] (ccell_next us.ll_unsnoc_tail) tail;
    change_equal_slprop
      (vptr ptail)
      (vptr (ccell_next us.ll_unsnoc_tail));
    intro_ccell us.ll_unsnoc_tail;
    let lc = intro_llist_fragment_head_cons us.ll_unsnoc_ptail us.ll_unsnoc_tail tail [] in
    let head = llist_fragment_tail_to_head us.ll_unsnoc_l phead us.ll_unsnoc_ptail in
    let g = gget (llist_fragment_head us.ll_unsnoc_l phead head) in
    let g : Ghost.erased (ref (ccell_ptrvalue a) & ccell_ptrvalue a) = Ghost.hide (Ghost.reveal g) in
    assert (Ghost.reveal g == (Ghost.reveal us.ll_unsnoc_ptail, Ghost.reveal us.ll_unsnoc_tail));
    let l' = llist_fragment_head_append us.ll_unsnoc_l phead head lc us.ll_unsnoc_ptail us.ll_unsnoc_tail in
    change_equal_slprop
      (llist_fragment_head l' phead head)
      (llist_fragment_head l phead head);
    head
  end

#pop-options

val llist_fragment_head_is_nil
  (#opened: _)
  (#a: Type)
  (l: Ghost.erased (list a))
  (phead: ref (ccell_ptrvalue a))
  (head: ccell_ptrvalue a)
: SteelGhost unit opened
    (llist_fragment_head l phead head)
    (fun _ -> llist_fragment_head l phead head)
    (fun h -> ccell_ptrvalue_is_null (snd (sel_llist_fragment_head l phead head h)) == true)
    (fun h _ h' ->
      Nil? l == ccell_ptrvalue_is_null head /\
      h' (llist_fragment_head l phead head) == h (llist_fragment_head l phead head)
    )

let llist_fragment_head_is_nil
  l phead head
=
  if Nil? l
  then begin
    elim_llist_fragment_head_nil l phead head;
    assert (ccell_ptrvalue_is_null head == true);
    intro_llist_fragment_head_nil l phead head
  end else begin
    let r = elim_llist_fragment_head_cons l phead head in
    let head2 : ccell_lvalue _ = head in
    change_equal_slprop
      (llist_fragment_head r.ll_uncons_tl r.ll_uncons_pnext r.ll_uncons_next)
      (llist_fragment_head r.ll_uncons_tl (ccell_next head2) r.ll_uncons_next);
    change_equal_slprop
      (ccell head)
      (ccell head2);
    let l' = intro_llist_fragment_head_cons phead head2 r.ll_uncons_next r.ll_uncons_tl in
    change_equal_slprop
      (llist_fragment_head l' phead head2)
      (llist_fragment_head l phead head)
  end

let queue_head_refine
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
  (hd: ccell_ptrvalue a)
  (ptl: t_of (llist_fragment_head l (cllist_head x) hd))
  (tl: ref (ccell_ptrvalue a))
: Tot prop
= let ptl : (ref (ccell_ptrvalue a) & ccell_ptrvalue a) = ptl in
  tl == fst ptl /\ ccell_ptrvalue_is_null (snd ptl) == true

let queue_head_dep1
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
  (hd: ccell_ptrvalue a)
  (ptl: t_of (llist_fragment_head l (cllist_head x) hd))
: Tot vprop
= vptr (cllist_tail x) `vrefine` queue_head_refine x l hd ptl

let queue_head_dep2
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
  (hd: ccell_ptrvalue a)
: Tot vprop
= llist_fragment_head l (cllist_head x) hd `vdep` queue_head_dep1 x l hd

[@@__reduce__]
let queue_head
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
: Tot vprop
= vptr (cllist_head x) `vdep` queue_head_dep2 x l

val intro_queue_head
  (#opened: _)
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
  (hd: Ghost.erased (ccell_ptrvalue a))
: SteelGhost unit opened
    (vptr (cllist_head x) `star` llist_fragment_head l (cllist_head x) hd `star` vptr (cllist_tail x))
    (fun _ -> queue_head x l)
    (fun h -> (
        can_be_split (vptr (cllist_head x) `star` llist_fragment_head l (cllist_head x) hd `star` vptr (cllist_tail x)) (llist_fragment_head l (cllist_head x) hd) /\
        can_be_split (vptr (cllist_head x) `star` llist_fragment_head l (cllist_head x) hd `star` vptr (cllist_tail x)) (vptr (cllist_head x))
      ) ==> (
        let frag = (sel_llist_fragment_head l (cllist_head x) hd) h in
        h (vptr (cllist_head x)) == Ghost.reveal hd /\
        h (vptr (cllist_tail x)) == fst frag /\
        ccell_ptrvalue_is_null (snd frag) == true
    ))
    (fun _ _ _ -> True)

let intro_queue_head
  #_ #a x l hd
=
  reveal_star_3 (vptr (cllist_head x)) (llist_fragment_head l (cllist_head x) hd) (vptr (cllist_tail x));
  let ptl = gget (llist_fragment_head l (cllist_head x) hd) in
  intro_vrefine
    (vptr (cllist_tail x))
    (queue_head_refine x l hd ptl);
  assert_norm (vptr (cllist_tail x) `vrefine` queue_head_refine x l hd ptl == queue_head_dep1 x l hd ptl);
  intro_vdep
    (llist_fragment_head l (cllist_head x) hd)
    (vptr (cllist_tail x) `vrefine` queue_head_refine x l hd ptl)
    (queue_head_dep1 x l hd);
  intro_vdep
    (vptr (cllist_head x))
    (llist_fragment_head l (cllist_head x) hd `vdep` queue_head_dep1 x l hd)
    (queue_head_dep2 x l)

val elim_queue_head
  (#opened: _)
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
: SteelGhost (Ghost.erased (ccell_ptrvalue a)) opened
    (queue_head x l)
    (fun hd -> vptr (cllist_head x) `star` llist_fragment_head l (cllist_head x) hd `star` vptr (cllist_tail x))
    (fun _ -> True)
    (fun _ hd h -> (
        can_be_split (vptr (cllist_head x) `star` llist_fragment_head l (cllist_head x) hd `star` vptr (cllist_tail x)) (llist_fragment_head l (cllist_head x) hd) /\
        can_be_split (vptr (cllist_head x) `star` llist_fragment_head l (cllist_head x) hd `star` vptr (cllist_tail x)) (vptr (cllist_head x)) /\ (
        let frag = (sel_llist_fragment_head l (cllist_head x) hd) h in
        h (vptr (cllist_head x)) == Ghost.reveal hd /\
        h (vptr (cllist_tail x)) == fst frag /\
        ccell_ptrvalue_is_null (snd frag) == true
    )))

let elim_queue_head
  #_ #a x l
=
  let hd = elim_vdep
    (vptr (cllist_head x))
    (queue_head_dep2 x l)
  in
  let ptl = elim_vdep
    (llist_fragment_head l (cllist_head x) hd)
    (queue_head_dep1 x l hd)
  in
  elim_vrefine
    (vptr (cllist_tail x))
    (queue_head_refine x l hd ptl);
  reveal_star_3 (vptr (cllist_head x)) (llist_fragment_head l (cllist_head x) hd) (vptr (cllist_tail x));
  hd

let queue_head_to_tail
  (#opened: _)
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
: SteelGhostT unit opened
    (queue_head x l)
    (fun _ -> queue_tail x l)
=
  let hd = elim_queue_head x l in
  let tl = llist_fragment_head_to_tail l (cllist_head x) hd in
  intro_queue_tail x l tl

let queue_tail_to_head
  (#opened: _)
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list a))
: SteelGhostT unit opened
    (queue_tail x l)
    (fun _ -> queue_head x l)
=
  let tl = elim_queue_tail x l in
  let hd = llist_fragment_tail_to_head l (cllist_head x) tl in
  intro_queue_head x l hd

(* We choose the head representation, since queue_is_empty and dequeue
need the head representation, but only enqueue needs the tail
representation. *)

[@@__reduce__]
let queue x l = queue_head x l

#push-options "--ide_id_info_off" // necessary because of fst, snd in the post-resource (likely caught by normal(). This does not happen with other projectors)

let create_queue a =
  let head = ccell_ptrvalue_null a in
  let tail : ref (ccell_ptrvalue a) = null in
  let l0 = alloc_llist head tail in
  let l = elim_cllist l0 in
  write (cllist_tail l) (cllist_head l);
  intro_llist_fragment_head_nil [] (cllist_head l) (Ghost.reveal (Ghost.hide head));
  reveal_star_3 (vptr (cllist_head l)) (llist_fragment_head [] (cllist_head l) (Ghost.reveal (Ghost.hide head))) (vptr (cllist_tail l));
  intro_queue_head l [] head;
  let res : (t a & Ghost.erased (v a)) = (l0, Ghost.hide []) in
  change_equal_slprop
    (queue_head l [])
    (queue (fst res) (snd res));
  return res

let enqueue #a x l w =
  queue_head_to_tail x l;
  let ptail0 = elim_queue_tail x l in
  let ptail = read (cllist_tail x) in
  let c = alloc_cell w (ccell_ptrvalue_null a) in
  let c0 = elim_ccell_ghost c in
  change_equal_slprop
    (vptr ptail0)
    (vptr ptail);
  write ptail c;
  change_equal_slprop
    (vptr ptail)
    (vptr ptail0);
  let l' = intro_llist_fragment_tail_snoc l (cllist_head x) ptail0 c0 in
  write (cllist_tail x) (ccell_next c);
  intro_queue_tail x l' (ccell_next c0);
  queue_tail_to_head x l';
  return l'

let queue_is_empty #a x l =
  let head0 = elim_queue_head x l in
  let head = read (cllist_head x) in
  let res = ccell_ptrvalue_is_null head in
  llist_fragment_head_is_nil l (cllist_head x) head0;
  intro_queue_head x l head0;
  return res

let dequeue #a x l =
  let head0 = elim_queue_head x l in
  let head = read (cllist_head x) in
  let u = elim_llist_fragment_head_cons l (cllist_head x) head0 in
  change_equal_slprop
    (ccell head0)
    (ccell head);
  let head = elim_ccell head in
  let data = read (ccell_data head) in
  let next = read (ccell_next head) in
  intro_ccell head;
  free_cell head;
  llist_fragment_head_is_nil u.ll_uncons_tl u.ll_uncons_pnext u.ll_uncons_next;
  assert (Nil? u.ll_uncons_tl == ccell_ptrvalue_is_null next);
  write (cllist_head x) next;
  if ccell_ptrvalue_is_null next
  then begin
    elim_llist_fragment_head_nil u.ll_uncons_tl u.ll_uncons_pnext u.ll_uncons_next;
    write (cllist_tail x) (cllist_head x);
    intro_llist_fragment_head_nil [] (cllist_head x) (Ghost.reveal (Ghost.hide next));
    intro_queue_head x [] next;
    let res = (data, Ghost.hide []) in
    change_equal_slprop
      (queue_head x [])
      (queue x (snd res));
    return res
  end else begin
    let u2 = elim_llist_fragment_head_cons u.ll_uncons_tl u.ll_uncons_pnext u.ll_uncons_next in
    let next2 : Ghost.erased (ccell_lvalue a) = next in
    change_equal_slprop
      (ccell u.ll_uncons_next)
      (ccell next2);
    change_equal_slprop
      (llist_fragment_head u2.ll_uncons_tl u2.ll_uncons_pnext u2.ll_uncons_next)
      (llist_fragment_head u2.ll_uncons_tl (ccell_next next2) u2.ll_uncons_next);
    let l' = intro_llist_fragment_head_cons (cllist_head x) next2 u2.ll_uncons_next u2.ll_uncons_tl in
    change_equal_slprop
      (llist_fragment_head l' (cllist_head x) next2)
      (llist_fragment_head l' (cllist_head x) u.ll_uncons_next);
    intro_queue_head x l' u.ll_uncons_next;
    let res = (data, l') in
    change_equal_slprop
      (queue_head x l')
      (queue x (snd res));
    return res
  end
