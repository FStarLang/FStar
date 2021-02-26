module Queue

let pure_upd_next
  (#a: Type0)
  (c: cell a)
  (next: t a)
: Tot (cell a)
= {c with next = next}

assume
val upd_next
  (#a: Type0) (#u: _) (#v: Ghost.erased (cell a)) (x:t a) (nxt:t a)
     : SteelAtomic unit u observable (pts_to x v)
                            (fun _ -> pts_to x (pure_upd_next v nxt))
                            (requires (fun _ -> True))
                            (ensures (fun _ _ _ -> True))

let rec fragment
  (#a: Type0)
  (pstart: Ghost.erased (ref (cell a)))
  (l: Ghost.erased (list (ref (cell a) & cell a)))
: Tot slprop
  (decreases (Ghost.reveal l))
=
  match Ghost.reveal l with
  | [] -> emp
  | (pa, a) :: q -> pts_to pa a `star` fragment a.next q `star` pure (Ghost.reveal pstart == pa)

let slprop_extensionality (p q:slprop)
  : Lemma
    (requires p `equiv` q)
    (ensures p == q)
    [SMTPat (p `equiv` q)]
=
  slprop_extensionality p q

inline_for_extraction noextract let canon () : FStar.Tactics.Tac unit =
  (Steel.Memory.Tactics.canon ())

let emp_equiv_pure
  (p: prop)
: Lemma
  (requires p)
  (ensures (emp `equiv` pure p))
=
  Classical.forall_intro intro_emp;
  Classical.forall_intro (pure_interp p)

let rec next_last
  (#a: Type)
  (pstart: ref (cell a))
  (l: list (ref (cell a) & cell a))
: Tot (ref (cell a))
  (decreases l)
= match l with
  | [] -> pstart
  | (_, c) :: q -> next_last c.next q

let rec next_last_correct
  (#a: Type)
  (pstart: ref (cell a))
  (l: list (ref (cell a) & cell a))
: Lemma
  (requires (Cons? l))
  (ensures (next_last pstart l == (snd (L.last l)).next))
  (decreases l)
=
  match l with
  | [a] -> ()
  | (_, c) :: q -> next_last_correct c.next q

let rec fragment_append
  (#a: Type0)
  (pstart: Ghost.erased (ref (cell a)))
  (l1: Ghost.erased (list (ref (cell a) & cell a)))
  (l2: Ghost.erased (list (ref (cell a) & cell a)))
: Lemma
  (ensures ((
    fragment pstart l1 `star` fragment (next_last pstart l1) l2
  ) `equiv` (
    fragment pstart (l1 `L.append` l2)
  )))
  (decreases (Ghost.reveal l1))
= match Ghost.reveal l1 with
  | [] -> ()
  | (pa, a) :: q ->
    assert ((
      (pts_to pa a `star` fragment a.next q `star` pure (Ghost.reveal pstart == pa)) `star` fragment (next_last pstart l1) l2
    ) `equiv` (
      pts_to pa a `star` (fragment a.next q `star` fragment (next_last pstart l1) l2) `star` pure (Ghost.reveal pstart == pa)
    )) by canon ();
    fragment_append a.next q l2

let get_data
  (#a: Type)
  (x: (ref (cell a) & cell a))
: Tot a
= (snd x).data

unfold
let queue_lc_prop
  (#a: Type0)
  (tl: Ghost.erased (ref (cell a)))
  (l: Ghost.erased (list a))
  (lc: Ghost.erased (list (ref (cell a) & cell a)))
: Tot prop
= Cons? l /\
  Ghost.reveal l == List.Tot.map get_data lc /\
  Ghost.reveal tl == fst (L.last lc) /\
  is_null (snd (L.last lc)).next

let queue_lc
  (#a: Type0)
  (hd tl: Ghost.erased (ref (cell a)))
  (l: Ghost.erased (list a))
  (lc: Ghost.erased (list (ref (cell a) & cell a)))
: Tot slprop
= fragment hd lc `star` pure (queue_lc_prop tl l lc)

let queue_l
  #a hd tl l
=
  h_exists (queue_lc hd tl l)

let new_queue
  #a v
=
  let c : cell a = {data = v; next = null} in
  let pc : t a = alloc c in
  intro_pure (queue_lc_prop pc [v] [(pc, c)]);
  intro_pure (Ghost.reveal (Ghost.hide pc) == pc);
  change_slprop ((pts_to pc c `star` emp `star` pure (Ghost.reveal (Ghost.hide pc) == pc)) `star` pure (queue_lc_prop pc [v] [(pc, c)])) (queue_lc pc pc [v] [(pc, c)]) (fun _ -> ());
  intro_exists (Ghost.hide [(pc, c)]) (queue_lc pc pc [v]);
  intro_exists (Ghost.hide [v]) (queue_l pc pc);
  pc

#push-options "--ide_id_info_off --print_implicits"

let witness_h_exists_erased (#a:Type) (#opened_invariants:_) (#p: Ghost.erased a -> slprop) (_:unit)
  : SteelAtomicT (Ghost.erased a) opened_invariants unobservable
                (h_exists p) (fun x -> p x)
=
  let w = witness_h_exists #(Ghost.erased a) #_ #p () in
  Ghost.reveal w

let snoc_inj (#a: Type) (hd1 hd2: list a) (tl1 tl2: a) : Lemma
  (requires (hd1 `L.append` [tl1] == hd2 `L.append` [tl2]))
  (ensures (hd1 == hd2 /\ tl1 == tl2))
  [SMTPat (hd1 `L.append` [tl1]); SMTPat (hd2 `L.append` [tl2])]
= L.lemma_snoc_unsnoc (hd1, tl1);
  L.lemma_snoc_unsnoc (hd2, tl2)

[@"opaque_to_smt"]
let unsnoc (#a: Type) (l: list a) : Pure (list a & a)
  (requires (Cons? l))
  (ensures (fun (hd, tl) -> l == hd `L.append` [tl]))
=
  L.lemma_unsnoc_snoc l;
  L.unsnoc l

let unsnoc_hd (#a: Type) (l: list a) : Pure (list a) (requires (Cons? l)) (ensures (fun _ -> True)) = fst (unsnoc l)
let unsnoc_tl (#a: Type) (l: list a) : Pure (a) (requires (Cons? l)) (ensures (fun _ -> True)) = snd (unsnoc l)

let enqueue
  #a #u #hd tl #v last
=
  let l : (Ghost.erased (list a)) = witness_h_exists_erased () in
  let lc0 : Ghost.erased (list (ref (cell a) & cell a)) = witness_h_exists_erased () in
  change_slprop (queue_lc hd tl l lc0) (fragment hd lc0 `star` pure (queue_lc_prop tl l lc0)) (fun _ -> ());
  elim_pure (queue_lc_prop tl l lc0);
  (* I don't have a pointer to the next field, so I need to manually change the next field of the last cell of the list *)
  let lc : (lc: Ghost.erased (list (ref (cell a) & cell a)) { Cons? (Ghost.reveal lc) }) = lc0 in
  change_slprop (fragment hd lc0) (fragment hd lc) (fun _ -> ());
  let lhd = Ghost.hide (unsnoc_hd (Ghost.reveal lc)) in
  let ltl = Ghost.hide (unsnoc_tl (Ghost.reveal lc)) in
  L.lemma_append_last lhd [Ghost.reveal ltl];
  next_last_correct hd lc;  
  change_slprop
    (fragment hd lc)
    (fragment hd lhd `star` (pts_to tl (Ghost.hide (snd ltl)) `star` emp `star` pure (next_last hd lhd == fst ltl)))
    (fun _ -> fragment_append hd lhd [Ghost.reveal ltl]);
  upd_next tl last;
  let c1 = Ghost.hide (pure_upd_next (snd ltl) last) in
  let lc1 : (lc: Ghost.erased (list (ref (cell a) & cell a)) { Cons? (Ghost.reveal lc) }) = Ghost.hide (lhd `L.append` [(fst ltl, Ghost.reveal c1)]) in
  next_last_correct hd lc1;
  L.lemma_append_last lhd [(fst ltl, Ghost.reveal c1)];
  change_slprop
    (fragment hd lhd `star` (pts_to tl _  `star` emp `star` pure (next_last hd lhd == fst ltl)))
    (fragment hd lc1)
    (fun _ -> fragment_append hd lhd [(fst ltl, Ghost.reveal c1)]);
  intro_pure (Ghost.reveal (Ghost.hide last) == last);
  let lc2 = Ghost.hide (lc1 `L.append` [(last, Ghost.reveal v)]) in
  change_slprop
    (fragment hd lc1 `star` (pts_to last _ `star` emp `star` pure (Ghost.reveal (Ghost.hide last) == last)))
    (fragment hd lc2)
    (fun _ -> fragment_append hd lc1 [(last, Ghost.reveal v)]);
  let l2 = Ghost.hide (l `L.append` [v.data]) in
  L.map_append get_data lhd [Ghost.reveal ltl];
  L.map_append get_data lhd [(fst ltl, Ghost.reveal c1)];
  L.map_append get_data lc1 [(last, Ghost.reveal v)];
  L.lemma_append_last lc1 [(last, Ghost.reveal v)];
  intro_pure (queue_lc_prop last l2 lc2);
  change_slprop (fragment hd lc2 `star` pure (queue_lc_prop last l2 lc2)) (queue_lc hd last l2 lc2) (fun _ -> ());
  intro_exists lc2 (queue_lc hd last l2);
  intro_exists l2 (queue_l hd last)

let dequeue
  #a #u #tl hd
=
  change_slprop emp emp (fun _ -> ());
  None
