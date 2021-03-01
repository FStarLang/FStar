module LListQueue
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
include LListQueue.LList
module L = FStar.List.Tot

(* High-level value, should not be used in C code outside of specs *)

noeq
type v (a: Type0) = {
  vllist: vllist a;
  cells: list (ccell_lvalue a & vcell a);
}

let (==) (#a:_) (x y: a) : prop = x == y

let rec llist_fragment (#a:Type) (rptr: ref (ccell_ptrvalue a))
                                 (ptr: ccell_ptrvalue a)
                                 (l:Ghost.erased (list (ccell_lvalue a & vcell a)))
    : Tot slprop (decreases (Ghost.reveal l))
    =
    match Ghost.reveal l with
    | [] -> emp
    | (chd, vhd) :: tl ->
      pts_to rptr full_perm ptr `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
      llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
      pure (chd == ptr)

inline_for_extraction noextract let canon () : FStar.Tactics.Tac unit =
  (Steel.Memory.Tactics.canon ())

let rec next_last
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
: Tot (Ghost.erased (ref (ccell_ptrvalue a) & ccell_ptrvalue a))
  (decreases (Ghost.reveal l))
=
  match Ghost.reveal l with
  | [] -> Ghost.hide (rptr, ptr)
  | (ca, va) :: q -> next_last (ccell_next ca) va.vcell_next q

let rec next_last_correct
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
: Lemma
  (requires (Cons? l))
  (ensures (
    let (ca', va') = L.last l in
    let (ca, va) = Ghost.reveal (next_last rptr ptr l) in
    ca == ccell_next ca' /\
    va == va'.vcell_next
  ))
  (decreases (Ghost.reveal l))
= match Ghost.reveal l with
  | [_] -> ()
  | (ca, va) :: q -> next_last_correct (ccell_next ca) va.vcell_next (Ghost.hide q)

let slprop_extensionality (p q:slprop)
  : Lemma
    (requires p `equiv` q)
    (ensures p == q)
    [SMTPat (p `equiv` q)]
=
  slprop_extensionality p q

let rec llist_fragment_append
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l1: Ghost.erased (list (ccell_lvalue a & vcell a)))
  (l2: Ghost.erased (list (ccell_lvalue a & vcell a)))
: Lemma
  (requires True)
  (ensures (((llist_fragment rptr ptr l1 `star` llist_fragment (fst (next_last rptr ptr l1)) (snd (next_last rptr ptr l1))  l2)) `equiv` llist_fragment rptr ptr (l1 `L.append` l2)))
  (decreases (Ghost.reveal l1))
= match Ghost.reveal l1 with
  | [] ->
    assert (
      (emp `star` llist_fragment rptr ptr l2) `equiv` llist_fragment rptr ptr l2
    ) by canon ()
  | (chd, vhd) :: tl ->
    assert ((
      (
        pts_to rptr full_perm ptr `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
        pure (chd == ptr)
      ) `star`
      llist_fragment (fst (next_last (ccell_next chd) vhd.vcell_next tl)) (snd (next_last (ccell_next chd) vhd.vcell_next tl)) l2
    ) `equiv` (
        pts_to rptr full_perm ptr `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        (
          llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
          llist_fragment (fst (next_last (ccell_next chd) vhd.vcell_next tl)) (snd (next_last (ccell_next chd) vhd.vcell_next tl)) l2
        ) `star`
        pure (chd == ptr)
    )) by canon ();
    llist_fragment_append (ccell_next chd) vhd.vcell_next tl l2

(* I <3 equiv extensionality *)

(* I need to account for changing the next pointer of the last cell *)

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

let update_next_last
  (#a: Type)
  (l: list (ccell_lvalue a & vcell a))
  (n: ccell_ptrvalue a)
: Tot (list (ccell_lvalue a & vcell a))
= match l with
  | [] -> l
  | _ ->
    let (ctl, vtl) = unsnoc_tl l in
    unsnoc_hd l `L.append` [(ctl, { vcell_data = vtl.vcell_data; vcell_next = n })]

let next_last_update_next_last
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
  (n: ccell_ptrvalue a)
: Lemma
  (requires (Cons? l))
  (ensures (next_last rptr ptr (update_next_last l n) == Ghost.hide (fst (next_last rptr ptr l), n)))
= next_last_correct rptr ptr l;
  next_last_correct rptr ptr (update_next_last l n);
  let (ctl, vtl) = unsnoc_tl l in
  L.lemma_append_last (unsnoc_hd l) [(unsnoc_tl l)];
  L.lemma_append_last (unsnoc_hd l) [(ctl, { vcell_data = vtl.vcell_data; vcell_next = n })]

let llist_fragment_update_next_last
  (#a: Type)
  (rptr: ref (ccell_ptrvalue a))
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
  (n: ccell_ptrvalue a)
: Lemma
  (llist_fragment rptr ptr (update_next_last l n) `equiv` llist_fragment rptr ptr l)
= match Ghost.reveal l with
  | [] -> ()
  | _ ->
    let hd = unsnoc_hd l in
    let (ctl, vtl) = unsnoc_tl l in
    llist_fragment_append rptr ptr hd [(ctl, vtl)];
    llist_fragment_append rptr ptr hd [(ctl, { vcell_data = vtl.vcell_data; vcell_next = n })]


(* The singly-linked list as a queue *)

let queue_prop
  (#a: Type) (x: cllist_lvalue a) (l: Ghost.erased (v a))
: Tot prop
=
  fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
  ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true

let queue (#a: Type) (x: cllist_lvalue a) (l: Ghost.erased (v a)) : Tot slprop =
  pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
  llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
  pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
  pure (queue_prop x l)

#push-options "--ide_id_info_off"

let unpack_queue
  (#a: Type)
  (x: cllist_lvalue a) (l: Ghost.erased (v a))
: Steel unit
    (queue x l)
    (fun _ -> pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    (requires (fun _ -> True))
    (ensures (fun _ _ _ ->
      fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
      ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true
    ))
= change_slprop
    (queue x l)
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      pure (queue_prop x l))
    (fun _ -> ());
  elim_pure (queue_prop x l)

let pack_queue
  (#a: Type)
  (x: cllist_lvalue a) (l: Ghost.erased (v a))
: Steel unit
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    (fun _ -> queue x l)
    (requires (fun _ ->
      fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
      ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true
    ))
    (ensures (fun _ _ _ -> True))
= intro_pure (queue_prop x l);
  change_slprop
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      pure (queue_prop x l))
    (queue x l)
    (fun _ -> ())

let pack_queue1
  (#a: Type)
  (x: cllist_lvalue a) (l: Ghost.erased (v a))
  (tail1: _) (vtail1: Ghost.erased _)
  (tail2: _) (vtail2: Ghost.erased _)
: Steel unit
    (pts_to tail1 full_perm vtail1 `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to tail2 full_perm vtail2)
    (fun _ -> queue x l)
    (requires (fun _ ->
      tail1 == cllist_tail x /\
      Ghost.reveal vtail1 == l.vllist.vllist_tail /\
      tail2 == l.vllist.vllist_tail /\
      Ghost.reveal vtail2 == ccell_ptrvalue_null a /\
      fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
      ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true
    ))
    (ensures (fun _ _ _ -> True))
=
  change_slprop
    (pts_to (tail1) full_perm vtail1)
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail)
    (fun _ -> ());
  change_slprop
    (pts_to (tail2) full_perm vtail2)
    (pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    (fun _ -> ());
  pack_queue x l

let change_equiv_slprop
  (p q: slprop)
  (sq: (unit -> Lemma (p `equiv` q)))
: SteelT unit
    p
    (fun _ -> q)
=
  change_slprop p q (fun _ -> sq ())

let change_equal_slprop
  (p q: slprop)
  (sq: (unit -> Lemma (p == q)))
: SteelT unit
    p
    (fun _ -> q)
= change_equiv_slprop p q (fun _ -> sq ())

let get_data
  (#a: Type0)
  (x: (ccell_lvalue a & vcell a))
: Tot a
= (snd x).vcell_data

let datas
  (#a: Type0)
  (l: v a)
: Tot (list a)
= L.map get_data l.cells

let get_data_update_next_last
  (#a: Type)
  (l: (list (ccell_lvalue a & vcell a)))
  (n: ccell_ptrvalue a)
: Lemma
  (L.map get_data (update_next_last l n) == L.map get_data l)
= match l with
  | [] -> ()
  | _ ->
    let hd = unsnoc_hd l in
    let (ctl, vtl) = unsnoc_tl l in
    L.map_append get_data hd [(ctl, vtl)];
    L.map_append get_data hd [(ctl, { vcell_data = vtl.vcell_data; vcell_next = n })]

val create_queue (a: Type) : Steel (cllist_lvalue a & Ghost.erased (v a)) emp (fun x -> queue (fst x) (snd x))
  (requires (fun _ -> True))
  (ensures (fun _ res _ -> datas (snd res) == []))

let create_queue
  a
=
  let ll = alloc_cllist (ccell_ptrvalue_null _) null in
  let cl = fst ll in
  change_slprop (cllist (fst ll) full_perm (snd ll)) (pts_to (cllist_head cl) full_perm (snd ll).vllist_head `star` pts_to (cllist_tail cl) full_perm (snd ll).vllist_tail) (fun _ -> ());
  write (cllist_tail cl) (cllist_head cl);
  let wl = { vllist_head = ccell_ptrvalue_null _; vllist_tail = cllist_head cl } in
  let w = Ghost.hide ({
    vllist = wl;
    cells = [];
  }) in
  let res = (cl, w) in
  change_slprop
    emp
    (llist_fragment (cllist_head (fst res)) (Ghost.reveal (snd res)).vllist.vllist_head (Ghost.reveal (snd res)).cells)
    (fun _ -> ());
  pack_queue1 (fst res) (snd res) (cllist_tail cl) (cllist_head cl) (cllist_head cl) (snd ll).vllist_head;
  res

let emp_equiv_pure
  (p: prop)
: Lemma
  (requires p)
  (ensures (emp `equiv` pure p))
=
  Classical.forall_intro intro_emp;
  Classical.forall_intro (pure_interp p)

val enqueue
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
  (w: a)
: Steel (Ghost.erased (v a))
    (queue x l)
    (fun res -> queue x res)
    (requires (fun _ -> True))
    (ensures (fun _ res _ -> datas res == datas l `L.append` [w]))

#restart-solver

let enqueue
  #a x l w
=
  let cc = alloc_cell w (ccell_ptrvalue_null a) in
  let c = fst cc in
  let vc = snd cc in
  change_slprop (ccell (fst cc) full_perm (snd cc))
    (pts_to (ccell_data c) full_perm w `star` pts_to (ccell_next c) full_perm (ccell_ptrvalue_null a))
    (fun _ -> ());
  unpack_queue x l;
  let tail = read (cllist_tail x) in
  change_slprop
    (pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    (pts_to tail full_perm (ccell_ptrvalue_null _))
    (fun _ -> ());
  write tail c;
  write (cllist_tail x) (ccell_next c);
  let res = Ghost.hide ({
    vllist = {
      vllist_head =
        begin match l.cells with
        | [] -> c
        | _ -> l.vllist.vllist_head
        end;
      vllist_tail = ccell_next c;
    };
    cells = update_next_last l.cells c `L.append` [(c, Ghost.reveal vc)]
  }) in
  L.map_append get_data (update_next_last l.cells c) [(c, Ghost.reveal vc)];
  get_data_update_next_last l.cells c;
  L.lemma_append_last (update_next_last l.cells c) [(c, Ghost.reveal vc)];
  next_last_correct l.vllist.vllist_tail l.vllist.vllist_head res.cells;
  change_equal_slprop
    (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to tail full_perm c `star`
      pts_to (ccell_data c) full_perm w)
    (llist_fragment (cllist_head x) res.vllist.vllist_head res.cells)
    (fun _ ->
      llist_fragment_update_next_last (cllist_head x) l.vllist.vllist_head l.cells c;
      match Ghost.reveal l.cells with
      | [] ->
        assert (
          (emp `star` pts_to tail full_perm c `star` pts_to (ccell_data c) full_perm w) `equiv`
          (pts_to tail full_perm c `star` pts_to (ccell_data c) full_perm w `star` emp `star` emp)
        ) by canon ();
        emp_equiv_pure (c == res.vllist.vllist_head)
      | _ ->
        next_last_update_next_last (cllist_head x) l.vllist.vllist_head l.cells c;
        emp_equiv_pure (c == (c <: ccell_ptrvalue a));
        llist_fragment_append (cllist_head x) l.vllist.vllist_head (update_next_last l.cells c) [(c, Ghost.reveal vc)];
        assert ((
          llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
          pts_to tail full_perm c `star`
          pts_to (ccell_data c) full_perm w
        ) `equiv` (
          llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
            (pts_to tail full_perm c `star`
              pts_to (ccell_data c) full_perm w `star`
              emp `star`
              emp
            )
        )) by canon ()
    );
  pack_queue1 x res (cllist_tail x) (ccell_next c) (ccell_next c) (ccell_ptrvalue_null a);
  res

let pure_star_equiv
  (p: slprop)
  (q: prop)
: Lemma
  (forall m . interp (p `star` pure q) m <==> interp p m /\ q)
=
  emp_unit p;
  Classical.forall_intro (fun m ->
    pure_star_interp p q m
  )

let pure_star_accumulate_r
  (p: slprop)
  (q1 q2: prop)
: Lemma
  (((p `star` pure q1) `star` pure q2) `equiv` (p `star` pure (q1 /\ q2)))
= pure_star_equiv (p `star` pure q1) q2;
  pure_star_equiv p q1;
  pure_star_equiv p (q1 /\ q2)

let pure_rewrite
  (p1 p2: slprop)
  (q: prop)
: Lemma
  (requires (q ==> (p1 `equiv` p2)))
  (ensures ((p1 `star` pure q) `equiv` (p2 `star` pure q)))
= pure_star_equiv p1 q;
  pure_star_equiv p2 q

let pure_rewrite_intro
  (p1 p2: slprop)
  (q: prop)
  (lem: unit -> Lemma (requires q) (ensures (p1 `equiv` p2)))
: Lemma
  (ensures ((p1 `star` pure q) `equiv` (p2 `star` pure q)))
=
  Classical.move_requires lem ();
  pure_rewrite p1 p2 q

let rec llist_fragment'
  (#a: Type)
  (p: ccell_ptrvalue a)
  (l: Ghost.erased (list (ccell_lvalue a & vcell a)))
: Tot slprop
  (decreases (Ghost.reveal l))
= match Ghost.reveal l with
  | [] -> emp
  | (pc, vc) :: q ->
    ccell pc full_perm vc `star` llist_fragment' vc.vcell_next q `star` pure (pc == p)

let queue_prop'
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Tot prop
= ccell_ptrvalue_is_null l.vllist.vllist_head == Nil? l.cells /\
  begin match l.cells with
  | [] -> l.vllist.vllist_tail == cllist_head x
  | _ -> l.vllist.vllist_tail == ccell_next (fst (L.last l.cells)) /\ ccell_ptrvalue_is_null (snd (L.last l.cells)).vcell_next
  end

let queue'
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Tot slprop
=
  cllist x full_perm l.vllist `star`
  llist_fragment' l.vllist.vllist_head l.cells `star`
  pure (queue_prop' x l)

let queue_prop0
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Tot prop
= ccell_ptrvalue_is_null l.vllist.vllist_head == Nil? l.cells /\
  fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
  ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true

let queue_prop0_equiv
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Lemma
  (queue_prop0 x l <==> queue_prop' x l)
= match l.cells with
  | [] -> ()
  | _ -> next_last_correct (cllist_head x) l.vllist.vllist_head l.cells

let pure_and_equiv
  (p q: prop)
: Lemma
  ((pure p `star` pure q) `equiv` pure (p /\ q))
=
  assert ((pure p `star` pure q) `equiv` (emp `star` pure p `star` pure q)) by canon ();
  assert (pure (p /\ q) `equiv` (emp `star` pure (p /\ q))) by canon ();
  pure_star_accumulate_r emp p q

let pure_dup
  (p q: prop)
: Lemma
  (pure p `equiv` (pure p `star` pure p))
=
  pure_equiv p (p /\ p);
  pure_and_equiv p p

let queue_equiv_1
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Lemma
  (queue x l `equiv` (
    pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
    llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
    pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
    pure (queue_prop0 x l)
  ))
=
  match l.cells with
  | [] ->
    pure_equiv (queue_prop x l) (queue_prop0 x l)
  | (chd, vhd) :: tl ->
    pure_equiv (chd == l.vllist.vllist_head) (chd == l.vllist.vllist_head /\ ccell_ptrvalue_is_null l.vllist.vllist_head == false);
    pure_and_equiv (chd == l.vllist.vllist_head) (ccell_ptrvalue_is_null l.vllist.vllist_head == false);
    assert (( (* necessary, otherwise queue x l cannot be proven equiv to the lhs of the equiv below *)
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells
    ) == (
        pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next (Ghost.hide tl) `star`
        pure (chd == l.vllist.vllist_head)
    ));
    assert ((
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (
        pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
        (pure (chd == l.vllist.vllist_head) `star` pure (ccell_ptrvalue_is_null l.vllist.vllist_head == false))
      ) `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      pure (queue_prop x l)
    ) `equiv` (
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (
        pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
        pure (chd == l.vllist.vllist_head)
      ) `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      (
        pure (queue_prop x l) `star`
        pure (ccell_ptrvalue_is_null l.vllist.vllist_head == false)
      )
    )) by canon ();
    pure_and_equiv (queue_prop x l) (ccell_ptrvalue_is_null l.vllist.vllist_head == false);
    pure_equiv (queue_prop0 x l) (queue_prop x l /\ ccell_ptrvalue_is_null l.vllist.vllist_head == false)

let rec llist_fragment_equiv
  (#a: Type)
  (phd: ref (ccell_ptrvalue a))
  (hd: ccell_ptrvalue a)
  (l: list (ccell_lvalue a & vcell a))
: Lemma
  (requires True)
  (ensures ((
    llist_fragment phd hd l `star`
    pts_to (fst (next_last phd hd l)) full_perm (snd (next_last phd hd l))
  ) `equiv` (
    pts_to phd full_perm hd `star`
    llist_fragment' hd l
  )))
  (decreases l)
= match l with
  | [] ->
    assert (
      (emp `star` pts_to phd full_perm hd) `equiv`
      (pts_to phd full_perm hd `star` emp)
    ) by canon ()
  | (chd, vhd) :: tl ->
    assert ((
      pts_to phd full_perm hd `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
      llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
      pure (chd == hd) `star`
      pts_to (fst (next_last phd hd l)) full_perm (snd (next_last phd hd l))
    ) `equiv` (
      pts_to phd full_perm hd `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        (llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
          pts_to (fst (next_last phd hd l)) full_perm (snd (next_last phd hd l))) `star`
      pure (chd == hd)
    )) by canon ();
    llist_fragment_equiv (ccell_next chd) vhd.vcell_next tl;
    assert ((
      pts_to phd full_perm hd `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        (pts_to (ccell_next chd) full_perm vhd.vcell_next `star`
          llist_fragment' vhd.vcell_next tl) `star`
      pure (chd == hd)
    ) `equiv` (
      pts_to phd full_perm hd `star`
      (pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        pts_to (ccell_next chd) full_perm vhd.vcell_next `star`
        llist_fragment' vhd.vcell_next tl `star`
        pure (chd == hd))
    )) by canon ()

let queue_equiv_2
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Lemma
  (requires (
    queue_prop0 x l
  ))
  (ensures ((
    pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
    llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
    pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _)
  ) `equiv` (
    cllist x full_perm l.vllist `star`
    llist_fragment' l.vllist.vllist_head l.cells
  )))
=
    assert ((
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _)
    ) `equiv` (
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
        pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    )) by canon ();
    llist_fragment_equiv (cllist_head x) l.vllist.vllist_head l.cells;
    assert ((
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        llist_fragment' l.vllist.vllist_head l.cells)
    ) `equiv` (
      pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment' l.vllist.vllist_head l.cells
    )) by canon ()

let queue_equiv
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Lemma
  (queue x l `equiv` queue' x l)
=
  pure_rewrite_intro
    (
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _)
    )
    (
      cllist x full_perm l.vllist `star`
      llist_fragment' l.vllist.vllist_head l.cells
    )
    (queue_prop0 x l)
    (fun _ -> queue_equiv_2 x l);
  queue_equiv_1 x l;
  queue_prop0_equiv x l;
  pure_equiv (queue_prop0 x l) (queue_prop' x l)

let peek_pure
  (#uses:_) (p:prop)
  : SteelAtomicT (_:unit{p}) uses unobservable
                (pure p)
                (fun _ -> pure p)
=
  let q = elim_pure p in
  intro_pure p;
  q

let read_no_change (#a:Type) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : Steel a (pts_to r p v) (fun _ -> pts_to r p v)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == Ghost.reveal v)
=
  let v' = read r in
  change_equal_slprop _ (pts_to r p v) (fun _ -> ());
  v'

let queue_is_empty
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Steel bool
    (queue x l)
    (fun _ -> queue x l)
    (requires (fun _ -> True))
    (ensures (fun _ res _ ->
      res == Nil? (datas l)
    ))
=
  change_equiv_slprop
    (queue x l)
    (
      pts_to (cllist_head x) full_perm l.vllist.vllist_head `star` pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment' l.vllist.vllist_head l.cells `star`
      pure (queue_prop' x l)
    )
    (fun _ -> queue_equiv x l);
  peek_pure (queue_prop' x l);
  let hd = read (cllist_head x) in
  change_equiv_slprop
    (
        pts_to (cllist_head x) full_perm hd `star` pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
        llist_fragment' l.vllist.vllist_head l.cells `star`
        pure (queue_prop' x l)
    )
    (queue x l)
    (fun _ -> queue_equiv x l);
  ccell_ptrvalue_is_null hd

val dequeue
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Steel (a & Ghost.erased (v a))
    (queue x l)
    (fun res -> queue x (snd res))
    (requires (fun _ -> Cons? (datas l) == true))
    (ensures (fun _ res _ -> datas l == fst res :: datas (snd res)))

let dequeue
  #a x l
=
  let l0 : (l0: Ghost.erased (list (ccell_lvalue a & vcell a)) { Cons? l0 }) = l.cells in
  let chd : Ghost.erased (ccell_lvalue a) = Ghost.hide (fst (L.hd l0)) in
  let vhd : Ghost.erased (vcell a) = Ghost.hide (snd (L.hd l0)) in
  let tl : Ghost.erased (list (ccell_lvalue a & vcell a)) = Ghost.hide (L.tl l0) in
  change_equiv_slprop
    (queue x l)
    (
      cllist x full_perm l.vllist `star`
      (
        ccell chd full_perm vhd `star`
        llist_fragment' vhd.vcell_next tl `star`
        pure (Ghost.reveal chd == l.vllist.vllist_head)
      ) `star`
      pure (queue_prop' x l)
    )
    (fun _ -> queue_equiv x l);
  elim_pure (queue_prop' x l);
  elim_pure (Ghost.reveal chd == l.vllist.vllist_head);
  let chd' = read (cllist_head x) in
  assert (chd' == Ghost.reveal chd);
  let (chd' : ccell_lvalue a) = chd' in
  change_equal_slprop
    (ccell chd full_perm vhd)
    (pts_to (ccell_data chd') full_perm vhd.vcell_data `star` pts_to (ccell_next chd') full_perm vhd.vcell_next)
    (fun _ -> ());
  let chd_data = read (ccell_data chd') in
  let chd_next = read (ccell_next chd') in
  change_equal_slprop
    (pts_to (ccell_data chd') full_perm chd_data `star` pts_to (ccell_next chd') full_perm chd_next)
    (ccell chd' full_perm vhd)
    (fun _ -> ());
  free_cell chd' _;
  write (cllist_head x) chd_next;
  if ccell_ptrvalue_is_null chd_next
  then begin
    change_equiv_slprop
      (llist_fragment' vhd.vcell_next tl)
      (llist_fragment' vhd.vcell_next tl `star` pure (Nil? tl == true))
      (fun _ ->
        match Ghost.reveal tl with
        | [] ->
          assert (llist_fragment' vhd.vcell_next tl `equiv` (llist_fragment' vhd.vcell_next tl `star` emp)) by canon ();
          emp_equiv_pure (Nil? tl == true)
        | (chd2, vhd2) :: tl2 ->
          pure_equiv (chd2 == vhd.vcell_next) (chd2 == vhd.vcell_next /\ Nil? tl == true); // because that equality contradicts ccell_ptrvalue_is_null chd_next
          pure_and_equiv (chd2 == vhd.vcell_next) (Nil? tl == true);
          assert ((
            ccell chd2 full_perm vhd2 `star` llist_fragment' vhd2.vcell_next tl2 `star` (pure (chd2 == vhd.vcell_next) `star` pure (Nil? tl == true))
          ) `equiv` (
            (ccell chd2 full_perm vhd2 `star` llist_fragment' vhd2.vcell_next tl2 `star` pure (chd2 == vhd.vcell_next)) `star` pure (Nil? tl == true)
          )) by canon ()
      );
    elim_pure (Nil? tl == true);
    write (cllist_tail x) (cllist_head x);
    let l' : Ghost.erased (v a) = Ghost.hide ({
      vllist = ({ vllist_head = chd_next; vllist_tail = cllist_head x });
      cells = []
    })
    in
    let res = (chd_data, l') in
    intro_pure (queue_prop' x l');
    change_equiv_slprop
      (
        pts_to (cllist_head x) full_perm chd_next `star`
        pts_to (cllist_tail x) full_perm (cllist_head x) `star`
        llist_fragment' vhd.vcell_next tl `star`
        pure (queue_prop' x l')
      )
      (queue x (snd res))
      (fun _ ->
        queue_equiv x (snd res)
      );
    res
  end else begin
    let l' : Ghost.erased (v a) = Ghost.hide ({
      vllist = ({ vllist_head = chd_next; vllist_tail = l.vllist.vllist_tail });
      cells = Ghost.reveal tl;
    })
    in
    let res = (chd_data, l') in
    intro_pure (queue_prop' x l');
    change_equiv_slprop
      (
        pts_to (cllist_head x) full_perm chd_next `star`
        pts_to (cllist_tail x) full_perm _ `star`
        llist_fragment' vhd.vcell_next tl `star`
        pure (queue_prop' x l')
      )
      (queue x (snd res))
      (fun _ -> queue_equiv x (snd res));
    res
  end
