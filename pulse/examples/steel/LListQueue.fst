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

let queue (#a: Type) (x: cllist_lvalue a) (l: Ghost.erased (v a)) : Tot slprop =
  pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
  llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
  pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
  pure (fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail) `star`
  pure (ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true)

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
      pure (fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail) `star`
      pure (ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true))
    (fun _ -> ());
  elim_pure (fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail);
  elim_pure (ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true)

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
= intro_pure (fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail);
  intro_pure (ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true);
  change_slprop
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      llist_fragment (cllist_head x) l.vllist.vllist_head l.cells `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      pure (fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail) `star`
      pure (ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true))
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

let pack_queue2
  (#a: Type)
  (x: cllist_lvalue a) (l: Ghost.erased (v a))
  (s1: slprop)
  (s2: slprop)
  (s3: slprop)
: Steel unit
    (s1 `star` s2 `star` s3)
    (fun _ -> queue x l)
    (requires (fun _ ->
      s1 == pts_to (cllist_tail x) full_perm l.vllist.vllist_tail /\
      s2 == llist_fragment (cllist_head x) l.vllist.vllist_head l.cells /\
      s3 == pts_to (l.vllist.vllist_tail) full_perm (ccell_ptrvalue_null a) /\
      fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail /\
      ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true
    ))
    (ensures (fun _ _ _ -> True))
=
  change_equal_slprop
    s1
    (pts_to (cllist_tail x) full_perm l.vllist.vllist_tail)
    (fun _ -> ());
  change_equal_slprop
    s2
    (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells)
    (fun _ -> ());
  change_equal_slprop
    s3
    (pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _))
    (fun _ -> ());
  pack_queue x l

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
  (requires (q ==> p1 == p2))
  (ensures ((p1 `star` pure q) `equiv` (p2 `star` pure q)))
= pure_star_equiv p1 q;
  pure_star_equiv p2 q

noeq
type token
  (a: Type)
= {
  token_value: a;
  token_slprop: slprop;
  token_prop: prop
}

val read_with_token
  (#a: Type)
  (p: slprop)
  (r: ref a)
  (token: Ghost.erased (token a))
: Steel a
    p
    (fun _ -> p)
    (requires (fun _ -> p `equiv` (pts_to r full_perm token.token_value `star` token.token_slprop `star` pure token.token_prop)))
    (ensures (fun _ res _ ->
      res == token.token_value /\
      token.token_prop
    ))

let read_with_token
  #a p r token
=
  change_equiv_slprop p (pts_to r full_perm token.token_value `star` token.token_slprop `star` pure token.token_prop) (fun _ -> ());
  let res = read r in
  let sq : squash (token.token_prop) = elim_pure token.token_prop in
  intro_pure token.token_prop;
  change_equiv_slprop (pts_to r full_perm res `star` token.token_slprop `star` pure token.token_prop) p (fun _ -> ());
  res

[@"opaque_to_smt"]
irreducible
val queue_cons_ccell_next
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Pure (Ghost.erased (token (ccell_ptrvalue a)))
  (requires (Cons? l.cells))
  (ensures (fun y ->
    match l.cells with
    | [] -> False
    | ((chd, vhd) :: q) ->
      y.token_value == vhd.vcell_next /\
      queue x l `equiv` (pts_to (ccell_next chd) full_perm y.token_value `star` y.token_slprop `star` pure y.token_prop) /\
      (y.token_prop ==> ccell_ptrvalue_is_null y.token_value == Nil? q)
  ))

let queue_cons_ccell_next
  #a x l
=
  let p1 : prop = ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true in
  let p2 : prop = fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail in
  let (chd, vhd) :: tl = l.cells in
  let pz : slprop = pts_to (ccell_next chd) full_perm vhd.vcell_next in
  let p3 : prop = chd == l.vllist.vllist_head in
  let rv = vhd.vcell_next in
  match tl with
  | [] ->
    let p0 = pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) in
    let r1 = 
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
      llist_fragment (ccell_next chd) vhd.vcell_next tl
    in
    let z = p0 `star` r1 `star` pure p3 `star` pure p2 `star` pure p1 in
    let z0 = 
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (
        pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
        pure p3
      ) `star`
      p0 `star` pure p2 `star` pure p1
    in
    assert (queue x l == z0);
    assert (z0 `equiv` z) by canon ();
    pure_star_accumulate_r (p0 `star` r1 `star` pure p3) p2 p1;
    pure_star_accumulate_r (p0 `star` r1) p3 (p2 /\ p1);
    pure_rewrite (p0 `star` r1) (pz `star` r1) (p3 /\ (p2 /\ p1));
    {token_value = rv; token_slprop = r1; token_prop = (p3 /\ (p2 /\ p1)) }
  | (chd', vhd') :: tl' ->
    let z0 = 
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      (
        pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
        pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
        (
          pts_to (ccell_next chd) full_perm vhd.vcell_next `star`
          pts_to (ccell_data chd') full_perm vhd'.vcell_data `star`
          llist_fragment (ccell_next chd') vhd'.vcell_next tl' `star`
          pure (chd' == vhd.vcell_next)
        ) `star`
        pure p3
      ) `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star` pure p2 `star` pure p1
    in
    assert (queue x l == z0);
    let res =
      pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
      pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
      pts_to (ccell_data chd') full_perm vhd'.vcell_data `star`
      llist_fragment (ccell_next chd') vhd'.vcell_next tl' `star`
      pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
      pure p3 `star`
      pure p2 `star`
      pure p1
    in
    assert (z0 `equiv` (pz `star` res `star` pure (chd' == vhd.vcell_next))) by canon ();
    {token_value = rv; token_slprop = res; token_prop = (chd' == vhd.vcell_next)}

[@"opaque_to_smt"]
irreducible
val queue_cons_ccell_data
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Pure (Ghost.erased (token a))
  (requires (Cons? l.cells))
  (ensures (fun y ->
    match l.cells with
    | [] -> False
    | ((chd, vhd) :: _) ->
      y.token_value == vhd.vcell_data /\
      queue x l `equiv` (pts_to (ccell_data chd) full_perm y.token_value `star` y.token_slprop `star` pure y.token_prop)
  ))

let queue_cons_ccell_data
  #a x l
=
  let ((chd, vhd) :: tl) = l.cells in
  let rv = vhd.vcell_data in
  let z0 =
    pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
    (
      pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
      pts_to (ccell_data chd) full_perm vhd.vcell_data `star`
      llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
      pure (chd == l.vllist.vllist_head)
    ) `star`
    pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
    pure (fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail) `star`
    pure (ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true)
  in
  assert (queue x l == z0);
  let pr = (ccell_ptrvalue_is_null (snd (next_last (cllist_head x) l.vllist.vllist_head l.cells)) == true) in
  let res =
    pts_to (cllist_tail x) full_perm l.vllist.vllist_tail `star`
    pts_to (cllist_head x) full_perm l.vllist.vllist_head `star`
    llist_fragment (ccell_next chd) vhd.vcell_next tl `star`
    pure (chd == l.vllist.vllist_head) `star`
    pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _) `star`
    pure (fst (next_last (cllist_head x) l.vllist.vllist_head l.cells) == l.vllist.vllist_tail)
  in
  assert (z0 `equiv` (pts_to (ccell_data chd) full_perm vhd.vcell_data `star` res `star` pure pr)) by canon ();
  { token_value = rv; token_slprop = res; token_prop = pr }

assume
val queue_cllist_head
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Pure (Ghost.erased (token (ccell_ptrvalue a)))
  (requires True)
  (ensures (fun y ->
    y.token_value == l.vllist.vllist_head /\
    queue x l `equiv` (pts_to (cllist_head x) full_perm y.token_value `star` y.token_slprop `star` pure y.token_prop) /\
    begin y.token_prop ==> y.token_value == begin match l.cells with
    | [] -> ccell_ptrvalue_null _
    | (chd, _) :: _ -> chd
    end end
  ))

val dequeue
  (#a: Type)
  (x: cllist_lvalue a)
  (l: Ghost.erased (v a))
: Steel unit // (a & Ghost.erased (v a))
    (queue x l)
    (fun res -> emp) // queue x (snd res))
    (requires (fun _ -> Cons? (datas l) == true))
    (ensures (fun _ res _ -> True)) // datas l == fst res :: datas (snd res)))

let dequeue
  #a x l
= (* read *)
  let qhd = queue_cllist_head x l in
  let chd' = read_with_token (queue x l) (cllist_head x) qhd in
  let chd' : ccell_lvalue a = chd' in
  let qd = queue_cons_ccell_data x l in
  let d = read_with_token (queue x l) (ccell_data chd') qd in
  let qn = queue_cons_ccell_next x l in
  let n = read_with_token (queue x l) (ccell_next chd') qn in
  (* write *)
  let vhd : Ghost.erased (vcell a) = Ghost.hide (snd (L.hd l.cells)) in
  let tl : Ghost.erased (list (ccell_lvalue a & vcell a)) = Ghost.hide (L.tl l.cells) in
  unpack_queue x l;
  change_equal_slprop
    (llist_fragment (cllist_head x) l.vllist.vllist_head l.cells)
    (pts_to (cllist_head x) full_perm chd' `star`
       pts_to (ccell_data chd') full_perm vhd.vcell_data `star`
       llist_fragment (ccell_next chd') vhd.vcell_next tl `star`
       pure (chd' == l.vllist.vllist_head))
    (fun _ -> ());
  write (cllist_head x) n;
  drop (pts_to (ccell_data chd') full_perm vhd.vcell_data);
  elim_pure (chd' == l.vllist.vllist_head);
  assert (vhd.vcell_next == n);
  if ccell_ptrvalue_is_null n
  then begin
    (* remaining list is empty *)
    noop ();
    change_slprop _ emp (fun m -> intro_emp m);
    ()
  end else begin
    let l' : Ghost.erased (v a) = Ghost.hide ({
      vllist = { vllist_head = n; vllist_tail = l.vllist.vllist_tail };
      cells = Ghost.reveal tl;
    }) in
//    assert (llist_fragment (ccell_next chd') vhd.vcell_next tl == llist_fragment 
    assume False;
    pack_queue2 x l'
      (pts_to (cllist_tail x) full_perm (Ghost.hide (l.vllist.vllist_tail)))
      (llist_fragment (ccell_next chd') vhd.vcell_next tl)
      (pts_to l.vllist.vllist_tail full_perm (ccell_ptrvalue_null _));
    change_slprop _ emp (fun m -> intro_emp m);
    ()
  end

(*

 assert (Cons? (Ghost.reveal l).cells);
  let lc : (lc: Ghost.erased (list (ccell_lvalue a & vcell a)) { Cons? (Ghost.reveal lc) }) = Ghost.hide (Ghost.reveal l).cells in
  let chd : Ghost.erased (ccell_lvalue a) = Ghost.hide (fst (L.hd (Ghost.reveal lc))) in
  let vhd : Ghost.erased (vcell a) = Ghost.hide (snd (L.hd (Ghost.reveal lc))) in
  let tl = Ghost.hide (L.tl (Ghost.reveal lc)) in 



(* BEGIN helpers to unfold definitions just to prove that I can read the head pointer of a list and check its value to determine whether the list is empty or not *)

[@"opaque_to_smt"]
let read_head_nil
  (#a: Type) (x: t a) (l: Ghost.erased (list (vcell a)))
: Ghost slprop
  (requires (Nil? l))
  (ensures (fun q -> queue x l `equiv` (ccellp x.head full_perm None `star` q)))
= assert (
    (llist_fragment x.head l `star` ccellp (next_last x.head l) full_perm None `star` pure (x.tail == Ghost.reveal (next_last x.head l))) `equiv`
    (ccellp (next_last x.head l) full_perm None `star` (llist_fragment x.head l `star` pure (x.tail == Ghost.reveal (next_last x.head l))))
  ) by canon ();
  (llist_fragment x.head l `star` pure (x.tail == Ghost.reveal (next_last x.head l)))

[@"opaque_to_smt"]
let read_head_snoc
  (#a: Type) (x: t a) (l: Ghost.erased (list (vcell a)))
: Ghost (slprop)
  (requires (Cons? l))
  (ensures (fun q -> queue x l `equiv` (ccellp x.head full_perm (Some (L.hd l)) `star` q)))
=
  let hd = L.hd l in
  let tl = L.tl l in
  assert (
    ((ccellp x.head full_perm (Some hd) `star` llist_fragment hd.vcell_next tl) `star` ccellp (next_last x.head l) full_perm None `star` pure (x.tail == Ghost.reveal (next_last x.head l))) `equiv`
    (ccellp x.head full_perm (Some hd) `star` ((llist_fragment hd.vcell_next tl `star` ccellp (next_last x.head l) full_perm None) `star` pure (x.tail == Ghost.reveal (next_last x.head l))))
  ) by canon ();
  (llist_fragment hd.vcell_next tl `star` ccellp (next_last x.head l) full_perm None) `star` pure (x.tail == Ghost.reveal (next_last x.head l))

let read_head_ghost
  (#a: Type) (x: t a) (l: Ghost.erased (list (vcell a)))
: Ghost (option (vcell a) & slprop)
  (requires True)
  (ensures (fun (v, q) -> queue x l `equiv` (ccellp x.head full_perm v `star` q) /\ 
    v == begin match Ghost.reveal l with 
    | [] -> None
    | a :: _ -> Some a
    end
  ))
=
  if Nil? l
  then (None, read_head_nil x l)
  else (Some (L.hd l), read_head_snoc x l)

let gfst
  (#a #b: Type)
  (x: Ghost.erased (a & b))
: Pure (Ghost.erased a)
  (requires (True))
  (ensures (fun y -> Ghost.reveal y == fst (Ghost.reveal x)))
= fst x

let gsnd
  (#a #b: Type)
  (x: Ghost.erased (a & b))
: Pure (Ghost.erased b)
  (requires (True))
  (ensures (fun y -> Ghost.reveal y == snd (Ghost.reveal x)))
= snd x

[@"opaque_to_smt"]
let read_head_pure
  (#a: Type) (x: t a) (l: Ghost.erased (list (vcell a)))
: Pure (Ghost.erased (option (vcell a)) & slprop)
  (requires True)
  (ensures (fun (v, q) -> queue x l `equiv` (ccellp x.head full_perm v `star` q) /\ 
    Ghost.reveal v == begin match Ghost.reveal l with 
    | [] -> None
    | a :: _ -> Some a
    end
  ))
= 
  let vq = Ghost.elift1 (fun () -> read_head_ghost x l) () in
  (gfst vq, Ghost.reveal (gsnd vq))

let is_empty
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list (vcell a)))
: Steel bool
  (queue x l)
  (fun _ -> queue x l)
  (requires (fun _ -> True))
  (ensures (fun _ v _ ->
    v == Nil? (Ghost.reveal l)
  ))
=
  let q : Ghost.erased (option (vcell a)) & slprop = read_head_pure x l in
  change_equiv_slprop (queue x l) (ccellp x.head full_perm (fst q) `star` snd q) ();
  let r = ccell_ptrvalue_is_null x.head in
  ccellp_is_null x.head full_perm (fst q);
  change_equiv_slprop (ccellp x.head full_perm (fst q) `star` snd q)  (queue x l) ();
  r

(* END helpers to unfold definitions just to prove that I can read the head pointer of a list and check its value to determine whether the list is empty or not *)

noeq
type dequeue_result (a: Type0) = {
  dq_val: a;
  dq_rem: t a;
  dq_rem_g: Ghost.erased (list (vcell a));
}

val dequeue
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list (vcell a)))
: Steel (dequeue_result a)
    (queue x l)
    (fun res -> queue (res.dq_rem) (res.dq_rem_g))
    (requires (fun _ -> Cons? l == true))
    (ensures (fun _ res _ -> Cons? l /\ res.dq_val == Ghost.reveal (L.hd l).vcell_data /\ res.dq_rem_g == Ghost.hide (L.tl l) /\ res.dq_rem.tail == x.tail))

let dequeue
  #a x l
=
  let (l2: Ghost.erased (l: list (vcell a) { Cons? l })) = Ghost.hide (Ghost.reveal l) in // necessary otherwise refinement type checking fails
  change_equiv_slprop
    (llist_fragment x.head l)
    (ccellp x.head full_perm (Some (L.hd l2)) `star` llist_fragment (L.hd l2).vcell_next (L.tl l2))
    ();
  ccellp_is_null x.head full_perm (Some (L.hd l2));
  let hd : ccell_lvalue a = x.head in
  let pval_hd = ccell_data hd in
  let pnext_hd = ccell_next hd in
  change_equiv_slprop
    (ccellp x.head full_perm (Ghost.hide (Some (L.hd l2))))
    (pts_to pval_hd full_perm (Ghost.hide (L.hd l2).vcell_data) `star` pts_to pnext_hd full_perm (Ghost.hide (L.hd l2).vcell_next))
    ();
  let next_hd = read pnext_hd in
  let val_hd = read #a #full_perm #(Ghost.hide (L.hd l2).vcell_data) pval_hd in
  let x' = { head = next_hd ; tail = x.tail } in
  let res = { dq_val = val_hd; dq_rem = x' ; dq_rem_g = Ghost.hide (L.tl l2) } in
  drop (pts_to pval_hd full_perm val_hd);
  drop (pts_to pnext_hd full_perm next_hd);
  change_slprop
    (llist_fragment (L.hd l2).vcell_next (L.tl l2)
     `star` ccellp (next_last x.head l) full_perm None `star` pure (x.tail == Ghost.reveal (next_last x.head l)))
    (queue res.dq_rem res.dq_rem_g)
    (fun _ -> ());
  res

let test_read_head_dequeue
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list (vcell a)))
: Steel (t a & Ghost.erased (list (vcell a)))
    (queue x l)
    (fun res -> queue (fst res) (snd res))
    (requires (fun _ -> True))
    (ensures (fun _ res _ ->
      match Ghost.reveal l with
      | [] -> res == (x, l)
      | _ :: q -> Ghost.reveal (snd res) == q
    ))
=
  let r = is_empty x l in
  if r
  then begin
    noop (); // necessary, otherwise "effects PURE and SteelF cannot be composed"
    (x, l)
  end else
    let res = dequeue x l in
    (res.dq_rem, res.dq_rem_g)

let test
  ()
: SteelT unit
    emp
    (fun _ -> emp)
=
  let l = create_queue nat in
  let lk = enqueue l _ 1 in
  let lk = enqueue (fst lk) _ 2 in
  let Some c = read_head (fst lk) _ in
  let lk = dequeue (fst lk) _ (next c) in
  let lk = enqueue (fst lk) _ 3 in
  let Some c = read_head (fst lk) _ in
  let lk = dequeue (fst lk) _ (next c) in
  let Some c = read_head (fst lk) _ in
  let lk = dequeue (fst lk) _ (next c) in
  assert (snd lk == Ghost.hide []);
  assert (data c == 3);
  drop (queue (fst lk) _)
