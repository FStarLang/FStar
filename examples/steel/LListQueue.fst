module LListQueue
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
include LListQueue.Cell
module L = FStar.List.Tot

noeq
type t (a: Type0) = {
  head: ccell_ptrvalue a;
  tail: ccell_ptrvalue a;
}

let (==) (#a:_) (x y: a) : prop = x == y

let rec llist_fragment (#a:Type) (ptr: ccell_ptrvalue a)
                                 (l:Ghost.erased (list (vcell a)))
    : Tot slprop (decreases (Ghost.reveal l))
    =
    match Ghost.reveal l with
    | [] -> emp
    | hd :: tl ->
      ccellp ptr full_perm (Some hd) `star`
      llist_fragment hd.vcell_next tl

let llist_fragment_nil (#a: Type) (ptr: ccell_ptrvalue a) (l: Ghost.erased (list (vcell a))) : Lemma
  (requires (Nil? l))
  (ensures (llist_fragment ptr l == emp))
= ()

let llist_fragment_cons (#a: Type) (ptr: ccell_ptrvalue a) (l: Ghost.erased (list (vcell a))) : Lemma
  (requires (Cons? l))
  (ensures (llist_fragment ptr l == (ccellp ptr full_perm (Some (L.hd l)) `star` llist_fragment (L.hd l).vcell_next (L.tl l))))
= ()

inline_for_extraction noextract let canon () : FStar.Tactics.Tac unit =
  (Steel.Memory.Tactics.canon ())

let rec next_last
  (#a: Type)
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (vcell a)))
: Tot (Ghost.erased (ccell_ptrvalue a))
  (decreases (Ghost.reveal l))
=
  match Ghost.reveal l with
  | [] -> Ghost.hide ptr
  | a :: q -> next_last a.vcell_next q

let rec next_last_correct
  (#a: Type)
  (ptr: ccell_ptrvalue a)
  (l: Ghost.erased (list (vcell a)))
: Lemma
  (requires (Cons? l))
  (ensures (next_last ptr l == Ghost.hide (L.last l).vcell_next))
  (decreases (Ghost.reveal l))
= match Ghost.reveal l with
  | [_] -> ()
  | a :: q -> next_last_correct a.vcell_next (Ghost.hide q)

let rec llist_fragment_append
  (#a: Type)
  (ptr: ccell_ptrvalue a)
  (l1: Ghost.erased (list (vcell a)))
  (l2: Ghost.erased (list (vcell a)))
: Lemma
  (requires True)
  (ensures (((llist_fragment ptr l1 `star` llist_fragment (next_last ptr l1) l2)) `equiv` llist_fragment ptr (l1 `L.append` l2)))
  (decreases (Ghost.reveal l1))
= match Ghost.reveal l1 with
  | [] ->
    assert (
      (emp `star` llist_fragment ptr l2) `equiv` llist_fragment ptr l2
    ) by canon ()
  | hd :: tl ->
    assert (
      ((ccellp ptr full_perm (Some hd) `star` llist_fragment hd.vcell_next tl) `star` llist_fragment (next_last hd.vcell_next tl) l2) `equiv`
      (ccellp ptr full_perm (Some hd) `star` (llist_fragment hd.vcell_next tl `star` llist_fragment (next_last hd.vcell_next tl) l2))
    ) by (Steel.Memory.Tactics.canon ());
    llist_fragment_append hd.vcell_next tl l2;
    star_congruence
      (ccellp ptr full_perm (Some hd))
      (llist_fragment hd.vcell_next (tl) `star` llist_fragment (next_last hd.vcell_next tl) l2)
      (ccellp ptr full_perm (Some hd))
      (llist_fragment hd.vcell_next (tl `L.append` (l2)))

(* I wish I had this:

assume val a : slprop
assume val b : slprop
assume val f (_: unit) : Tot (squash (a `equiv` b))
assume val c : slprop
let _ : squash ((a `star` c) `equiv` (b `star` c)) =
  let q : squash (a `equiv` b) = f () in
  assert ((a `star` c) `equiv` (b `star` c)) by (canon ())

Cf. Coq's congruence tactic

*)

let snoc_inj (#a: Type) (hd1 hd2: list a) (tl1 tl2: a) : Lemma
  (requires (hd1 `L.append` [tl1] == hd2 `L.append` [tl2]))
  (ensures (hd1 == hd2 /\ tl1 == tl2))
  [SMTPat (hd1 `L.append` [tl1]); SMTPat (hd2 `L.append` [tl2])]
= L.lemma_snoc_unsnoc (hd1, tl1);
  L.lemma_snoc_unsnoc (hd2, tl2)

let snoc_is_not_nil
  (#a: Type)
  (hd: list a)
  (tl: a)
: Lemma
  (Nil? (hd `L.append` [tl]) == false)
= ()

let snoc_is_cons
  (#a: Type)
  (hd: list a)
  (tl: a)
: Lemma
  (Cons? (hd `L.append` [tl]) == true)
= ()

[@"opaque_to_smt"]
let unsnoc (#a: Type) (l: list a) : Pure (list a & a)
  (requires (Cons? l))
  (ensures (fun (hd, tl) -> l == hd `L.append` [tl]))
=
  L.lemma_unsnoc_snoc l;
  L.unsnoc l

let unsnoc_hd (#a: Type) (l: list a) : Pure (list a) (requires (Cons? l)) (ensures (fun _ -> True)) = fst (unsnoc l)
let unsnoc_tl (#a: Type) (l: list a) : Pure (a) (requires (Cons? l)) (ensures (fun _ -> True)) = snd (unsnoc l)

[@@__reduce__]
let queue (#a: Type) (x: t a) (l: Ghost.erased (list (vcell a))) : Tot slprop =
  llist_fragment x.head l `star` ccellp (next_last x.head l) full_perm None `star` pure (x.tail == Ghost.reveal (next_last x.head l))

let create_queue (a: Type) : SteelT (t a) emp (fun x -> queue x []) =
  let head : ccell_ptrvalue a = ccell_ptrvalue_null a in
  let x : t a = ({ head = head; tail = head; }) in
  ccellp_null_intro head full_perm;
  intro_pure (x.tail == Ghost.reveal (next_last x.head (Ghost.hide [])));
  change_slprop (emp `star` ccellp head full_perm None `star` pure (x.tail == Ghost.reveal (next_last x.head (Ghost.hide [])))) (queue x []) (fun _ -> ());
  x

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

let change_equiv_slprop
  (p q: slprop)
  (sq: squash (p `equiv` q))
: SteelT unit
    p
    (fun _ -> q)
=
  change_slprop p q (fun _ -> ())

#push-options "--ide_id_info_off"

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

(* TODO: No longer works because I can no longer overwrite the value pointed to by an "option cell pointer" with a whole cell.

val enqueue
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list (vcell a)))
  (v: a)
: Steel (t a & Ghost.erased (list (vcell a)))
    (queue x l)
    (fun res -> queue (fst res) (snd res))
    (requires (fun _ -> True))
    (ensures (fun _ res _ -> datas (snd res) == datas l `L.append` [v] /\ (fst res).head == x.head))

let enqueue
  #a x l v
=
  let cc = alloc_cell v (ccell_ptrvalue_null a) in
  let c = Ghost.hide ({ vcell_data = v; vcell_next = ccell_ptrvalue_null a }) in
  elim_pure (x.tail == Ghost.reveal (next_last x.head l));
  change_slprop (pts_to (next_last x.head l) full_perm None) (pts_to x.tail full_perm None) (fun _ -> ());
  write #(option (cell a)) #None x.tail (Some c); // FIXME: WHY WHY WHY do I need to explicitly provide the implicits?
  change_slprop (pts_to x.tail full_perm (Some c) `star` emp) (llist_fragment (next_last x.head l) [c]) (fun _ -> ());
  let l2 : Ghost.erased (list (cell a)) = Ghost.hide (l `L.append` [c]) in
  change_slprop (llist_fragment x.head l `star` llist_fragment (next_last x.head l) [c]) (llist_fragment x.head l2) (fun _ -> llist_fragment_append x.head l [c]);
  let y = { head = x.head; tail = n } in
  change_slprop (llist_fragment x.head l2) (llist_fragment y.head l2) (fun _ -> ());
  L.lemma_append_last l [c];
  next_last_correct y.head (l `L.append` [c]);
  intro_pure (y.tail == Ghost.reveal (next_last y.head l2));
  change_slprop (pts_to n full_perm None) (pts_to (next_last y.head l2) full_perm None) (fun _ -> ());
  L.map_append data l [c]; // must appear before the last change_slprop
  let res : t a & Ghost.erased (list (cell a)) = (y, l2) in
  change_slprop
    (llist_fragment y.head l2 `star` pts_to (next_last y.head l2) full_perm None `star` pure (y.tail == Ghost.reveal (next_last y.head l2)))
    (queue (fst res) (snd res))
    (fun _ -> ());
  // it seems that nothing must come before the last change_slprop and the return value
  res

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
