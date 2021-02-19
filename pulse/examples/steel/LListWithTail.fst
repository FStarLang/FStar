module LListWithTail
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
include LListWithTail.Cell
module L = FStar.List.Tot

noeq
type t (a: Type0) = {
  head: cellptr a;
  tail: cellptr a;
}

let (==) (#a:_) (x y: a) : prop = x == y

let rec llist_fragment (#a:Type) (ptr: cellptr a)
                                 (l:Ghost.erased (list (cell a)))
    : Tot slprop (decreases (Ghost.reveal l))
    =
    match Ghost.reveal l with
    | [] -> emp
    | hd :: tl ->
      pts_to ptr full_perm (Some hd) `star`
      llist_fragment (next hd) tl

let llist_fragment_nil (#a: Type) (ptr: cellptr a) (l: Ghost.erased (list (cell a))) : Lemma
  (requires (Nil? l))
  (ensures (llist_fragment ptr l == emp))
= ()

let llist_fragment_cons (#a: Type) (ptr: cellptr a) (l: Ghost.erased (list (cell a))) : Lemma
  (requires (Cons? l))
  (ensures (llist_fragment ptr l == (pts_to ptr full_perm (Some (L.hd l)) `star` llist_fragment (next (L.hd l)) (L.tl l))))
= ()

inline_for_extraction noextract let canon () : FStar.Tactics.Tac unit =
  (Steel.Memory.Tactics.canon ())

let rec next_last
  (#a: Type)
  (ptr: cellptr a)
  (l: Ghost.erased (list (cell a)))
: Tot (Ghost.erased (cellptr a))
  (decreases (Ghost.reveal l))
=
  match Ghost.reveal l with
  | [] -> Ghost.hide ptr
  | a :: q -> next_last (next a) q

let rec next_last_correct
  (#a: Type)
  (ptr: cellptr a)
  (l: Ghost.erased (list (cell a)))
: Lemma
  (requires (Cons? l))
  (ensures (next_last ptr l == Ghost.hide (next (L.last l))))
  (decreases (Ghost.reveal l))
= match Ghost.reveal l with
  | [_] -> ()
  | a :: q -> next_last_correct (next a) (Ghost.hide q)

let rec llist_fragment_append
  (#a: Type)
  (ptr: cellptr a)
  (l1: Ghost.erased (list (cell a)))
  (l2: Ghost.erased (list (cell a)))
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
      ((pts_to ptr full_perm (Some hd) `star` llist_fragment (next hd) tl) `star` llist_fragment (next_last (next hd) tl) l2) `equiv`
      (pts_to ptr full_perm (Some hd) `star` (llist_fragment (next hd) tl `star` llist_fragment (next_last (next hd) tl) l2))
    ) by (Steel.Memory.Tactics.canon ());
    llist_fragment_append (next hd) tl l2;
    star_congruence
      (pts_to ptr full_perm (Some hd))
      (llist_fragment (next hd) (tl) `star` llist_fragment (next_last (next hd) tl) l2)
      (pts_to ptr full_perm (Some hd))
      (llist_fragment (next hd) (tl `L.append` (l2)))

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

let llist_with_tail (#a: Type) (x: t a) (l: Ghost.erased (list (cell a))) : Tot slprop =
  llist_fragment x.head l `star` pts_to (next_last x.head l) full_perm None `star` pure (x.tail == Ghost.reveal (next_last x.head l))

let create_llist_with_tail (a: Type) : SteelT (t a) emp (fun x -> llist_with_tail x []) =
  let head : cellptr a = alloc None in
  let x : t a = ({ head = head; tail = head; }) in
  intro_pure (x.tail == Ghost.reveal (next_last x.head (Ghost.hide [])));
  change_slprop (emp `star` (* FIXME: WHY WHY WHY this emp? *) pts_to head full_perm None `star` pure (x.tail == Ghost.reveal (next_last x.head (Ghost.hide [])))) (llist_with_tail x []) (fun _ -> ());
  x

(* BEGIN helpers to unfold definitions just to prove that I can read the head pointer of a list and check its value to determine whether the list is empty or not *)

[@"opaque_to_smt"]
let read_head_nil
  (#a: Type) (x: t a) (l: Ghost.erased (list (cell a)))
: Ghost slprop
  (requires (Nil? l))
  (ensures (fun q -> llist_with_tail x l `equiv` (pts_to x.head full_perm None `star` q)))
= assert (
    (llist_fragment x.head l `star` pts_to (next_last x.head l) full_perm None `star` pure (x.tail == Ghost.reveal (next_last x.head l))) `equiv`
    (pts_to (next_last x.head l) full_perm None `star` (llist_fragment x.head l `star` pure (x.tail == Ghost.reveal (next_last x.head l))))
  ) by canon ();
  (llist_fragment x.head l `star` pure (x.tail == Ghost.reveal (next_last x.head l)))

[@"opaque_to_smt"]
let read_head_snoc
  (#a: Type) (x: t a) (l: Ghost.erased (list (cell a)))
: Ghost (slprop)
  (requires (Cons? l))
  (ensures (fun q -> llist_with_tail x l `equiv` (pts_to x.head full_perm (Some (L.hd l)) `star` q)))
=
  let hd = L.hd l in
  let tl = L.tl l in
  assert (
    ((pts_to x.head full_perm (Some hd) `star` llist_fragment (next hd) tl) `star` pts_to (next_last x.head l) full_perm None `star` pure (x.tail == Ghost.reveal (next_last x.head l))) `equiv`
    (pts_to x.head full_perm (Some hd) `star` ((llist_fragment (next hd) tl `star` pts_to (next_last x.head l) full_perm None) `star` pure (x.tail == Ghost.reveal (next_last x.head l))))
  ) by canon ();
  (llist_fragment (next hd) tl `star` pts_to (next_last x.head l) full_perm None) `star` pure (x.tail == Ghost.reveal (next_last x.head l))

let read_head_ghost
  (#a: Type) (x: t a) (l: Ghost.erased (list (cell a)))
: Ghost (option (cell a) & slprop)
  (requires True)
  (ensures (fun (v, q) -> llist_with_tail x l `equiv` (pts_to x.head full_perm v `star` q) /\ 
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
  (#a: Type) (x: t a) (l: Ghost.erased (list (cell a)))
: Pure (Ghost.erased (option (cell a)) & slprop)
  (requires True)
  (ensures (fun (v, q) -> llist_with_tail x l `equiv` (pts_to x.head full_perm v `star` q) /\ 
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

let read_head
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list (cell a)))
: Steel (option (cell a))
  (llist_with_tail x l)
  (fun _ -> llist_with_tail x l)
  (requires (fun _ -> True))
  (ensures (fun _ v _ ->
    Ghost.reveal v == begin match Ghost.reveal l with 
    | [] -> None
    | a :: _ -> Some a
    end
  ))
=
  let q : Ghost.erased (option (cell a)) & slprop = read_head_pure x l in
  change_equiv_slprop (llist_with_tail x l) (pts_to x.head full_perm (fst q) `star` snd q) ();
  let r = read #(option (cell a)) #full_perm #(fst q) x.head in
  change_equiv_slprop (pts_to x.head full_perm r `star` snd q)  (llist_with_tail x l) ();
  r

(* END helpers to unfold definitions just to prove that I can read the head pointer of a list and check its value to determine whether the list is empty or not *)

(*
val pop
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list (cell a)))
  (next_hd: cellptr a) (* assumed I received this pointer through read_head above *)
: Steel unit // (t a & Ghost.erased (list (cell a)))
    (llist_with_tail x l)
    (fun _ -> llist_with_tail x l)
//    (fun res -> llist_with_tail (fst res) (snd res))
    (requires (fun _ -> Cons? l /\ next_hd == next (L.hd l)))
//    (ensures (fun _ res _ -> Cons? l /\ snd res == Ghost.hide (L.tl l)))
    (ensures (fun _ _ _ -> True))

let pop
  #a x l next_hd
=
  noop ();
  change_equiv_slprop (llist_with_tail x l) (
    pts_to x.head full_perm (Some (L.hd l)) `star` ((llist_fragment (next (L.hd l)) (L.tl l) `star` pts_to (next_last x.head l) full_perm None) `star` pure (x.tail == Ghost.reveal (next_last x.head l)))
  ) ();
  change_equiv_slprop (
    pts_to x.head full_perm (Some (L.hd l)) `star` ((llist_fragment (next (L.hd l)) (L.tl l) `star` pts_to (next_last x.head l) full_perm None) `star` pure (x.tail == Ghost.reveal (next_last x.head l)))
  ) (llist_with_tail x l) ();
  ()

[@"opaque_to_smt"]
let llist_with_tail_read_next_head_snoc
  (#a: Type) (x: t a) (l: Ghost.erased (list (cell a)))
: Ghost (option (cell a) & slprop)
  (requires (Cons? l /\ Cons? (unsnoc_hd l)))
  (ensures (fun (v, q) -> llist_with_tail x l `equiv` (pts_to (next (L.hd l)) full_perm v `star` q) /\ v == Some (L.hd (L.tl l))))
= 
  let hd = unsnoc_hd l in
  let tl = unsnoc_tl l in
  let r = (pts_to (next_last x.head hd) full_perm (Some (Ghost.reveal tl)) `star` pts_to (next tl) full_perm None `star` pts_to x.tail full_perm (next_last x.head hd)) in
  let (v, q) = llist_fragment_read_head_cons (next (L.hd l)) (L.tl l) in
  star_congruence (pts_to x.head full_perm (Some (L.hd l))) (llist_fragment
  
  star_congruence (llist_fragment x.head hd) r (pts_to x.head full_perm v `star` q) r;
  assert (
    ((pts_to x.head full_perm v `star` q) `star` r)
    `equiv`
    (pts_to x.head full_perm v `star` (q `star` r))
  ) by (canon ());
  (Ghost.reveal v, (q `star` r))



(*
  slassert (llist_with_tail x l);
  change_equiv_slprop
    (llist_with_tail x l)
    (pts_to x.head full_perm (fst q) `star` snd q)
    ();
  let r = read #a #full_perm #(fst q) x.head in
  change_equiv_slprop
    (pts_to x.head full_perm (fst q) `star` snd q)
    (llist_with_tail x l)
    ();
  (r, snd q)



(*

let llist_with_tail_read
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list (cell a)))
: Steel (option (cell a) & slprop)
  (llist_with_tail x l)
  (fun q -> llist_with_tail x l) // pts_to x.head full_perm (fst q) `star` snd q)
  (requires (fun _ -> True))
  (ensures (fun _ q _ ->
    llist_with_tail x l `equiv` (pts_to x.head full_perm (fst q) `star` snd q) /\
    Cons? l == Some? (fst q)
  ))
=
  noop ();
  let q : Ghost.erased (option (cell a)) & slprop = llist_with_tail_read_2 x l in
  let q2 = snd q in
  noop ()

  slassert (llist_with_tail x l);
  change_equiv_slprop
    (llist_with_tail x l)
    (pts_to x.head full_perm (fst q) `star` snd q)
    ();
  let r = read #a #full_perm #(fst q) x.head in
  change_equiv_slprop
    (pts_to x.head full_perm (fst q) `star` snd q)
    (llist_with_tail x l)
    ();
  (r, snd q)





let rec llist_with_tail_fragment (#a: Type0) (x: t a) (hd: Ghost.erased (cell a)) (tl: Ghost.erased (list (cell a))) : Tot slprop (decreases (Ghost.reveal tl)) =
  pts_to x.head full_perm hd `star`
  begin match Ghost.reveal tl with
  | [] -> pure (x.tail == x.head)
  | a' :: q -> llist_with_tail_fragment ({ head = next hd; tail = x.tail }) a' q
  end

let llist_with_tail_fragment_aux (#a: Type0) (x: t a) (hd: Ghost.erased (cell a)) (tl: Ghost.erased (list (cell a))) : Tot slprop =
  match Ghost.reveal tl with
  | [] -> pure (x.tail == x.head)
  | a' :: q -> llist_with_tail_fragment ({ head = next hd; tail = x.tail }) a' q

let llist_with_tail_fragment_unfold
(#a: Type0) (x: t a) (hd: Ghost.erased (cell a)) (tl: Ghost.erased (list (cell a))) : Lemma
  (llist_with_tail_fragment x hd tl ==
  pts_to x.head full_perm hd `star` llist_with_tail_fragment_aux x hd tl
)
= ()

let llist_with_tail_fragment_nil
  (#a: Type0) (x: t a) (hd: Ghost.erased (cell a)) (tl: Ghost.erased (list (cell a)))
: Lemma
  (requires (Nil? tl))
  (ensures (llist_with_tail_fragment x hd tl == (pts_to x.head full_perm hd `star` pure (x.tail == x.head))))
=
  ()

let llist_with_tail_fragment_cons
  (#a: Type0) (x: t a) (hd: Ghost.erased (cell a)) (tl: Ghost.erased (list (cell a)))
: Lemma
  (requires (Cons? tl))
  (ensures (llist_with_tail_fragment x hd tl == (pts_to x.head full_perm hd `star` llist_with_tail_fragment ({ head = next hd; tail = x.tail }) (L.hd tl) (L.tl tl))))
=
  ()

let llist_with_tail_fragment_rev_aux (#a: Type0) (x: t a) (hd: Ghost.erased (list (cell a))) (tl: Ghost.erased (cell a)) : Tot slprop =
  match Ghost.reveal hd with
  | [] -> pure (x.tail == x.head)
  | a' :: q -> llist_with_tail_fragment_rev ({ head = next a'; tail = x.tail }) q tl

let llist_with_tail_fragment_rev_unfold
  (#a: Type0) (x: t a) (hd: Ghost.erased (list (cell a))) (tl: Ghost.erased (cell a))
: Lemma
  (llist_with_tail_fragment_rev x hd tl ==
  pts_to x.tail full_perm tl `star` llist_with_tail_fragment_rev_aux x hd tl)
= ()

let llist_with_tail_fragment_rev_nil (#a: Type0) (x: t a) (hd: Ghost.erased (list (cell a))) (tl: Ghost.erased (cell a)) : Lemma
  (requires (Nil? hd))
  (ensures (llist_with_tail_fragment_rev x hd tl == (pts_to x.tail full_perm tl `star` pure (x.tail == x.head))))
= ()

let llist_with_tail_fragment_rev_cons (#a: Type0) (x: t a) (hd: Ghost.erased (list (cell a))) (tl: Ghost.erased (cell a)) : Lemma
  (requires (Cons? hd))
  (ensures (llist_with_tail_fragment_rev x hd tl == (pts_to x.tail full_perm tl `star` llist_with_tail_fragment_rev ({ head = next (L.hd hd); tail = x.tail }) (L.tl hd) tl)))
= ()

let llist_with_tail (#a: Type0) (x: t a) (l: Ghost.erased (list (cell a))) : Tot slprop =
  match Ghost.reveal l with
  | [] -> pure (is_null x.head == true) `star` pure (is_null x.tail == true)
  | hd :: tl -> llist_with_tail_fragment x hd tl `star` pure (is_null (next (L.last l)) == true)

let llist_with_tail_nil
  (#a: Type)
  (x: t a)
  (l: Ghost.erased (list (cell a)))
: Lemma
  (requires (Nil? l))
  (ensures (llist_with_tail x l == pure (is_null x.head == true) `star` pure (is_null x.tail == true)))
= ()

let llist_with_tail_cons
  (#a: Type0) (x: t a) (l: Ghost.erased (list (cell a)))
: Lemma
  (requires (Cons? l))
  (ensures (llist_with_tail x l == llist_with_tail_fragment x (L.hd l) (L.tl l) `star` pure (is_null (next (L.last l)) == true)))
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
  (x: cell a)
  (m: mem)
: Lemma
  (requires (
    is_null (next x) == true /\ ptr.tail == ptr.head /\
    interp (pts_to ptr.head full_perm x) m
  ))
  (ensures (interp (llist_with_tail ptr [x]) m))

let intro_llist_cons_nil'
  a ptr x m
=
  norm_spec [delta; zeta] (llist_with_tail ptr [x]);
  pure_star_interp (llist_with_tail_fragment ptr x []) (is_null (next (L.last [x])) == true) m;
  norm_spec [delta; zeta] (llist_with_tail_fragment ptr x []);
  pure_star_interp (pts_to ptr.head full_perm x) (ptr.tail == ptr.head) m

let intro_llist_cons_nil
  (a: Type)
  (ptr: t a)
  (x: cell a)
: Steel unit
    (pts_to ptr.head full_perm x)
    (fun _ -> llist_with_tail ptr [x])
    (requires (fun _ -> is_null (next x) == true /\ ptr.tail == ptr.head))
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
    (t a & Ghost.erased (list (cell a)))
    (emp)
    (fun z -> llist_with_tail (fst z) (snd z))
    (requires (fun _ -> True))
    (ensures (fun _ z _ -> datas (snd z) == [x]))

#push-options "--ide_id_info_off"

let push_nil
  a e
=
  let x = mk_cell null e in
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
  (l: Ghost.erased (list (cell a)))
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
    pure_star_interp (llist_with_tail_fragment ptr (L.hd l) (L.tl l)) (is_null (next (L.last l)) == true) m;
    llist_with_tail_fragment_unfold ptr hd tl;
    elim_star (pts_to ptr.head full_perm hd) (llist_with_tail_fragment_aux ptr hd tl) m;
    pts_to_not_null ptr.head full_perm hd m

val llist_is_nil
  (a: Type)
  (ptr: t a)
  (l: Ghost.erased (list (cell a)))
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
  (x: cell a)
  (q: Ghost.erased (list (cell a)))
  (m: mem)
: Lemma
  (requires (interp
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x)
    m /\
    ptr0.head == next x /\ ptr0.tail == ptr.tail /\ Cons? q == true
  ))
  (ensures (interp
    (llist_with_tail ptr (x :: q))
  ) m)

let intro_llist_cons_cons'
  a ptr ptr0 x q m
=
  (* destruct the hypothesis *)
  llist_with_tail_cons ptr0 q;
  assert ((
    (llist_with_tail_fragment ptr0 (L.hd q) (L.tl q) `star` pure (is_null (next (L.last q)) == true)) `star` pts_to ptr.head full_perm x
    ) `equiv` (
    (pts_to ptr.head full_perm x `star` llist_with_tail_fragment ptr0 (L.hd q) (L.tl q)) `star` pure (is_null (next (L.last q)) == true)
  )) by (Steel.Memory.Tactics.canon ());
  pure_star_interp
    (pts_to ptr.head full_perm x `star` llist_with_tail_fragment ptr0 (L.hd q) (L.tl q))
    (is_null (next (L.last q)) == true)
    m;
  (* construct the conclusion *)
  assert (ptr0 == ({ head = next x; tail = ptr.tail }));
  assert (L.last (x :: q) == L.last q);
  llist_with_tail_fragment_cons ptr x q;
  pure_star_interp
    (llist_with_tail_fragment ptr x q)
    (is_null (next (L.last (x :: q))) == true)
    m;
  llist_with_tail_cons ptr (x :: q)

let intro_llist_cons_cons
  (a: Type)
  (ptr: t a)
  (ptr0 : t a)
  (x: cell a)
  (q: Ghost.erased (list (cell a)))
: Steel
    unit
    (llist_with_tail ptr0 q `star` pts_to ptr.head full_perm x)
    (fun _ -> llist_with_tail ptr (x :: q))
    (requires (fun _ -> ptr0.head == next x /\ ptr0.tail == ptr.tail /\ Cons? q == true))
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
  (q: Ghost.erased (list (cell a)))
: Steel
    (t a & Ghost.erased (list (cell a)))
    (llist_with_tail ptr q)
    (fun z -> llist_with_tail (fst z) (snd z))
    (requires (fun _ -> Cons? q == true))
    (ensures (fun _ z _ -> datas (snd z) == x :: datas q))

let push_cons
  a ptr0 e q
=
  let x = mk_cell ptr0.head e in
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
  (q: Ghost.erased (list (cell a)))
: Steel
    (t a & Ghost.erased (list (cell a)))
    (llist_with_tail ptr q)
    (fun z -> llist_with_tail (fst z) (snd z))
    (requires (fun _ -> True))
    (ensures (fun _ z _ -> datas (snd z) == x :: datas q))

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

val intro_llist_cons_snoc'
  (a: Type)
  (ptr: t a)
  (ptr0 : t a)
  (x: cell a)
  (q: Ghost.erased (list (cell a)))
  (m: mem)
: Lemma
  (requires (
    Cons? q == true /\
    interp
      (llist_with_tail ptr0 q `star` pts_to (next (L.last q)) full_perm x)
    m /\
    ptr0.head == ptr.head /\ ptr.tail == next (L.last q)
  ))
  (ensures (interp
    (llist_with_tail ptr (q `L.append` [x]))
  ) m)

let intro_llist_cons_snoc'
  a ptr ptr0 x q m
=
  (* destruct the hypothesis *)
  llist_with_tail_cons ptr0 q;
  assert ((
    (llist_with_tail_fragment ptr0 (L.hd q) (L.tl q) `star` pure (is_null (next (L.last q)) == true)) `star` pts_to ptr.head full_perm x
    ) `equiv` (
    (pts_to ptr.head full_perm x `star` llist_with_tail_fragment ptr0 (L.hd q) (L.tl q)) `star` pure (is_null (next (L.last q)) == true)
  )) by (Steel.Memory.Tactics.canon ());
  pure_star_interp
    (pts_to ptr.head full_perm x `star` llist_with_tail_fragment ptr0 (L.hd q) (L.tl q))
    (is_null (next (L.last q)) == true)
    m;
  (* construct the conclusion *)
  assert (ptr0 == ({ head = next x; tail = ptr.tail }));
  assert (L.last (x :: q) == L.last q);
  llist_with_tail_fragment_cons ptr x q;
  pure_star_interp
    (llist_with_tail_fragment ptr x q)
    (is_null (next (L.last (x :: q))) == true)
    m;
  llist_with_tail_cons ptr (x :: q)
