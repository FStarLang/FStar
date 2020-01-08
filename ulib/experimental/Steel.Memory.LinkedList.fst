module Steel.Memory.LinkedList

open Steel.Memory.RST
open Steel.Permissions
module M = Steel.Memory
module L = FStar.List.Tot
module FI = FStar.IndefiniteDescription

#reset-options "--__no_positivity"

noeq
type t (a:Type0) =
  ptr:M.ref (cell a)

and cell (a:Type0) = {
  next: t a;
  data: a;
}

/// These predicates and assumptions should go into Memory at some point
assume val null (#a:Type0) : M.ref a
assume val is_null (#a:Type0) (r:M.ref a) : Tot (b:bool{b <==> r == null})

let pred_is_null (#a:Type) (ptr:t a) : Tot (M.fp_prop M.emp) = fun h -> ptr == null
let pred_is_not_null (#a:Type) (ptr:t a) : Tot (M.fp_prop M.emp) = fun h -> ptr =!= null

/// Similarly, once we have a good model for null, the refinements pred_is_null/not_null should
/// not be needed since they should be derivable from pts_to
let rec slist' (#a:Type) (ptr:t a) (l:list (cell a)) : Tot M.hprop
  (decreases l)
  = match l with
  | [] -> M.refine M.emp (pred_is_null ptr)
  | hd::tl -> M.refine M.emp (pred_is_not_null ptr) `M.star` (M.pts_to ptr full_permission hd `M.star` slist' hd.next tl)

let slist_exists (#a:Type) (ptr:t a) : Tot M.hprop =
    M.h_exists (slist' ptr)

let rec injective_slist' (#a:Type) (ptr:t a) (l1 l2:list (cell a)) (h:M.heap) : Lemma
  (requires M.interp (slist' ptr l1) h /\ M.interp (slist' ptr l2) h)
  (ensures l1 == l2)
  (decreases l1)
  = match l1, l2 with
    | [], [] -> ()
    | [], hd::tl | hd::tl, [] ->
      M.refine_equiv M.emp (pred_is_null ptr) h;
      M.affine_star (M.refine M.emp (pred_is_not_null ptr))
        (M.pts_to ptr full_permission hd `M.star` slist' hd.next tl) h;
      M.refine_equiv M.emp (pred_is_not_null ptr) h
    | hd1::tl1, hd2::tl2 ->
      M.affine_star (M.refine M.emp (pred_is_not_null ptr))
        (M.pts_to ptr full_permission hd1 `M.star` slist' hd1.next tl1) h;
      M.affine_star (M.refine M.emp (pred_is_not_null ptr))
        (M.pts_to ptr full_permission hd2 `M.star` slist' hd2.next tl2) h;
      M.affine_star (M.pts_to ptr full_permission hd1) (slist' hd1.next tl1) h;
      M.affine_star (M.pts_to ptr full_permission hd2) (slist' hd2.next tl2) h;
      M.pts_to_injective ptr full_permission hd1 hd2 h;
      injective_slist' hd1.next tl1 tl2 h

let split_interp_slist (#a:Type) (ptr:t a) (l:list (cell a)) (h:M.heap) : Lemma
  (requires M.interp (slist' ptr l) h /\ ptr =!= null)
  (ensures Cons? l /\ M.interp (M.ptr ptr) h /\ M.interp (slist' (M.sel ptr h).next (L.tl l)) h)
  = admit()

let rec length' (#a:Type) (ptr:t a) (l:list (cell a)) (h:M.hheap (slist' ptr l))
  : Tot nat
  (decreases l)
  =
  if is_null ptr then 0
  else (
    split_interp_slist ptr l h;
    let next = (M.sel ptr h).next in
    1 + length' next (L.tl l) h
  )

let length (#a:Type) (ptr:t a) (h:M.hheap (slist_exists ptr)) : GTot nat =
  M.reveal_exists (slist' ptr) h;
  assert (exists x. M.interp (slist' ptr x) h);
  let (|l, _ |) = FI.indefinite_description (list (cell a)) (fun x -> M.interp (slist' ptr x) h) in
  length' ptr l h

let rec list_view' (#a:Type) (ptr:t a) (l:list (cell a)) (h:M.hheap (slist' ptr l))
  : Tot (list a)
  (decreases l) =
  match l with
  | [] -> []
  | hd::tl ->
    M.affine_star (M.refine M.emp (pred_is_not_null ptr)) (M.pts_to ptr full_permission hd `M.star` slist' hd.next tl) h;
    M.affine_star (M.pts_to ptr full_permission hd) (slist' hd.next tl) h;
    hd.data :: list_view' hd.next tl h

let list_view (#a:Type) (ptr:t a) (h:M.hheap (slist_exists ptr)) : GTot (list a) =
  M.reveal_exists (slist' ptr) h;
  assert (exists x. M.interp (slist' ptr x) h);
  let (|l, _ |) = FI.indefinite_description (list (cell a)) (fun x -> M.interp (slist' ptr x) h) in
  list_view' ptr l h

let slist (#a:Type) (ptr:t a) : Tot viewable'
   = {t = list a;
      fp = slist_exists ptr;
      sel = list_view ptr }

[@__reduce__]
let vlist (#a:Type) (ptr:t a) = VUnit (slist ptr)

assume
val cell_alloc (#a:Type)
               (init:cell a)
               : Steel (t a) (vemp) (fun ptr -> vptr ptr)
                       (requires fun _ -> True)
                       (ensures fun _ ptr m1 -> view_sel (vptr ptr) m1 == init /\ ptr =!= null)

val set_cell (#a:Type) (ptr:t a) (c:cell a) (v:a)
  : Steel unit
          (vptr ptr)
          (fun _ -> vptr ptr)
          (requires fun m0 -> True)
          (ensures fun _ _ m1 -> view_sel (vptr ptr) m1 == ({c with data = v}))

let set_cell #a ptr c v = fupd ptr ({c with data = v})

let lemma_cons
  (#a:Type)
  (hd tl:t a)
  (h:M.heap)
  : Lemma (requires M.interp (fp_of (vptr hd <*> vlist tl)) h /\ hd =!= null /\
                     normal ((view_sel (vptr hd) (mk_rmem (vptr hd <*> vlist tl) h)).next) == tl
          )
          (ensures M.interp (fp_of (vlist hd)) h /\
                   M.interp (fptr hd) h /\
                   M.interp (fp_of (vlist tl)) h /\
                   M.interp (fp_of (vptr hd <*> vlist tl)) h /\ (
                   let m0 = mk_rmem (vlist hd) h in
                   let m1 = mk_rmem (vptr hd <*> vlist tl) h in
                   view_sel (vlist hd) m0 ==
                   (view_sel (vptr hd) m1).data :: view_sel (vlist tl) m1))
  =
  M.affine_star (fp_of (vptr hd)) (fp_of (vlist tl)) h;
  let v_hd = fsel hd h in
  // assert (v_hd.next == tl);
  let h1, h2 = M.split_mem (fp_of (vptr hd)) (fp_of (vlist tl)) h in
  M.reveal_exists (slist' tl) h2;
  let (|l_tl', _ |) = FI.indefinite_description (list (cell a)) (fun x -> M.interp (slist' tl x) h2) in
  M.sel_lemma hd full_permission h1;
  M.sel_split_lemma hd h1 h2;
  // assert (M.sel hd h1 == v_hd);
  M.intro_star (M.pts_to hd full_permission v_hd) (slist' v_hd.next l_tl') h1 h2;
  let p = M.pts_to hd full_permission v_hd `M.star` slist' tl l_tl' in
  // assert (M.interp p h);
  M.emp_unit p;
  M.star_commutative p M.emp;
  // assert (M.interp (M.emp `M.star` p) h);
  M.refine_equiv (M.emp `M.star` p) (pred_is_not_null hd) h;
  M.refine_star M.emp p (pred_is_not_null hd);
  // assert (M.interp (slist' hd (v_hd::l_tl')) h);
  M.intro_exists (v_hd::l_tl') (slist' hd) h;
  // assert (M.interp (fp_of (vlist hd)) h
  // Start proving the part about views
  M.reveal_exists (slist' hd) h;
  M.reveal_exists (slist' tl) h;
  let (|l_full, _ |) = FI.indefinite_description (list (cell a)) (fun x -> M.interp (slist' hd x) h) in
  let (|l_tl, _ |) = FI.indefinite_description (list (cell a)) (fun x -> M.interp (slist' tl x) h) in

  let m0 = mk_rmem (vlist hd) h in
  let m1 = mk_rmem (vptr hd <*> vlist tl) h in
  assume (l_tl' == l_tl); // Should be provable with value_depends_only_on predicate on views
  assert (view_sel (vlist hd) m0 == list_view' hd l_full h);
  assert (view_sel (vlist tl) m1 == list_view' tl l_tl h);
  injective_slist' hd l_full (v_hd::l_tl') h
  // assert (l_full == v_hd::l_tl')

val pack_list (#a:Type) (hd tl:t a)
  : Steel unit
          (vptr hd <*> vlist tl)
          (fun _ -> vlist hd)
          (requires fun m0 -> (view_sel (vptr hd) m0).next == tl /\ hd =!= null)
          (ensures fun m0 _ m1 -> view_sel (vlist hd) m1 ==
            (view_sel (vptr hd) m0).data :: (view_sel (vlist tl) m0)
          )

let pack_list #a hd tl =
  Classical.forall_intro (Classical.move_requires (lemma_cons hd tl))

/// What actually prevents us to return unit here and modify ptr in place is the
/// current model of null pointers. It might not be the only blocking issue
val cons (#a:Type) (ptr:t a) (v:a)
  : Steel (t a)
          (vlist ptr)
          (fun res -> vlist res)
          (fun _ -> True)
          (fun m0 res m1 -> view_sel (vlist res) m1 == v:: (view_sel (vlist ptr) m0))

#set-options "--z3rlimit 20"

let cons #a ptr v =
  let m0 = get (vlist ptr) in
  let hd = frame (vlist ptr)
                 (fun () -> cell_alloc ({next = ptr; data = v})) in
  let m1 = get (vptr hd <*> vlist ptr) in
  assert ((view_sel (vptr hd) m1).data == v);
  pack_list hd ptr;
  assert (view_sel (vlist ptr) m0 == view_sel (vlist ptr) m1);
  hd
