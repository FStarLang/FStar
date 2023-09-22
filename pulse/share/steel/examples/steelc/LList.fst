module LList
open Steel.ST.GenElim
open Steel.ST.C.Types

module U32 = FStar.UInt32

noextract
inline_for_extraction
[@@ norm_field_attr]
let cell_fields =
  field_description_cons "hd" (scalar U32.t) (
  field_description_cons "tl" (scalar void_ptr) (
  field_description_nil))

inline_for_extraction noextract
let cell_n : Type0 = norm Steel.C.Typestring.norm_typestring (Steel.C.Typestring.mk_string_t "LList.cell")

let _ = define_struct0 cell_n "LList.cell" cell_fields

inline_for_extraction noextract
let cell = struct0 cell_n "LList.cell" cell_fields

[@@__reduce__]
let llist_nil (p: ptr cell) : Tot vprop =
  pure (p == null _)

[@@__reduce__]
let llist_cons (p: ptr cell) (a: U32.t) (q: Ghost.erased (list U32.t)) (llist: (ptr cell -> (l: Ghost.erased (list U32.t) { List.Tot.length l < List.Tot.length (a :: q) }) -> Tot vprop)) : Tot vprop =
  exists_ (fun (p1: ref cell) -> exists_ (fun (p2: ptr cell) ->
    pts_to p1 (struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (ghost_void_ptr_of_ptr_gen p2)) (unknown cell))) `star`
    llist p2 q `star`
    freeable p1 `star`
    pure (p == p1)
  ))

let rec llist (p: ptr cell) (l: Ghost.erased (list U32.t)) : Tot vprop (decreases (List.Tot.length l)) =
  match Ghost.reveal l with
  | [] -> llist_nil p
  | a :: q -> llist_cons p a q llist

let intro_llist_cons
  (#opened: _)
  (p1: ref cell) (#v1: Ghost.erased (typeof cell)) (p2: ptr cell) (a: U32.t) (q: Ghost.erased (list U32.t))
: STGhost unit opened
    (pts_to p1 v1 `star`
      llist p2 q `star`
      freeable p1
    )
    (fun _ -> llist p1 (a :: q))
    (Ghost.reveal v1 `struct_eq` struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (ghost_void_ptr_of_ptr_gen p2)) (unknown cell)))
    (fun _ -> True)
= noop ();
  rewrite_with_tactic (llist_cons p1 a q llist) (llist p1 (a :: q))

let elim_llist_cons
  (#opened: _)
  (p1: ptr cell) (a: U32.t) (q: Ghost.erased (list U32.t))
: STGhostT (p2: Ghost.erased (ptr cell) { ~ (p1 == null _) }) opened
    (llist p1 (a :: q))
    (fun p2 ->
      pts_to p1 (struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (ghost_void_ptr_of_ptr_gen p2)) (unknown cell))) `star`
      llist p2 q `star`
      freeable p1
    )
= rewrite_with_tactic (llist p1 (a :: q)) (llist_cons p1 a q llist);
  let _ = gen_elim () in
  let p2' = vpattern_erased (fun x -> llist x q) in
  let p2 : (p2: Ghost.erased (ptr cell) { ~ (p1 == null _) }) = p2' in
  vpattern_rewrite (fun x -> llist x q) p2;
  rewrite (pts_to _ _) (pts_to _ _);
  rewrite (freeable _) (freeable _);
  _

let rewrite_with_implies
  (#opened: _)
  (a b: vprop)
: STGhost unit opened
    a
    (fun _ -> b `star` (b `implies_` a))
    (a == b)
    (fun _ -> True)
= rewrite a b;
  intro_implies b a emp (fun _ -> rewrite b a)

let thunk_implies
  (#opened: _)
  (p: vprop)
: STGhostT unit opened
    p
    (fun _ -> emp `implies_` p)
= intro_implies emp p p (fun _ -> noop ())

let extract_pure_with_implies
  (#opened: _)
  (p: prop)
: STGhost unit opened
    (pure p)
    (fun _ -> emp `implies_` pure p)
    True
    (fun _ -> p)
= extract_pure p;
  thunk_implies (pure p)

let llist_pts_to_or_null
  (#opened: _)
  (p: ptr cell)
  (l: Ghost.erased (list U32.t))
: STGhostT (Ghost.erased (typeof cell)) opened
    (llist p l)
    (fun c ->
      pts_to_or_null p c `star`
        (pts_to_or_null p c `implies_` llist p l)
    )
= match l with
  | [] ->
    rewrite_with_implies (llist p l) (llist_nil p);
    let _ = extract_pure _ in
    thunk_implies (llist_nil p);
    let c = uninitialized cell in
    rewrite_with_implies emp (pts_to_or_null p c);
    implies_trans (pts_to_or_null p c) emp (llist_nil p);
    implies_trans (pts_to_or_null p c) (llist_nil p) (llist p l);
    c
  | a :: q ->
    rewrite (llist p l) (llist p (a :: q));
    let p2 = elim_llist_cons p a q in
    let c = vpattern_replace (pts_to p) in
    rewrite (pts_to p c) (pts_to_or_null p c);
    intro_implies (pts_to_or_null p c) (llist p l) (llist p2 q `star` freeable p) (fun _ ->
      rewrite (pts_to_or_null p c) (pts_to p c);
      intro_llist_cons p p2 a q;
      rewrite (llist p (a :: q)) (llist p l)
    );
    c

[@@__reduce__]
let pllist0
  (p: ref (scalar (ptr cell)))
  (l: Ghost.erased (list U32.t))
: Tot vprop
= exists_ (fun (pc: ptr cell) ->
    pts_to p (mk_scalar pc) `star`
    llist pc l
  )

let pllist
  (p: ref (scalar (ptr cell)))
  (l: Ghost.erased (list U32.t))
: Tot vprop
= pllist0 p l

let pllist_get
  (#l: Ghost.erased (list U32.t))
  (p: ref (scalar (ptr cell)))
: STT (ptr cell)
    (pllist p l)
    (fun pc -> pts_to p (mk_scalar (Ghost.reveal pc)) `star` llist pc l)
= rewrite (pllist p l) (pllist0 p l);
  let _ = gen_elim () in
  let pc = read p in
  vpattern_rewrite (fun x -> llist x l) pc;
  return pc

let pllist_put
  (#v: Ghost.erased (scalar_t (ptr cell)))
  (#l: Ghost.erased (list U32.t))
  (p: ref (scalar (ptr cell)))
  (pc: ptr cell)
: ST unit
    (pts_to p v `star` llist pc l)
    (fun _ -> pllist p l)
    (full (scalar (ptr cell)) v)
    (fun _ -> True)
= write p pc;
  rewrite (pllist0 p l) (pllist p l)

let push
  (#l: Ghost.erased (list U32.t))
  (a: U32.t)
  (p: ref (scalar (ptr cell)))
: STT bool
    (pllist p l)
    (fun b -> pllist p (if b then a :: l else l))
= let c = alloc cell in
  if is_null c
  then begin
    rewrite (pts_to_or_null _ _) emp;
    rewrite (freeable_or_null _) emp;
    return false
  end else begin
    rewrite (pts_to_or_null _ _) (pts_to c (uninitialized cell));
    rewrite (freeable_or_null c) (freeable c);
    let p_tl0 = pllist_get p in
    let _ = llist_pts_to_or_null p_tl0 _ in
    let p_tl = void_ptr_of_ptr p_tl0 in
    elim_implies (pts_to_or_null p_tl0 _) (llist p_tl0 _);
    let c_hd = struct_field c "hd" () in
    let c_tl = struct_field c "tl" () in
    write c_hd a;
    write c_tl p_tl;
    let _ = unstruct_field_and_drop c "tl" c_tl in
    let _ = unstruct_field_and_drop c "hd" c_hd in
    intro_llist_cons c p_tl0 a l;
    pllist_put p c;
    return true
  end

inline_for_extraction noextract
let llist_of_void_ptr
  (#opened: _)
  (#l: Ghost.erased (list U32.t))
  (p: void_ptr)
: STAtomicBase (ptr cell) false opened Unobservable
    (llist (ghost_ptr_gen_of_void_ptr p (typeof cell)) l)
    (fun p' -> llist p' l)
    True
    (fun p' -> p' == ghost_ptr_gen_of_void_ptr p (typeof cell))
= let c = llist_pts_to_or_null (ghost_ptr_gen_of_void_ptr p (typeof cell)) l in
  let p' = ptr_of_void_ptr p in
  vpattern_rewrite (fun p -> pts_to_or_null p _) (ghost_ptr_gen_of_void_ptr p (typeof cell));
  elim_implies (pts_to_or_null (ghost_ptr_gen_of_void_ptr p (typeof cell)) c) (llist (ghost_ptr_gen_of_void_ptr p (typeof cell)) l);
  vpattern_rewrite (fun p' -> llist p' _) p';
  return p'

let pop
  (#l: Ghost.erased (list U32.t))
  (p: ref (scalar (ptr cell)))
  (sq: squash (Cons? l))
: ST U32.t
    (pllist p l)
    (fun _ -> pllist p (List.Tot.tl l))
    (True)
    (fun res -> res == List.Tot.hd l)
= rewrite (pllist p l) (pllist p (List.Tot.hd l :: List.Tot.tl l));
  let c = pllist_get p in
  let _ = elim_llist_cons c (List.Tot.hd l) (List.Tot.tl l) in
  let c_hd = struct_field c "hd" () in
  let c_tl = struct_field c "tl" () in
  let res = read c_hd in
  let p_tl0 = read c_tl in // type ascription necessary to avoid C compiler warning -Wincompatible-pointer-types
  vpattern_rewrite (fun p -> llist p _) (Ghost.hide (ghost_ptr_gen_of_void_ptr p_tl0 (typeof cell)));
  let p_tl = llist_of_void_ptr p_tl0 in
  let _ = unstruct_field c "tl" c_tl in
  let _ = unstruct_field c "hd" c_hd in
  free c;
  pllist_put p p_tl;
  drop (has_struct_field c "hd" _);
  drop (has_struct_field _ _ _);
  return res

let init
  (#v: Ghost.erased (scalar_t (ptr cell)))
  (r: ref (scalar (ptr cell)))
: ST unit
    (pts_to r v)
    (fun _ -> pllist r [])
    (full (scalar (ptr cell)) v)
    (fun _ -> True)
= noop ();
  rewrite (llist_nil (null _)) (llist (null _) []);
  pllist_put r (null _)
