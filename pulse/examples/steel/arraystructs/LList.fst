module LList
open Steel.C.Types

module U32 = FStar.UInt32

noextract
inline_for_extraction
[@@ norm_field_attr]
let cell_fields =
  field_description_cons "hd" (scalar U32.t) (
  field_description_cons "tl" (scalar void_ptr) (
  field_description_nil))

let _ = define_struct "LList.cell" cell_fields

inline_for_extraction noextract
let cell = struct "LList.cell" cell_fields

let rec llist' (p: ptr cell) (l: Ghost.erased (list U32.t)) : Tot vprop (decreases (Ghost.reveal l)) =
  match Ghost.reveal l with
  | [] -> pure (p == null _)
  | a :: q ->
    h_exists (fun (_: squash (~ (p == null _) /\ freeable p)) ->
      h_exists (fun (p' : ptr cell) ->
      pts_to p (struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (p' <: void_ptr)) (unknown cell))) `star`
      llist' p' q
    ))

[@@__steel_reduce__]
let llist (p: ptr cell) (l: Ghost.erased (list U32.t)) : Tot vprop = VUnit ({
  hp = hp_of (llist' p l);
  t = _;
  sel = trivial_selector _;
})

let change_slprop_by_norm
  (#opened: _) (p q: vprop)
: SteelGhost unit opened p (fun _ -> q) (fun _ -> normalize (hp_of p == hp_of q)) (fun _ _ _ -> True)
= rewrite_slprop p q (fun _ -> ())

let llist_intro_nil (#opened: _) (p: ptr cell) : SteelGhost unit opened
  emp
  (fun _ -> llist p [])
  (fun _ -> p == null _)
  (fun _ _ _ -> True)
= intro_pure (p == null _);
  change_slprop_by_norm
    (pure (p == null _))
    (llist p [])

let llist_intro_cons (#opened: _) (p: ref cell) (s: Ghost.erased (struct_t "LList.cell" cell_fields)) (a: U32.t) (p' : ptr cell) (q: Ghost.erased (list U32.t)) : SteelGhost unit opened
  (pts_to p s `star` llist p' q)
  (fun _ -> llist p (a :: q))
  (fun _ ->
    freeable p /\
    s `struct_eq` struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (p' <: void_ptr)) (unknown cell))
  )
  (fun _ _ _ -> True)
= change_equal_slprop (pts_to p s) (pts_to p (struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (p' <: void_ptr)) (unknown cell))));
  intro_exists p' (fun (p' : ptr cell) -> pts_to p (struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (p' <: void_ptr)) (unknown cell))) `star`
      llist p' q
  );
  intro_exists () (fun (_: squash (~ (p == null _) /\ freeable p)) ->
    h_exists (fun (p' : ptr cell) -> pts_to p (struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (p' <: void_ptr)) (unknown cell))) `star`
      llist p' q
  ));
  change_slprop_by_norm
    (h_exists _)
    (llist p (a :: q))

let llist_elim_nil (#opened: _) (p: ptr cell) (l: Ghost.erased (list U32.t)) : SteelGhost unit opened
  (llist p l)
  (fun _ -> emp)
  (fun _ -> Nil? l)
  (fun _ _ _ -> p == null _)
= change_equal_slprop (llist p l) (llist p []);
  change_slprop_by_norm
    (llist p [])
    (pure (p == null _));
  elim_pure _

let llist_elim_cons (#opened: _) (p: ptr cell) (l: Ghost.erased (list U32.t)) (sq: squash (Cons? l))
: SteelGhostT (p': Ghost.erased (ptr cell) { ~ (p == null _) /\ freeable p }) opened
  (llist p l)
  (fun p' ->
    pts_to p (struct_set_field "hd" (mk_scalar (List.Tot.hd l)) (struct_set_field "tl" (mk_scalar (p' <: void_ptr)) (unknown cell))) `star`
    llist p' (List.Tot.tl l)
  )
= let a :: q = Ghost.reveal l in
  change_equal_slprop (llist p l) (llist p (a :: q));
  change_slprop_by_norm
    (llist p (a :: q))
    (h_exists (fun (_: squash (~ (p == null _) /\ freeable p)) ->
      h_exists (fun (p' : ptr cell) ->
      pts_to p (struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (p' <: void_ptr)) (unknown cell))) `star`
      llist p' q
    )));
  let prf : Ghost.erased (squash (~ (p == null _) /\ freeable p)) = witness_exists () in
  let _ = Ghost.reveal prf in
  let p1 = witness_exists () in
  let p' : (p': Ghost.erased (ptr cell) { ~ (p == null _) /\ freeable p }) = p1 in
  change_equal_slprop
    (pts_to p (struct_set_field "hd" (mk_scalar a) (struct_set_field "tl" (mk_scalar (p1 <: void_ptr)) (unknown cell))))
    (pts_to p (struct_set_field "hd" (mk_scalar (List.Tot.hd l)) (struct_set_field "tl" (mk_scalar (p' <: void_ptr)) (unknown cell))));
  change_equal_slprop
    (llist _ q)
    (llist p' (List.Tot.tl l));
  p'

[@@__steel_reduce__]
let pllist
  (p: ref (scalar (ptr cell)))
  (l: Ghost.erased (list U32.t))
: Tot vprop
= h_exists (fun (pc: ptr cell) ->
    pts_to p (mk_scalar pc) `star`
    llist pc l
  )

let pllist_get
  (#l: Ghost.erased (list U32.t))
  (p: ref (scalar (ptr cell)))
: SteelT (ptr cell)
    (pllist p l)
    (fun pc -> pts_to p (mk_scalar (Ghost.reveal pc)) `star` llist pc l)
= let _ = witness_exists () in
  let pc = read p in
  change_equal_slprop (pts_to p _) (pts_to p (mk_scalar (Ghost.reveal pc)));
  change_equal_slprop (llist _ _) (llist pc l);
  return pc

let pllist_put
  (#v: Ghost.erased (scalar_t (ptr cell)))
  (#l: Ghost.erased (list U32.t))
  (p: ref (scalar (ptr cell)))
  (pc: ptr cell)
: Steel unit
    (pts_to p v `star` llist pc l)
    (fun _ -> pllist p l)
    (fun _ -> full (scalar (ptr cell)) v)
    (fun _ _ _ -> True)
= write p pc;
  intro_exists pc (fun (pc: ptr cell) ->
    pts_to p (mk_scalar pc) `star`
    llist pc l
  );
  change_slprop_by_norm
    (h_exists (fun (pc: ptr cell) ->
      pts_to p (mk_scalar pc) `star`
      llist pc l
    ))
    (pllist p l)

let push
  (#l: Ghost.erased (list U32.t))
  (a: U32.t)
  (p: ref (scalar (ptr cell)))
: SteelT bool
    (pllist p l)
    (fun b -> pllist p (if b then a :: l else l))
= let c = alloc cell in
  if is_null c
  then begin
    assert_null c;
    return false
  end else begin
    assert_not_null c;
    let p_tl = pllist_get p in
    let c_hd = struct_field c "hd" in
    let c_tl = struct_field c "tl" in
    write c_hd a;
    write c_tl p_tl;
    unstruct_field c "tl" c_tl;
    unstruct_field c "hd" c_hd;
    llist_intro_cons c _ a p_tl _;
    pllist_put p c;
    return true
  end

let pop
  (#l: Ghost.erased (list U32.t))
  (p: ref (scalar (ptr cell)))
  (sq: squash (Cons? l))
: Steel U32.t
    (pllist p l)
    (fun _ -> pllist p (List.Tot.tl l))
    (fun _ -> True)
    (fun _ res _ -> res == List.Tot.hd l)
= let c = pllist_get p in
  let _ = llist_elim_cons c _ () in
  let c_hd = struct_field c "hd" in
  let c_tl = struct_field c "tl" in
  let res = read c_hd in
  let p_tl = read c_tl in
  unstruct_field c "tl" c_tl;
  unstruct_field c "hd" c_hd;
  free c;
  change_equal_slprop (llist _ _) (llist p_tl (List.Tot.tl l));
  pllist_put p p_tl;
  return res

let init
  (#v: Ghost.erased (scalar_t (ptr cell)))
  (r: ref (scalar (ptr cell)))
: Steel unit
    (pts_to r v)
    (fun _ -> pllist r [])
    (fun _ -> full (scalar (ptr cell)) v)
    (fun _ _ _ -> True)
= llist_intro_nil (null _);
  pllist_put r (null _)
