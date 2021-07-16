module Steel.Pointer

(* NOTE: this implementation based on a sequence of references is
   provisional. It is here only to show that the interface can be
   implemented, but we expect it to be replaced with a full model for
   C pointers handling structs, unions, etc. *)

open Steel.Reference
module RS = Steel.Pointer.RefSeq

unfold
let base_array_precond (#a: Type0) (x: RS.array1 a) : Tot prop =
  size_precond (Seq.length x) /\ Seq.length x > 0

[@@erasable]
noeq
type base_array a = {
  array: RS.array2 a; // ghost
  base_alloc_unit: ghost_ref unit; // to track permissions for freeing
  base_array_prf: squash (base_array_precond array);
}

let base_array_len #a b =
  int_to_size_t (Seq.length b.array)

let base_array_freeable _ = True

noeq
type t_nn a = {
  base: RS.array1 a; // pure
  alloc_unit: ghost_ref unit; // to track permissions for freeing, cf. base_alloc_unit above
  offset: size_t;
  prf: squash (base_array_precond base /\ size_v offset <= Seq.length base);
}

let t a = option (t_nn a)

let null _ = None

let g_is_null p = None? p

let base #a p =
  {
    array = Ghost.hide (Some?.v p).base;
    base_alloc_unit = (Some?.v p).alloc_unit;
    base_array_prf = ();
  }

let offset p = (Some?.v p).offset

let base_offset_inj p1 p2 = ()

val pure_add
  (#a: Type0)
  (p: t a)
  (off: size_t)
: Pure (t a)
  (requires (g_is_null p == false /\ size_v (offset p) + size_v off <= size_v (base_array_len (base p))))
  (ensures (fun res ->
    g_is_null res == false /\
    base res == base p /\
    size_v (offset res) == size_v (offset p) + size_v off
  ))

let pure_add p off = Some ({
  base = (Some?.v p).base;
  alloc_unit = (Some?.v p).alloc_unit;
  offset = (Some?.v p).offset `size_add` off;
  prf = ();
})

let g_add p off = pure_add p off

val pure_sub
  (#a: Type0)
  (p: t a)
  (off: size_t)
: Pure (t a)
  (requires (g_is_null p == false /\ size_v (offset p) >= size_v off))
  (ensures (fun res ->
    g_is_null res == false /\
    base res == base p /\
    size_v (offset res) == size_v (offset p) - size_v off
  ))

let pure_sub p off = Some ({
  base = (Some?.v p).base;
  alloc_unit = (Some?.v p).alloc_unit;
  offset = (Some?.v p).offset `size_sub` off;
  prf = ();
})

let g_sub p off = pure_sub p off

let t_r_prop
  (#a: Type)
  (x: t_nn a)
  (r: range)
: Tot prop
= 
  0 <= size_v x.offset + r.range_from /\
  size_v x.offset + r.range_to <= Seq.length x.base

let t_r (a: Type) (r: range) = (x: t_nn a { t_r_prop x r })

let array_of
  (#a: Type)
  (#r: range)
  (x: t_r a r)
: Tot (RS.array2 a)
= Seq.slice x.base (size_v x.offset + r.range_from) (size_v x.offset + r.range_to)

let prod_perm (p1 p2: perm) : Tot perm =
  MkPerm (let open FStar.Real in MkPerm?.v p1 *. MkPerm?.v p2)

let vptr_range0_refine
  (#a: Type)
  (x: t a)
  (r: range)
  (_: t_of emp)
: Tot prop
= Some? x /\ t_r_prop (Some?.v x) r

let vptr_range0_rewrite1
  (#a: Type)
  (x: t a)
  (r: range)
  (_: t_of (emp `vrefine` vptr_range0_refine x r))
: Tot (t_r a r)
= Some?.v x

let vptr_range0_payload
  (a: Type)
  (r: range)
  (x': t_r a r)
: Tot vprop
= ghost_vptrp x'.alloc_unit (r.range_write_perm `prod_perm` r.range_free_perm) `star` RS.varray2 (array_of x') r.range_write_perm

let vptr_range0_rewrite2
  (#a: Type)
  (x: t a)
  (r: range)
  (y: normal (t_of (emp `vrefine` vptr_range0_refine x r `vrewrite` vptr_range0_rewrite1 x r `vdep` vptr_range0_payload a r)))
: Tot (Seq.lseq a (r.range_to - r.range_from))
= let (| _, (_, v) |) = y in
  v

let vptr_range0
  (#a: Type)
  (x: t a)
  (r: range)
: Tot vprop
= emp `vrefine` vptr_range0_refine x r `vrewrite` vptr_range0_rewrite1 x r `vdep` vptr_range0_payload a r `vrewrite` vptr_range0_rewrite2 x r

let slptr_range x r = hp_of (vptr_range0 x r)

let ptr_select x r = fun h -> sel_of (vptr_range0 x r) h

val intro_vptr_range
  (#opened: _)
  (#a: Type)
  (x: t a)
  (r: range)
  (u: ghost_ref unit)
  (pu: perm)
  (w: RS.array2 a)
  (pw: perm)
: SteelGhost unit opened
    (ghost_vptrp u pu `star` RS.varray2 w pw)
    (fun _ -> vptr_range x r)
    (fun _ ->
      Some? x /\
      t_r_prop (Some?.v x) r /\
      u == (Some?.v x).alloc_unit /\
      MkPerm?.v pu == (let open FStar.Real in MkPerm?.v r.range_write_perm *. MkPerm?.v r.range_free_perm) /\ // FIXME: WHY not pu == r.range_write_perm `prod_perm` r.range_free_perm /\
      w `Seq.equal` array_of #_ #r (Some?.v x) /\
      pw == r.range_write_perm
    )
    (fun h _ h' ->
      Seq.length w == r.range_to - r.range_from /\
      h' (vptr_range x r) == h (RS.varray2 w pw)
    )

#push-options "--z3rlimit 16"
#restart-solver

let intro_vptr_range
  #_ #a x r u pu w pw
=
  intro_vrefine emp (vptr_range0_refine x r);
  intro_vrewrite (emp `vrefine` vptr_range0_refine x r) (vptr_range0_rewrite1 x r);
  reveal_star (ghost_vptrp u pu) (RS.varray2 w pw);
  intro_vdep
    (emp `vrefine` vptr_range0_refine x r `vrewrite` vptr_range0_rewrite1 x r)
    (ghost_vptrp u pu `star` RS.varray2 w pw)
    (vptr_range0_payload a r);
  intro_vrewrite
    (emp `vrefine` vptr_range0_refine x r `vrewrite` vptr_range0_rewrite1 x r `vdep` vptr_range0_payload a r)
    (vptr_range0_rewrite2 x r);
  assert_norm (
    emp `vrefine` vptr_range0_refine x r `vrewrite` vptr_range0_rewrite1 x r `vdep` vptr_range0_payload a r `vrewrite` vptr_range0_rewrite2 x r ==
    vptr_range0 x r
  );
  change_slprop_rel
    (vptr_range0 x r)
    (vptr_range x r)
    (fun x y -> x == y)
    (fun _ -> ())

#pop-options

[@@erasable]
noeq
type elim_vptr_range_t
  (a: Type)
= {
  e_alloc_unit: ghost_ref unit;
  e_alloc_unit_perm: perm;
  e_array: RS.array2 a;
}

val elim_vptr_range
  (#opened: _)
  (#a: Type)
  (x: t a)
  (r: range)
: SteelGhost (elim_vptr_range_t a) opened
    (vptr_range x r)
    (fun res -> ghost_vptrp res.e_alloc_unit res.e_alloc_unit_perm `star` RS.varray2 res.e_array r.range_write_perm)
    (fun _ -> True)
    (fun h res h' ->
      Some? x /\
      t_r_prop (Some?.v x) r /\
      res.e_alloc_unit == (Some?.v x).alloc_unit /\
      MkPerm?.v res.e_alloc_unit_perm == (let open FStar.Real in MkPerm?.v r.range_write_perm *. MkPerm?.v r.range_free_perm) /\ // same here
      res.e_array == array_of #_ #r (Some?.v x) /\
      h (vptr_range x r) == h' (RS.varray2 res.e_array r.range_write_perm)
    )

let elim_vptr_range
  #_ #a x r
=
  change_slprop_rel
    (vptr_range x r)
    (vptr_range0 x r)
    (fun x y -> x == y)
    (fun _ -> ());
  assert_norm (
    vptr_range0 x r ==
    emp `vrefine` vptr_range0_refine x r `vrewrite` vptr_range0_rewrite1 x r `vdep` vptr_range0_payload a r `vrewrite` vptr_range0_rewrite2 x r
  );
  elim_vrewrite
    (emp `vrefine` vptr_range0_refine x r `vrewrite` vptr_range0_rewrite1 x r `vdep` vptr_range0_payload a r)
    (vptr_range0_rewrite2 x r);
  let x' : Ghost.erased (t_r a r) = elim_vdep
    (emp `vrefine` vptr_range0_refine x r `vrewrite` vptr_range0_rewrite1 x r)
    (vptr_range0_payload a r)
  in
  let res = {
    e_alloc_unit = (Ghost.reveal x').alloc_unit;
    e_alloc_unit_perm = r.range_write_perm `prod_perm` r.range_free_perm;
    e_array = array_of (Ghost.reveal x');
  } in
  change_equal_slprop
    (vptr_range0_payload a r (Ghost.reveal x'))
    (ghost_vptrp res.e_alloc_unit res.e_alloc_unit_perm `star`
      RS.varray2 res.e_array r.range_write_perm);
  ghost_vptrp res.e_alloc_unit res.e_alloc_unit_perm `reveal_star`
      RS.varray2 res.e_array r.range_write_perm;
  elim_vrewrite (emp `vrefine` vptr_range0_refine x r) (vptr_range0_rewrite1 x r);
  elim_vrefine emp (vptr_range0_refine x r);
  res

let vptr_range_not_null
  x r
=
  let res = elim_vptr_range x r in
  intro_vptr_range x r res.e_alloc_unit res.e_alloc_unit_perm res.e_array r.range_write_perm

let vptr_range_or_null1
  (#a: Type)
  (x: t a)
  (r: range)
: Tot vprop
= if g_is_null x then emp else vptr_range x r

let vptr_range_or_null_rewrite
  (#a: Type)
  (x: t a)
  (r: range)
  (s: t_of (vptr_range_or_null1 x r))
: GTot (option (Seq.lseq a (r.range_to - r.range_from)))
= if g_is_null x
  then None
  else Some s

let vptr_range_or_null0
  (#a: Type)
  (x: t a)
  (r: range)
: Tot vprop
= vptr_range_or_null1 x r `vrewrite` vptr_range_or_null_rewrite x r

let slptr_range_or_null x r =
  hp_of (vptr_range_or_null0 x r)

let ptr_or_null_select x r =
  fun h -> sel_of (vptr_range_or_null0 x r) h

let is_null
  x r
=
  return (None? x)

let intro_vptr_range_or_null_none x r =
  assert (g_is_null x == true);
  change_equal_slprop
    emp
    (vptr_range_or_null1 x r);
  intro_vrewrite (vptr_range_or_null1 x r) (vptr_range_or_null_rewrite x r);
  change_slprop_rel
    (vptr_range_or_null0 x r)
    (vptr_range_or_null x r)
    (fun u v -> u == v)
    (fun _ -> ())

let intro_vptr_range_or_null_some x r =
  vptr_range_not_null x r;
  change_equal_slprop
    (vptr_range x r)
    (vptr_range_or_null1 x r);
  intro_vrewrite (vptr_range_or_null1 x r) (vptr_range_or_null_rewrite x r);
  change_slprop_rel
    (vptr_range_or_null0 x r)
    (vptr_range_or_null x r)
    (fun u v -> u == v)
    (fun _ -> ())

let assert_null x r =
  change_slprop_rel
    (vptr_range_or_null x r)
    (vptr_range_or_null0 x r)
    (fun u v -> u == v)
    (fun _ -> ());
  elim_vrewrite (vptr_range_or_null1 x r) (vptr_range_or_null_rewrite x r);
  if g_is_null x
  then begin
    change_equal_slprop
      (vptr_range_or_null1 x r)
      emp
  end else begin
    assert False;
    change_slprop_rel
      (vptr_range_or_null1 x r)
      emp
      (fun _ _ -> False)
      (fun _ -> ())
  end

let assert_not_null x r =
  change_slprop_rel
    (vptr_range_or_null x r)
    (vptr_range_or_null0 x r)
    (fun u v -> u == v)
    (fun _ -> ());
  elim_vrewrite (vptr_range_or_null1 x r) (vptr_range_or_null_rewrite x r);
  if g_is_null x
  then begin
    assert False;
    change_slprop_rel
      (vptr_range_or_null1 x r)
      (vptr_range x r)
      (fun _ _ -> False)
      (fun _ -> ())
  end else begin
    change_equal_slprop
      (vptr_range_or_null1 x r)
      (vptr_range x r)
  end

let calloc
  x len
=
  let base = RS.valloc (size_v len) x in
  let offset = mk_size_t 0ul in
  let prf : squash (base_array_precond base /\ size_v offset <= Seq.length base) = () in
  let u = ghost_alloc () in
  let res = Some ({
    base = base;
    alloc_unit = u;
    offset = offset;
    prf = prf;
  }) in
  intro_vptr_range res (calloc_range len) u _ base _;
  intro_vptr_range_or_null_some res _;
  return res

#restart-solver

let free
  #a x r
=
  let res = elim_vptr_range x r in
  let u = (Some?.v x).alloc_unit in
  FStar.Real.mul_id 1.0R;
  change_equal_slprop
    (ghost_vptrp res.e_alloc_unit res.e_alloc_unit_perm)
    (ghost_vptr u);
  ghost_free u;
  let base = (Some?.v x).base in
  change_equal_slprop
    (RS.varray2 res.e_array r.range_write_perm)
    (RS.varray2 base full_perm);
  RS.vfree base

let add
  x r i
=
  let res = elim_vptr_range x r in
  intro_vptr_range x r res.e_alloc_unit res.e_alloc_unit_perm res.e_array r.range_write_perm;
  return (pure_add x i)

let sub
  x r i
=
  let res = elim_vptr_range x r in
  intro_vptr_range x r res.e_alloc_unit res.e_alloc_unit_perm res.e_array r.range_write_perm;
  return (pure_sub x i)

let le x1 x2 _ _ =
  vptr_range_not_null x1 _;
  vptr_range_not_null x2 _;
  assert (base x1 == base x2);
  return ((Some?.v x1).offset `size_le` (Some?.v x2).offset)

let index
  #a x r i
=
  let ge = elim_vptr_range x r in
  let (y: t a { Some? y }) = x in
  let gu = RS.unpack_ith _ ge.e_array (ptrdiff_v i - r.range_from) in
  RS.seq_index_append_cons (ptrdiff_v i - r.range_from) gu.RS.ith_lhs gu.RS.ith_item gu.RS.ith_rhs;
  let gl : Ghost.erased (Seq.lseq a (Seq.length gu.RS.ith_lhs)) = gget (RS.varray2 gu.RS.ith_lhs _) in
  let gi : Ghost.erased a = gget (vptrp gu.RS.ith_item _) in
  let gr : Ghost.erased (Seq.lseq a (Seq.length gu.RS.ith_rhs)) = gget (RS.varray2 gu.RS.ith_rhs _) in
  RS.seq_index_append_cons (ptrdiff_v i - r.range_from) (Ghost.reveal gl) (Ghost.reveal gi) (Ghost.reveal gr);
  let j = (size_v (Some?.v y).offset + ptrdiff_v i) in
  let w = Seq.index (Some?.v y).base j in
  change_equal_slprop
    (vptrp gu.RS.ith_item _)
    (vptrp w r.range_write_perm);
  let res = readp w _ in
  change_equal_slprop
    (vptrp w _)
    (vptrp gu.RS.ith_item r.range_write_perm);
  RS.pack_ith _ gu ge.e_array;
  intro_vptr_range x r _ _ _ _;
  return res

let index_upd
  #a x r i v
=
  let ge = elim_vptr_range x r in
  let (y: t a { Some? y }) = x in
  let gu = RS.unpack_ith _ ge.e_array (ptrdiff_v i - r.range_from) in
  RS.seq_index_append_cons (ptrdiff_v i - r.range_from) gu.RS.ith_lhs gu.RS.ith_item gu.RS.ith_rhs;
  let gl : Ghost.erased (Seq.lseq a (Seq.length gu.RS.ith_lhs)) = gget (RS.varray2 gu.RS.ith_lhs _) in
  let gi : Ghost.erased a = gget (vptrp gu.RS.ith_item _) in
  let gr : Ghost.erased (Seq.lseq a (Seq.length gu.RS.ith_rhs)) = gget (RS.varray2 gu.RS.ith_rhs _) in
  RS.seq_upd_append_cons (ptrdiff_v i - r.range_from) v (Ghost.reveal gl) (Ghost.reveal gi) (Ghost.reveal gr);
  let j = (size_v (Some?.v y).offset + ptrdiff_v i) in
  let w = Seq.index (Some?.v y).base j in
  change_equal_slprop
    (vptrp gu.RS.ith_item _)
    (vptrp w full_perm);
  write w v;
  change_equal_slprop
    (vptrp w _)
    (vptrp gu.RS.ith_item r.range_write_perm);
  RS.pack_ith _ gu ge.e_array;
  intro_vptr_range x r _ _ _ _

#push-options "--z3rlimit 32"
#restart-solver

let merge_left
  p1 p2 r1 r2
=
  let ge1 = elim_vptr_range p1 r1 in
  let ge2 = elim_vptr_range p2 r2 in
  let _ : squash (g_is_null p1 == false) = () in
  let _ : squash (g_is_null p2 == false) = () in
  let _ : squash (base p1 == base p2) = () in
  let _ : squash (size_v (offset p1) + r1.range_to == size_v (offset p2) + r2.range_from) = () in
  let _ : squash (r1.range_write_perm == r2.range_write_perm) = () in
  change_equal_slprop
    (RS.varray2 ge2.e_array _)
    (RS.varray2 ge2.e_array r1.range_write_perm);
  let a = RS.vappend ge1.e_array ge2.e_array _ in
  change_equal_slprop
    (ghost_vptrp ge2.e_alloc_unit _)
    (ghost_vptrp ge1.e_alloc_unit ge2.e_alloc_unit_perm);
  let _ = ghost_gather_gen ge1.e_alloc_unit ge1.e_alloc_unit_perm ge2.e_alloc_unit_perm in
  let res = g_merge_left p1 p2 (GPair r1 r2) in
  FStar.Real.mul_dist_l_to_r (MkPerm?.v r1.range_write_perm) (MkPerm?.v r1.range_free_perm) (MkPerm?.v r2.range_free_perm);
  intro_vptr_range p1 res ge1.e_alloc_unit _ a _;
  res

let merge_right
  p1 p2 r1 r2
=
  let ge1 = elim_vptr_range p1 r1 in
  let ge2 = elim_vptr_range p2 r2 in
  let _ : squash (g_is_null p1 == false) = () in
  let _ : squash (g_is_null p2 == false) = () in
  let _ : squash (base p1 == base p2) = () in
  let _ : squash (size_v (offset p2) + r2.range_to == size_v (offset p1) + r1.range_from) = () in
  let _ : squash (r1.range_write_perm == r2.range_write_perm) = () in
  change_equal_slprop
    (RS.varray2 ge2.e_array _)
    (RS.varray2 ge2.e_array r1.range_write_perm);
  let a = RS.vappend ge2.e_array ge1.e_array _ in
  change_equal_slprop
    (ghost_vptrp ge2.e_alloc_unit _)
    (ghost_vptrp ge1.e_alloc_unit ge2.e_alloc_unit_perm);
  let _ = ghost_gather_gen ge1.e_alloc_unit ge1.e_alloc_unit_perm ge2.e_alloc_unit_perm in
  let res = g_merge_right p1 p2 (GPair r1 r2) in
  FStar.Real.mul_dist_l_to_r (MkPerm?.v r1.range_write_perm) (MkPerm?.v r1.range_free_perm) (MkPerm?.v r2.range_free_perm);
  intro_vptr_range p1 res ge1.e_alloc_unit _ a _;
  res

#pop-options

#push-options "--z3rlimit 16"
#restart-solver

let split
  p r
=
  let ge = elim_vptr_range p r in
  let res = g_split p r in
  let alar = RS.vsplit _ ge.e_array (0 - r.range_from) in
  ghost_share ge.e_alloc_unit;
  FStar.Real.mul_dist_l_to_r (MkPerm?.v r.range_write_perm) (MkPerm?.v (GPair?.fst res).range_free_perm) (MkPerm?.v (GPair?.snd res).range_free_perm);
  intro_vptr_range p (GPair?.fst res) ge.e_alloc_unit _ (RS.GPair?.fst alar) _;
  intro_vptr_range p (GPair?.snd res) ge.e_alloc_unit _ (RS.GPair?.snd alar) _;
  res

#pop-options

let move
  p1 p2 r
= let ge = elim_vptr_range p1 r in
  let res = g_move p1 p2 r in
  intro_vptr_range p2 res ge.e_alloc_unit _ ge.e_array _;
  res

let share
  p r
=
  let ge = elim_vptr_range p _ in
  ghost_share ge.e_alloc_unit;
  let _ = RS.vshare ge.e_array _ in
  let res = g_share r in
  FStar.Real.mul_div_2 (MkPerm?.v r.range_write_perm) (MkPerm?.v r.range_free_perm) FStar.Real.two;
  intro_vptr_range p _ ge.e_alloc_unit _ ge.e_array _;
  intro_vptr_range p _ ge.e_alloc_unit _ ge.e_array _;
  res

let gather
  p r1 r2
=
  let g1 = elim_vptr_range p r1 in
  let g2 = elim_vptr_range p r2 in
  let _ : squash (r1.range_free_perm == r2.range_free_perm) = () in
  let _ : squash (r1.range_from == r2.range_from) = () in
  let _ : squash (r1.range_to == r2.range_to) = () in
  change_equal_slprop
    (ghost_vptrp g2.e_alloc_unit _)
    (ghost_vptrp g1.e_alloc_unit g2.e_alloc_unit_perm);
  let _ = ghost_gather_gen g1.e_alloc_unit g1.e_alloc_unit_perm g2.e_alloc_unit_perm in
  change_equal_slprop
    (RS.varray2 g2.e_array _)
    (RS.varray2 g1.e_array r2.range_write_perm);
  let _ = RS.vgather g1.e_array r1.range_write_perm r2.range_write_perm in
  let res = g_gather r1 r2 in
  FStar.Real.mul_dist_r_to_l (MkPerm?.v r1.range_write_perm) (MkPerm?.v r2.range_write_perm) (MkPerm?.v r1.range_free_perm);
  intro_vptr_range p res g1.e_alloc_unit _ g1.e_array _;
  res
