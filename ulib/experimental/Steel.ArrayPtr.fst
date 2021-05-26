module Steel.ArrayPtr
module AP = Steel.ArrayPtrNotNull

let t a = option (AP.t a)

let g_is_null x = None? x

let varrayptr0_refine
  (#a: Type)
  (x: t a)
  (_: t_of emp)
: Tot prop
= g_is_null x == false

[@@__steel_reduce__]
let varrayptr0_payload
  (#a: Type)
  (x: t a)
  (_: t_of (emp `vrefine` varrayptr0_refine x))
: Tot vprop
= AP.varrayptr (Some?.v x)

let varrayptr0_rewrite
  (#a: Type)
  (x: t a)
  (z: normal (t_of (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload x)))
: Tot (v a)
= let (| _, y |) = z in
  { array = y.AP.array; contents = y.AP.contents; perm = y.AP.perm }

[@@__steel_reduce__; __reduce__]
let varrayptr0
  (#a: Type)
  (x: t a)
: Tot vprop
= emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload x `vrewrite` varrayptr0_rewrite x

let is_arrayptr r = hp_of (varrayptr0 r)

let arrayptr_sel r = fun h -> sel_of (varrayptr0 r) h

val intro_varrayptr
  (#opened: _)
  (#a: Type)
  (x: AP.t a)
: SteelGhost (Ghost.erased (t a)) opened
    (AP.varrayptr x)
    (fun res -> varrayptr res)
    (fun _ -> True)
    (fun h res h' ->
      let r' = h' (varrayptr res) in
      let r = h (AP.varrayptr x) in
      Ghost.reveal res == Some x /\
      r'.array == r.AP.array /\
      r'.contents == r.AP.contents /\
      r'.perm == r.AP.perm
    )

let intro_varrayptr
  #_ #a x
=
  let res : Ghost.erased (t a) = Ghost.hide (Some x) in
  intro_vrefine emp (varrayptr0_refine res);
  intro_vdep
    (emp `vrefine` varrayptr0_refine res)
    (AP.varrayptr x)
    (varrayptr0_payload res);
  intro_vrewrite
    (emp `vrefine` varrayptr0_refine res `vdep` varrayptr0_payload res)
    (varrayptr0_rewrite res);
  change_slprop_rel
    (varrayptr0 res)
    (varrayptr res)
    (fun m n -> m == n)
    (fun m ->
      assert_norm (hp_of (varrayptr res) == hp_of (varrayptr0 res));
      assert_norm (sel_of (varrayptr res) m === sel_of (varrayptr0 res) m)
    );
  res

val elim_varrayptr
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelGhost (Ghost.erased (AP.t a)) opened
    (varrayptr x)
    (fun res -> AP.varrayptr res)
    (fun _ -> True)
    (fun h res h' ->
      let r = h' (AP.varrayptr res) in
      let r' = h (varrayptr x) in
      x == Some (Ghost.reveal res) /\
      r'.array == r.AP.array /\
      r'.contents == r.AP.contents /\
      r'.perm == r.AP.perm
    )

let elim_varrayptr
  #_ #a x
=
  change_slprop_rel
    (varrayptr x)
    (varrayptr0 x)
    (fun m n -> m == n)
    (fun m ->
      assert_norm (hp_of (varrayptr x) == hp_of (varrayptr0 x));
      assert_norm (sel_of (varrayptr x) m === sel_of (varrayptr0 x) m)
    );
  elim_vrewrite
    (emp `vrefine` varrayptr0_refine x `vdep` varrayptr0_payload x)
    (varrayptr0_rewrite x);
  let sq = elim_vdep
    (emp `vrefine` varrayptr0_refine x)
    (varrayptr0_payload x)
  in
  elim_vrefine emp (varrayptr0_refine x);
  let res = Ghost.hide (Some?.v x) in
  change_equal_slprop
    (varrayptr0_payload x sq)
    (AP.varrayptr res);
  res

let varrayptr_not_null
  x
=
  let r1 = elim_varrayptr x in
  let r2 = intro_varrayptr r1 in
  change_equal_slprop
    (varrayptr r2)
    (varrayptr x)

[@@__steel_reduce__]
let varrayptr_or_null0
  (#a: Type)
  (x: t a)
: Tot vprop
= if None? x
  then emp `vrewrite` (fun _ -> None <: option (v a))
  else varrayptr x `vrewrite` Some

let is_arrayptr_or_null x = hp_of (varrayptr_or_null0 x)
let arrayptr_or_null_sel x = fun h -> sel_of (varrayptr_or_null0 x) h

let intro_varrayptr_or_null_none
  #_ #a x
=
  intro_vrewrite emp (fun _ -> None <: option (v a));
  change_equal_slprop
    (emp `vrewrite` (fun _ -> None <: option (v a)))
    (varrayptr_or_null0 x);
  change_slprop_rel
    (varrayptr_or_null0 x)
    (varrayptr_or_null x)
    (fun m n -> m == n)
    (fun _ -> ())

let intro_varrayptr_or_null_some
  #_ #a x
=
  intro_vrewrite (varrayptr x) Some;
  change_equal_slprop
    (varrayptr x `vrewrite` Some)
    (varrayptr_or_null0 x);
  change_slprop_rel
    (varrayptr_or_null0 x)
    (varrayptr_or_null x)
    (fun m n -> m == n)
    (fun _ -> ())

let elim_varrayptr_or_null_some
  #_ #a x
=
  change_slprop_rel
    (varrayptr_or_null x)
    (varrayptr_or_null0 x)
    (fun m n -> m == n)
    (fun _ -> ());
  if None? x
  then begin
    change_equal_slprop
      (varrayptr_or_null0 x)
      (emp `vrewrite` (fun _ -> None <: option (v a)));
    elim_vrewrite emp (fun _ -> None <: option (v a));
    change_slprop_rel
      emp
      (varrayptr x)
      (fun _ _ -> False)
      (fun _ -> assert False)
  end else begin
    change_equal_slprop
      (varrayptr_or_null0 x)
      (varrayptr x `vrewrite` Some);
    elim_vrewrite (varrayptr x) Some
  end

let elim_varrayptr_or_null_none
  #_ #a x
=
  change_slprop_rel
    (varrayptr_or_null x)
    (varrayptr_or_null0 x)
    (fun m n -> m == n)
    (fun _ -> ());
  if None? x
  then begin
    change_equal_slprop
      (varrayptr_or_null0 x)
      (emp `vrewrite` (fun _ -> None <: option (v a)));
    elim_vrewrite emp (fun _ -> None <: option (v a))
  end else begin
    change_equal_slprop
      (varrayptr_or_null0 x)
      (varrayptr x `vrewrite` Some);
    elim_vrewrite (varrayptr x) Some;
    let z = elim_varrayptr x in
    change_slprop_rel
      (AP.varrayptr z)
      emp
      (fun _ _ -> False)
      (fun _ -> assert False)
  end

val is_null_lemma
  (#opened: _)
  (#a: Type)
  (x: t a)
: SteelGhost unit opened
    (varrayptr_or_null x)
    (fun _ -> varrayptr_or_null x)
    (fun _ -> True)
    (fun h res h' ->
      let s = h (varrayptr_or_null x) in
      h' (varrayptr_or_null x) == s /\
      None? s == g_is_null x
    )

let is_null_lemma
  #_ #a x
=
  if None? x
  then begin
    elim_varrayptr_or_null_none x;
    intro_varrayptr_or_null_none x
  end else begin
    elim_varrayptr_or_null_some x;
    intro_varrayptr_or_null_some x
  end

let is_null
  x
=
  is_null_lemma x;
  return (None? x)

let join
  al ar
=
  let al0 = elim_varrayptr al in
  let ar0 = elim_varrayptr ar in
  AP.join al0 ar0;
  let al1 = intro_varrayptr al0 in
  change_equal_slprop
    (varrayptr al1)
    (varrayptr al)

let split
  x i
=
  let x0 = elim_varrayptr x in
  let x1 = Some?.v x in
  change_equal_slprop
    (AP.varrayptr x0)
    (AP.varrayptr x1);
  let y1 = AP.split x1 i in
  let y0 = intro_varrayptr y1 in
  let y = Some y1 in
  change_equal_slprop
    (varrayptr y0)
    (varrayptr y);
  let x0' = intro_varrayptr x1 in
  change_equal_slprop
    (varrayptr x0')
    (varrayptr x);
  return y

let alloc
  x n
=
  let y = AP.alloc x n in
  let y0 = intro_varrayptr y in
  let y1 = Some y in
  change_equal_slprop
    (varrayptr y0)
    (varrayptr y1);
  return y1

let index
  r i
=
  let r0 = elim_varrayptr r in
  let r1 = Some?.v r in
  change_equal_slprop
    (AP.varrayptr r0)
    (AP.varrayptr r1);
  let res = AP.index r1 i in
  let r0 = intro_varrayptr r1 in
  change_equal_slprop
    (varrayptr r0)
    (varrayptr r);
  return res

let upd
  r i x
=
  let r0 = elim_varrayptr r in
  let r1 = Some?.v r in
  change_equal_slprop
    (AP.varrayptr r0)
    (AP.varrayptr r1);
  AP.upd r1 i x;
  let r0 = intro_varrayptr r1 in
  change_equal_slprop
    (varrayptr r0)
    (varrayptr r)

let free
  r
=
  let r0 = elim_varrayptr r in
  let r1 = Some?.v r in
  change_equal_slprop
    (AP.varrayptr r0)
    (AP.varrayptr r1);
  AP.free r1

let share
  r
=
  let r0 = elim_varrayptr r in
  let r1 = Some?.v r in
  change_equal_slprop
    (AP.varrayptr r0)
    (AP.varrayptr r1);
  let res1 = AP.share r1 in
  let res0 = intro_varrayptr res1 in
  let res = Some res1 in
  change_equal_slprop
    (varrayptr res0)
    (varrayptr res);
  let r0 = intro_varrayptr r1 in
  change_equal_slprop
    (varrayptr r0)
    (varrayptr r);
  return res

let gather
  r1 r2
=
  let r1' = elim_varrayptr r1 in
  let r2' = elim_varrayptr r2 in
  AP.gather r1' r2';
  let r = intro_varrayptr r1' in
  change_equal_slprop
    (varrayptr r)
    (varrayptr r1)
