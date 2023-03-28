module Steel.ST.C.Types.Array
open Steel.ST.GenElim
friend Steel.ST.C.Types.Base
friend Steel.ST.C.Types.Struct.Aux
open Steel.ST.C.Types.Struct.Aux

open Steel.C.Model.PCM

/// Base arrays (without decay: explicit array types as top-level arrays or struct/union fields of array type)

module GHR = Steel.ST.GhostHigherReference
module R = Steel.ST.C.Model.Ref
module HR = Steel.ST.HigherReference
module FX = FStar.FunctionalExtensionality
module A = Steel.ST.C.Model.Array

let base_array_t'
  (t: Type0)
  (n: Ghost.erased array_size_t)
: Tot Type0
= A.array_pcm_carrier t (Ghost.hide (Ghost.reveal n))

let base_array_t t _ n = base_array_t' t n

[@@noextract_to "krml"] // proof-only
let base_array_fd
  (#t: Type)
  (td: typedef t)
  (n: Ghost.erased array_size_t)
: Tot (field_description_gen_t (base_array_index_t n))
= {
    fd_nonempty = (let _ : base_array_index_t n = 0sz in ());
    fd_type = A.array_range t (Ghost.hide (Ghost.reveal n));
    fd_typedef = (fun _ -> td);
  }

[@@noextract_to "krml"]
let base_array1 (#t: Type0) (td: typedef t) (n: Ghost.erased array_size_t) : Tot (typedef (base_array_t' t n)) = struct1 (base_array_fd td n)

let base_array0 tn td n = base_array1 td n

let base_array_index a i = a i

let base_array_eq #_ #_ #n a1 a2 =
  assert (a1 `FX.feq` a2 <==> (forall (i: base_array_index_t n) . a1 i == a2 i));
  a1 `FX.feq` a2

let mk_base_array _ n v = A.array_pcm_carrier_of_seq n v

let mk_base_array_index _ _ _ _ = ()

let base_array_fractionable a td = ()

let base_array_mk_fraction a td p i = ()

let base_array_index_unknown tn n td i = ()

let base_array_index_uninitialized tn n td i = ()

let base_array_index_full td x = ()

let base_array_index_t' (n: Ghost.erased array_size_t) : Tot eqtype =
  A.array_domain (Ghost.hide (Ghost.reveal n))

let base_array_index_t'_eq
  (n: array_size_t)
: Lemma
  (base_array_index_t n == base_array_index_t' n)
  [SMTPat (base_array_index_t n)]
= // syntactic equality of refinement types
  assert (base_array_index_t n == base_array_index_t' n) by (FStar.Tactics.trefl ())

let array_index_as_field_marker
  (n: Ghost.erased array_size_t)
  (i: SZ.t)
  (j: base_array_index_t' n)
: Tot (base_array_index_t' n)
= j

#set-options "--print_implicits"

let base_array1_eq
  (#t: Type)
  (n: Ghost.erased array_size_t)
  (td: typedef t)
: Lemma
  (ref (base_array1 td n) == ref (struct1 #(base_array_index_t' n) (base_array_fd td n)))
//  [SMTPat (ref (base_array1 td n))]
= () // assert (ref (base_array1 td n) == ref (struct1 #(base_array_index_t' n) (base_array_fd td n))) by (FStar.Tactics.trefl ())

[@@__reduce__]
let has_base_array_cell_as_struct_field0
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (j: base_array_index_t' n)
  (r': ref td)
: Tot vprop
= has_struct_field1 #(base_array_index_t' n) #(base_array_fd td n) r (array_index_as_field_marker n i j) r'

let has_base_array_cell_as_struct_field
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (j: base_array_index_t' n)
  (r': ref td)
: Tot vprop
= has_base_array_cell_as_struct_field0 r i j r'

[@@__reduce__]
let has_base_array_cell0
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r': ref td)
: Tot vprop
= exists_ (fun j ->
    has_base_array_cell_as_struct_field r i j r' `star`
    pure (i == j)
  )

let has_base_array_cell1
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r': ref td)
: Tot vprop
= has_base_array_cell0 r i r'

let has_base_array_cell
  r i r'
= has_base_array_cell0 r i r'

let has_base_array_cell_post
  r i r'
= rewrite (has_base_array_cell r i r') (has_base_array_cell0 r i r');
  let _ = gen_elim () in
  rewrite (has_base_array_cell0 r i r') (has_base_array_cell r i r')

let has_base_array_cell_dup'
  (#opened: _)
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r': ref td)
: STGhostT unit opened
    (has_base_array_cell1 r i r')
    (fun _ -> has_base_array_cell1 r i r' `star` has_base_array_cell1 r i r')
= rewrite (has_base_array_cell1 r i r') (has_base_array_cell0 r i r');
  let _ = gen_elim () in
  has_struct_field_dup'  #_ #(base_array_index_t' n) #(base_array_fd td n) (r) _ _;
  rewrite (has_base_array_cell0 r i r') (has_base_array_cell1 r i r');
  noop ();
  rewrite (has_base_array_cell0 r i r') (has_base_array_cell1 r i r')

let has_base_array_cell_dup
  r i r'
= has_base_array_cell_dup' r i r'

let has_base_array_cell_inj'
  (#opened: _)
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r1 r2: ref td)
: STGhostT unit opened
    (has_base_array_cell1 r i r1 `star` has_base_array_cell1 r i r2)
    (fun _ -> has_base_array_cell1 r i r1 `star` has_base_array_cell1 r i r2 `star` ref_equiv r1 r2)
= rewrite (has_base_array_cell1 r i r1) (has_base_array_cell0 r i r1);
  let _ = gen_elim () in
  let j = vpattern_replace (fun j -> has_base_array_cell_as_struct_field r i j _) in
  rewrite (has_base_array_cell1 r i r2) (has_base_array_cell0 r i r2);
  let _ = gen_elim () in
  vpattern_rewrite (fun j' -> has_base_array_cell_as_struct_field r i j _ `star` has_base_array_cell_as_struct_field r i j' _) j;
  has_struct_field_inj' #_ #(base_array_index_t' n) #(base_array_fd td n) (r) _ r1 r2;
  rewrite (has_base_array_cell0 r i r2) (has_base_array_cell1 r i r2);
  rewrite (has_base_array_cell0 r i r1) (has_base_array_cell1 r i r1)

let has_base_array_cell_inj
  r i r1 r2
= has_base_array_cell_inj' r i r1 r2

let has_base_array_cell_equiv_from'
  (#opened: _)
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r1 r2: ref (base_array1 td n))
  (i: SZ.t)
  (r': ref td)
: STGhostT unit opened
    (has_base_array_cell1 r1 i r' `star` ref_equiv r1 r2)
    (fun _ -> has_base_array_cell1 r2 i r' `star` ref_equiv r1 r2)
= rewrite (has_base_array_cell1 r1 i r') (has_base_array_cell0 r1 i r');
  let _ = gen_elim () in
  has_struct_field_equiv_from'  #_ #(base_array_index_t' n) #(base_array_fd td n) (r1) _ r' (r2);
  rewrite (has_base_array_cell0 r2 i r') (has_base_array_cell1 r2 i r')

let has_base_array_cell_equiv_from
  r1 r2 i r'
= has_base_array_cell_equiv_from' r1 r2 i r'

let has_base_array_cell_equiv_to'
  (#opened: _)
  (#t: Type)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (i: SZ.t)
  (r1 r2: ref td)
: STGhostT unit opened
    (has_base_array_cell1 r i r1 `star` ref_equiv r1 r2)
    (fun _ -> has_base_array_cell1 r i r2 `star` ref_equiv r1 r2)
= rewrite (has_base_array_cell1 r i r1) (has_base_array_cell0 r i r1);
  let _ = gen_elim () in
  has_struct_field_equiv_to'  #_ #(base_array_index_t' n) #(base_array_fd td n) r _ r1 (r2);
  rewrite (has_base_array_cell0 r i r2) (has_base_array_cell1 r i r2)

let has_base_array_cell_equiv_to
  r i r1 r2
= has_base_array_cell_equiv_to' r i r1 r2

/// Array pointers (with decay)

noeq
type array_ptr_gen t = {
  ar_is_null: Ghost.erased bool;
  ar_base_size: Ghost.erased array_size_t;
  ar_base: ptr_gen (base_array_t' t ar_base_size);
  ar_offset: SZ.t;
  ar_prf: squash (
    SZ.v ar_offset <= SZ.v ar_base_size /\
    (Ghost.reveal ar_is_null == true <==> ar_base == void_null) /\
    (ar_base == void_null ==> (SZ.v ar_base_size == 1 /\ SZ.v ar_offset == 0))
  );
}
let null_array_ptr td = {
  ar_is_null = true;
  ar_base_size = 1sz;
  ar_base = null_gen _;
  ar_offset = 0sz;
  ar_prf = ();
}
let g_array_ptr_is_null a = a.ar_is_null 
let array_ref_base_size ar = if ar.ar_is_null then 0sz else ar.ar_base_size
let has_array_ref_base ar r = ar.ar_base == r
let has_array_ref_base_inj ar r1 r2 = ()
let array_ref_offset ar = ar.ar_offset
let array_ref_base_offset_inj a1 r1 a2 r2 = ()

let base_array_pcm_eq
  (#t: Type)
  (td: typedef t)
  (n: Ghost.erased array_size_t)
: Lemma
  (A.array_pcm td.pcm (Ghost.hide (Ghost.reveal n)) == (base_array1 td n).pcm)
  [SMTPat (base_array1 td n).pcm]
= pcm0_ext (A.array_pcm td.pcm (Ghost.hide (Ghost.reveal n))) (base_array1 td n).pcm
    (fun _ _ -> ())
    (fun x1 x2 ->
      assert (op (A.array_pcm td.pcm (Ghost.hide (Ghost.reveal n))) x1 x2 `FX.feq` op (base_array1 td n).pcm x1 x2)
    )
    (fun _ -> ())
    ()

let model_array_of_array_precond
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (base: ref0_v)
: GTot prop
=
  base.t == base_array_t' t (array_ptr_of a).ar_base_size /\
  base.td == base_array1 td (array_ptr_of a).ar_base_size
      
[@@noextract_to "krml"] // proof-only
let model_array_of_array
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (base: ref0_v)
: Pure (A.array base.base td.pcm)
    (requires (
      model_array_of_array_precond a base
    ))
    (ensures (fun _ -> True))
= let (| al, len |) = a in
  {
    base_len = Ghost.hide (Ghost.reveal al.ar_base_size);
    base = base.ref;
    offset = al.ar_offset;
    len = len;
    prf = ();
  }

let has_model_array_of_array
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (base: ref0_v)
  (ar: A.array base.base td.pcm)
: GTot prop
= 
  model_array_of_array_precond a base /\
  model_array_of_array a base == ar

[@@__reduce__]
let array_pts_to0
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
: Tot vprop
= exists_ (fun br -> exists_ (fun p -> exists_ (fun (a: A.array br.base td.pcm) ->
    HR.pts_to (array_ptr_of r).ar_base p br `star`
    A.pts_to a v `star`
    pure (has_model_array_of_array r br a)
  )))

let array_pts_to r v =
  array_pts_to0 r v

let array_pts_to_intro
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
  (br: ref0_v)
  (p: P.perm)
  (sq: squash (model_array_of_array_precond r br))
: STGhostT unit opened
    (
      HR.pts_to (array_ptr_of r).ar_base p br `star`
      A.pts_to (model_array_of_array r br) v
    )
    (fun _ -> array_pts_to r v)
= noop ();
  intro_exists p (fun p -> exists_ (fun (a: A.array br.base td.pcm) ->
    HR.pts_to (array_ptr_of r).ar_base p br `star`
    A.pts_to a v `star`
    pure (has_model_array_of_array r br a)
  ));
  rewrite (array_pts_to0 r v) (array_pts_to r v)

let array_pts_to_res_t
  (#t: Type)
  (#td: typedef t)
  (r: array td)
: Tot Type
= (br: Ghost.erased ref0_v { model_array_of_array_precond r br })

let array_pts_to_elim
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
: STGhostT (array_pts_to_res_t r) opened
    (array_pts_to r v)
    (fun br -> exists_ (fun p ->
      HR.pts_to (array_ptr_of r).ar_base p br `star`
      A.pts_to (model_array_of_array r br) v
    ))
= rewrite (array_pts_to _ _) (array_pts_to0 r v);
  let _ = gen_elim () in
  let p = vpattern_replace (fun p -> HR.pts_to _ p _) in
  let br0 = vpattern_replace_erased (HR.pts_to _ _) in
  let br : array_pts_to_res_t r = br0 in
  rewrite (HR.pts_to _ _ _) (HR.pts_to (array_ptr_of r).ar_base p br);
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array r br) v);
  br

let array_ptr_is_null
  r _
= return (HR.is_null r.ar_base)

let array_pts_to_length r v =
  let _ = array_pts_to_elim _ _ in
  let _ = gen_elim () in
  let _ = A.pts_to_length _ _ in
  array_pts_to_intro _ _ _ _ ()

let has_array_of_base'
  (#t: Type)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array1 td n))
  (a: array td)
: GTot prop
=   let (| al, len |) = a in
    array_ref_base_size al == n /\
    al.ar_base == r /\
    array_ref_offset al == 0sz /\
    Ghost.reveal len == n

#push-options "--z3rlimit 16 --split_queries"

#restart-solver

let base_array_index' (#t: Type0) (#n: array_size_t) (a: base_array_t' t n)
(i: base_array_index_t n) : GTot t
= a i

let seq_of_base_array0
  (#t: Type)
  (#n: array_size_t)
  (v: base_array_t' t n)
: GTot (Seq.lseq t (SZ.v n))
= Seq.init_ghost (SZ.v n) (fun i -> base_array_index' v (SZ.uint_to_t i))

#pop-options


#push-options "--z3rlimit 16"
#restart-solver

let ghost_array_of_base_focus'
  (#t: Type)
  (#opened: _)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t' t n))
  (r: ref (base_array1 td n))
  (a: array td)
: STGhost unit opened
    (pts_to r v)
    (fun _ -> array_pts_to a (seq_of_base_array0 v))
    (has_array_of_base' r a)
    (fun _ -> True)
= rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  let w = vpattern_replace (HR.pts_to r _) in
  let rr = get_ref r in
  assert ((model_array_of_array a w).base == rr);
  rewrite (r_pts_to _ _) (R.pts_to (model_array_of_array a w).base v);
  assert (seq_of_base_array0 v `Seq.equal` A.seq_of_array_pcm_carrier v);
  A.array_pcm_carrier_of_seq_of_array_pcm_carrier v;
  A.pts_to_intro_from_base (model_array_of_array a w)  v (seq_of_base_array0 v);
  let p = vpattern_replace (fun p -> HR.pts_to _ p _) in
  rewrite (HR.pts_to _ _ _) (HR.pts_to (array_ptr_of a).ar_base p w);
  array_pts_to_intro a (seq_of_base_array0 v) w _ ()

let ghost_array_of_base_focus
  #_ #_ #_ #_ #td #v r a
= ghost_array_of_base_focus' r a

#pop-options

let ghost_array_of_base
  #_ #tn #_ #n #td #v r
=
  let al : array_ref td = {
    ar_is_null = false;
    ar_base_size = n;
    ar_base = r;
    ar_offset = 0sz;
    ar_prf = ();
  }
  in
  let a : (a: Ghost.erased (array td) { has_array_of_base r a }) = (| al, Ghost.hide (Ghost.reveal n) |) in
  ghost_array_of_base_focus r a;
  a

[@@noextract_to "krml"] // primitive
let array_of_base0
  (#t: Type)
  (#opened: _)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t' t n))
  (r: ref (base_array1 td n))
: STAtomicBase (array td) false opened Unobservable
    (pts_to r v)
    (fun a -> array_pts_to a (seq_of_base_array0 v))
    (True)
    (fun a -> has_array_of_base' r a)
=
  let al : array_ref td = {
    ar_is_null = false;
    ar_base_size = n;
    ar_base = r;
    ar_offset = 0sz;
    ar_prf = ();
  }
  in
  let a : (a: array td { has_array_of_base' r a }) = (| al, Ghost.hide (Ghost.reveal n) |) in
  ghost_array_of_base_focus' r a;
  return a

let array_ref_of_base
  #_ #tn #_ #n #td #v r
=
  let ar = array_of_base0 r in
  let a : array_ref td = array_ptr_of ar in
  return a

#push-options "--z3rlimit 64"
#restart-solver

let unarray_of_base0
  (#t: Type)
  (#opened: _)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: ref (base_array1 td n))
  (a: array td)
: STGhost (Ghost.erased (base_array_t' t n)) opened
    (array_pts_to a v)
    (fun v' -> pts_to r v')
    (
      has_array_of_base' r a
    )
    (fun v' -> Ghost.reveal v `Seq.equal` seq_of_base_array0 v')
= let ba = array_pts_to_elim a v in
  let _ = gen_elim () in
  let p = vpattern_replace (fun p -> HR.pts_to _ p _) in
  rewrite (HR.pts_to _ _ _) (HR.pts_to r p ba);
  let m = model_array_of_array a ba in
  rewrite (A.pts_to _ _) (A.pts_to m v);
  let y : Ghost.erased (A.array_pcm_carrier t m.base_len) = A.pts_to_elim_to_base m v in
  let rr : R.ref ba.base (base_array1 td n).pcm = coerce_eq () m.base in
  let y' : Ghost.erased (base_array_t' t n) = Ghost.hide (Ghost.reveal y) in
  rewrite (R.pts_to _ _) (r_pts_to rr y');
  pts_to_intro r p ba rr y';
  y'

#pop-options

let unarray_of_base
  #t #tn #_ #n #td #v r a
= unarray_of_base0 r a

[@@ __reduce__ ]
let freeable_array0
  (#t: Type) (#td: typedef t) (a: array td)
: Tot vprop
= freeable #_ #(base_array1 #t td (array_ptr_of a).ar_base_size) (array_ptr_of a).ar_base `star`
  pure (has_array_of_base' (array_ptr_of a).ar_base a)

let freeable_array
  a
= freeable_array0 a

let array_ptr_alloc
  #t td sz
= let base = alloc (base_array1 td sz) in
  if is_null base
  then begin
    noop ();
    let a = null_array_ptr td in
    let ar : array_or_null td = (| a, Ghost.hide 0sz |) in
    rewrite (pts_to_or_null _ _) (array_pts_to_or_null ar (seq_of_base_array0 (uninitialized (base_array1 td sz))));
    rewrite (freeable_or_null _) (freeable_or_null_array ar);
    return a
  end else begin
    noop ();
    let sq: squash (~ (base == null _)) = () in
    noop ();
    rewrite (pts_to_or_null _ _) (pts_to base (uninitialized (base_array1 td sz)));
    let ar : array td = array_of_base0 base in
    rewrite (array_pts_to ar _) (array_pts_to_or_null ar (seq_of_base_array0 (uninitialized (base_array1 td sz))));
    let a = array_ptr_of ar in
    rewrite (freeable_or_null _) (freeable #_ #(base_array1 #t td (array_ptr_of ar).ar_base_size) (array_ptr_of ar).ar_base);
    rewrite (freeable_array0 ar) (freeable_or_null_array ar);
    return a
  end

#push-options "--z3rlimit 16"
#restart-solver

let full_seq_seq_of_base_array'
  (#t: Type0) (td: typedef t) (#n: array_size_t)
  (b: base_array_t' t n)
: Lemma
  (ensures (full_seq td (seq_of_base_array0 b) <==> full (base_array1 td n) b))
= assert (forall (i: base_array_index_t n) . base_array_index' b i == Seq.index (seq_of_base_array0 b) (SZ.v i))

let array_ref_free
  #t #td #s a len
= rewrite (freeable_array _) (freeable_array0 (| a, len |));
  elim_pure _;
  let len0 : Ghost.erased array_size_t = Ghost.hide (Ghost.reveal len) in
  let r : ref (base_array1 td len0) = a.ar_base in
  array_pts_to_length _ _;
  let s' = unarray_of_base0 r (| a, len |) in
  full_seq_seq_of_base_array' td s';
  rewrite (pts_to _ _) (pts_to r s');
  rewrite (freeable _) (freeable r);
  free r

#pop-options

(*
let has_array_of_ref
  r a
= TD.type_of_token (array_ptr_of a).ar_base_size_token == unit /\
  model_array_of_array a == A.g_array_of_ref (coerce _ (Some?.v r).ref)

let has_array_of_ref_inj
  r a1 a2
= TD.type_of_token_inj (array_ptr_of a1).ar_base_size_token (array_ptr_of a2).ar_base_size_token;
  TD.type_of_token_inj (Some?.v (array_ptr_of a1).ar_base).dest (Some?.v (array_ptr_of a2).ar_base).dest

let ghost_array_of_ref_focus
  #t #_ #td #v r a
= let mr : R.ref td.pcm = (Some?.v r).ref in
  rewrite_slprop (pts_to _ _) (R.pts_to mr v) (fun _ -> ());
  let ma = A.ghost_array_of_ref mr in
  rewrite_slprop (A.pts_to _ _) (array_pts_to _ _) (fun _ -> ())

let ghost_array_of_ref
  #t #_ #td #v r
= let mr : R.ref td.pcm = (Some?.v r).ref in
  let ma = A.g_array_of_ref mr in
  let tok_unit = TD.get_token unit in
  let tok_array = TD.get_token (A.array_pcm_carrier t 1sz) in
  let ar = {
    ar_base_size_token = tok_unit;
    ar_base_size = 1sz;
    ar_base = Some ({
      dest = tok_array;
      typedef = base_array0 unit td 1sz;
      ref = coerce _ ma.base;
    });
    ar_offset = 0sz;
  }
  in
  let res: (a: Ghost.erased (array td) { has_array_of_ref r a }) = Ghost.hide (| ar, Ghost.hide 1sz |) in
  ghost_array_of_ref_focus r res;
  res

let array_ref_of_ref
  #t #_ #td #v r
= let mr : R.ref td.pcm = (Some?.v r).ref in
  rewrite_slprop (pts_to _ _) (R.pts_to mr v) (fun _ -> ());
  let ma = A.array_of_ref mr in
  let tok_unit = TD.get_token unit in
  let tok_array = TD.get_token (A.array_pcm_carrier t 1sz) in
  let res = {
    ar_base_size_token = tok_unit;
    ar_base_size = 1sz;
    ar_base = Some ({
      dest = tok_array;
      typedef = base_array0 unit td 1sz;
      ref = coerce _ ma.base;
    });
    ar_offset = 0sz;
  }
  in
  rewrite_slprop (A.pts_to _ _) (array_pts_to _ _) (fun _ -> ());
  return res

let unarray_of_ref = magic ()
*)

[@@noextract_to "krml"]
let array_index_as_base_array_index_marker
  (index: SZ.t)
  (base_index: SZ.t)
: Tot SZ.t
= base_index

[@@__reduce__]
let has_array_cell0
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: Tot vprop
= exists_ (fun (j: SZ.t) ->
    has_base_array_cell1 (array_ptr_of a).ar_base (array_index_as_base_array_index_marker i j) r `star`
    pure (
      SZ.v j == SZ.v ((array_ptr_of a).ar_offset) + SZ.v i /\
      SZ.v i < SZ.v (dsnd a)
    )
  )

let has_array_cell1
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: Tot vprop
= has_array_cell0 a i r

let has_array_cell
  a i r
= has_array_cell0 a i r

let has_array_cell_post
  a i r
= rewrite (has_array_cell a i r) (has_array_cell0 a i r);
  let _ = gen_elim () in
  rewrite (has_array_cell0 a i r) (has_array_cell a i r)

let has_array_cell_has_base_array_cell
  a i r br
= rewrite (has_array_cell a i r) (has_array_cell0 a i r);
  let _ = gen_elim () in
  let j = vpattern_replace_erased (fun j -> has_base_array_cell1 _ j r) in
  rewrite (has_base_array_cell1 _ _ _) (has_base_array_cell br j r);
  j

let has_base_array_cell_has_array_cell
  a i r br
= let j : Ghost.erased SZ.t = Ghost.hide (i `SZ.sub` (array_ptr_of a).ar_offset) in
  rewrite (has_base_array_cell br i r) (has_base_array_cell1 (array_ptr_of a).ar_base (array_index_as_base_array_index_marker j i) r);
  rewrite (has_array_cell0 a j r) (has_array_cell a j r);
  j

let has_array_cell_inj
  #_ #_ #td a i r1 r2
= has_array_cell_post a i r1;
  let br : ref (base_array0 unit (* dummy *) td (array_ref_base_size (array_ptr_of a))) = (array_ptr_of a).ar_base in
  let j1 = has_array_cell_has_base_array_cell a i r1 br in
  let j2 = has_array_cell_has_base_array_cell a i r2 br in
  vpattern_rewrite (fun j2 -> has_base_array_cell _ j2 r2) j1;
  has_base_array_cell_inj br j1 r1 r2;
  let _ = has_base_array_cell_has_array_cell a j1 r1 br in
  vpattern_rewrite (fun i -> has_array_cell _ i r1) i;
  let _ = has_base_array_cell_has_array_cell a j1 r2 br in
  vpattern_rewrite (fun i -> has_array_cell _ i r2) i
  

#restart-solver
let struct_field_eq_cell
  (#t: Type)
  (td: typedef t)
  (n: array_size_t)
  (k: base_array_index_t n)
: Lemma
  (Steel.ST.C.Model.Struct.struct_field (struct_field_pcm (base_array_fd td n)) k == A.cell td.pcm n k)
= // assert_norm (A.array_domain n == base_array_index_t n);
  Steel.ST.C.Model.Struct.struct_field_ext #(A.array_domain n) #(A.array_range t n) (struct_field_pcm (base_array_fd td n)) (A.array_elements_pcm td.pcm n) (fun _ -> ()) k

(*
#push-options "--split_queries --z3rlimit 16"

#restart-solver
let has_array_cell_array_of_ref
  #_ #td r a
= assert_norm (SZ.v 0sz == 0);
  assert_norm (SZ.v 1sz == 1);
  A.ref_of_array_of_ref (Some?.v r).ref;
  A.ref_of_array_of_ref_base (Some?.v r).ref;
  assert (Ghost.reveal (dsnd a) == 1sz);
  assert ((array_ptr_of a).ar_offset == 0sz);
  struct_field_eq_cell td 1sz 0sz;
  assert (has_base_array_cell0 (array_ref_base (array_ptr_of a)) (array_ref_offset (array_ptr_of a) `SZ.add` 0sz) r)

#pop-options
*)

let has_struct_field_gen
  (#field_t: eqtype)
  (fields: field_description_gen_t field_t)
  (r: ref0_v)
  (field: field_t)
  (r': ref0_v)
: GTot prop
= r'.base == r.base /\
  r.t == struct_t1 fields /\
  r.td == struct1 fields /\
  r'.t == fields.fd_type field /\
  r'.td == fields.fd_typedef field /\
  r'.ref == coerce_eq () (R.ref_focus r.ref (Steel.ST.C.Model.Struct.struct_field (struct_field_pcm fields) field))


let has_struct_field1_intro
  (#opened: _)
  (#field_t: eqtype)
  (#fields: field_description_gen_t field_t)
  (r: ref (struct1 fields))
  (field: field_t)
  (r': ref (fields.fd_typedef field))
  (p: P.perm)
  (w: ref0_v)
  (p': P.perm)
  (w': ref0_v)
  ()
: STGhost unit opened
    (HR.pts_to r p w `star` HR.pts_to r' p' w')
    (fun _ ->
      has_struct_field1 r field r'
    )
    (
      has_struct_field_gen fields w field w'
    )
    (fun _ -> True)
= noop ();
  rewrite
    (has_struct_field0 r field r')
    (has_struct_field1 r field r')

let has_array_cell_drop
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (#p': P.perm)
  (#b': ref0_v)
  (i: SZ.t)
  (r: ref td)
: STGhostT unit opened
    (has_array_cell1 a i r `star`
      HR.pts_to r p' b'
    )
    (fun _ -> has_array_cell1 a i r)
= rewrite (has_array_cell1 a i r) (has_array_cell0 a i r);
  let _ = gen_elim () in
  let j = vpattern_replace (fun j -> has_base_array_cell1 _ j _) in
  rewrite (has_base_array_cell1 (array_ptr_of a).ar_base j r) (has_base_array_cell0 (array_ptr_of a).ar_base j r);
  let _ = gen_elim () in
  let j' : base_array_index_t' (array_ptr_of a).ar_base_size = vpattern_replace (fun j' -> has_base_array_cell_as_struct_field _ _ j' _) in
  rewrite (has_base_array_cell_as_struct_field (array_ptr_of a).ar_base j j' r) (has_struct_field0 #(base_array_index_t' (array_ptr_of a).ar_base_size) #(base_array_fd td (array_ptr_of a).ar_base_size) (array_ptr_of a).ar_base j' r);
  let _ = gen_elim () in
  HR.gather p' r;
  has_struct_field1_intro
    #_ #(base_array_index_t' (array_ptr_of a).ar_base_size) #(base_array_fd td (array_ptr_of a).ar_base_size) (array_ptr_of a).ar_base j' r _ _ _ _ ();
  rewrite
    (has_struct_field1 #(base_array_index_t' (array_ptr_of a).ar_base_size) #(base_array_fd td (array_ptr_of a).ar_base_size) (array_ptr_of a).ar_base j' r)
    (has_base_array_cell_as_struct_field (array_ptr_of a).ar_base j j' r);
  rewrite
    (has_base_array_cell0 (array_ptr_of a).ar_base j r)
    (has_base_array_cell1 (array_ptr_of a).ar_base (array_index_as_base_array_index_marker i j) r);
  rewrite
    (has_array_cell0 a i r)
    (has_array_cell a i r)

let has_array_cell_elim
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#p: P.perm)
  (a: array td)
  (#b: ref0_v)
  (i: SZ.t)
  (r: ref td)
: STGhost (Ghost.erased (ref0_v)) opened
    (has_array_cell1 a i r `star`
      HR.pts_to (array_ptr_of a).ar_base p b
    )
    (fun b' -> has_array_cell1 a i r `star`
      exists_ (fun p -> exists_ (fun p' ->
        HR.pts_to (array_ptr_of a).ar_base p b `star`
        HR.pts_to r p' b'
    )))
    True
    (fun b' ->
      model_array_of_array_precond a b /\
      b'.base == b.base /\
      b'.t == t /\
      b'.td == td /\
      begin let ar = model_array_of_array a b in
        SZ.v i < SZ.v ar.len /\
        b'.ref == R.ref_focus (A.ref_of_array ar) (A.cell td.pcm ar.len i)
      end
    )
= 
  rewrite (has_array_cell1 a i r) (has_array_cell0 a i r);
  let _ = gen_elim () in
  let j = vpattern_replace (fun j -> has_base_array_cell1 _ j _) in
  rewrite (has_base_array_cell1 (array_ptr_of a).ar_base j r) (has_base_array_cell0 (array_ptr_of a).ar_base j r);
  let _ = gen_elim () in
  let j' : base_array_index_t' (array_ptr_of a).ar_base_size = vpattern_replace (fun j' -> has_base_array_cell_as_struct_field _ _ j' _) in
  rewrite (has_base_array_cell_as_struct_field (array_ptr_of a).ar_base j j' r) (has_struct_field0 #(base_array_index_t' (array_ptr_of a).ar_base_size) #(base_array_fd td (array_ptr_of a).ar_base_size) (array_ptr_of a).ar_base j' r);
  let _ = gen_elim () in
  hr_gather b (array_ptr_of a).ar_base;
  HR.share r;
  HR.share (array_ptr_of a).ar_base;
  has_struct_field1_intro #_ #(base_array_index_t' (array_ptr_of a).ar_base_size) #(base_array_fd td (array_ptr_of a).ar_base_size) (array_ptr_of a).ar_base j' r _ _ _ _ ();
  rewrite (has_struct_field1 #(base_array_index_t' (array_ptr_of a).ar_base_size) #(base_array_fd td (array_ptr_of a).ar_base_size) (array_ptr_of a).ar_base j' r) (has_base_array_cell_as_struct_field (array_ptr_of a).ar_base j j' r);
  rewrite
    (has_base_array_cell0 (array_ptr_of a).ar_base j r)
    (has_base_array_cell1 (array_ptr_of a).ar_base (array_index_as_base_array_index_marker i j) r);
  rewrite
    (has_array_cell0 a i r)
    (has_array_cell a i r);
  A.ref_of_array_eq (model_array_of_array a b) i;
  struct_field_eq_cell td (array_ptr_of a).ar_base_size j';
  let b' = vpattern_replace_erased (HR.pts_to r _) in
  noop ();
  b'

let ghost_array_cell_focus
  #_ #_ #td #s a i r
= rewrite (array_pts_to a s) (array_pts_to0 a s);
  let _ = gen_elim () in
  let b = vpattern_replace (HR.pts_to (array_ptr_of a).ar_base _) in
  let r' = has_array_cell_elim a i r in
  let _ = gen_elim () in
  let _ = A.g_focus_cell _ _ i () in
  pts_to_intro_rewrite r _ (Seq.index s (SZ.v i));
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array a b) (Seq.upd s (SZ.v i) (unknown td)));
  array_pts_to_intro a (Seq.upd s (SZ.v i) (unknown td)) _ _ ()

let has_array_cell_intro
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#p: P.perm)
  (a: array td)
  (#b: ref0_v)
  (#p': P.perm)
  (#b': ref0_v)
  (i: SZ.t)
  (r: ref td)
: STGhost unit opened
    (HR.pts_to (array_ptr_of a).ar_base p b `star`
      HR.pts_to r p' b'
    )
    (fun _ -> has_array_cell1 a i r)
    (
      model_array_of_array_precond a b /\
      begin let ar = model_array_of_array a b in
      SZ.v i < SZ.v ar.len /\
      b'.base == b.base /\
      b'.t == t /\
      b'.td == td /\
      b'.ref == R.ref_focus (A.ref_of_array ar) (A.cell td.pcm ar.len i)
      end
    )
    (fun _ -> True)
= 
  A.ref_of_array_eq (model_array_of_array a b) i;
  let j : base_array_index_t' (array_ptr_of a).ar_base_size = (array_ptr_of a).ar_offset `SZ.add` i in
  struct_field_eq_cell td (array_ptr_of a).ar_base_size j;
  has_struct_field1_intro #_ #(base_array_index_t' (array_ptr_of a).ar_base_size) #(base_array_fd td (array_ptr_of a).ar_base_size) (array_ptr_of a).ar_base j r _ _ _ _ ();
  rewrite (has_struct_field1 #(base_array_index_t' (array_ptr_of a).ar_base_size) #(base_array_fd td (array_ptr_of a).ar_base_size) (array_ptr_of a).ar_base j r) (has_base_array_cell_as_struct_field (array_ptr_of a).ar_base j j r);
  rewrite
    (has_base_array_cell0 (array_ptr_of a).ar_base j r)
    (has_base_array_cell1 (array_ptr_of a).ar_base (array_index_as_base_array_index_marker i j) r);
  rewrite
    (has_array_cell0 a i r)
    (has_array_cell a i r)

let ghost_array_cell
  #_ #_ #td #s a i
= array_pts_to_length _ _;
  let b = array_pts_to_elim a s in
  let _ = gen_elim () in
  HR.share _;
  array_pts_to_intro a s _ _ ();
  let ar = model_array_of_array a b in
  let b' = {
    t = _;
    td = td;
    base = b.base;
    ref = R.ref_focus (A.ref_of_array ar) (A.cell td.pcm ar.len i);
  }
  in
  let ghr = GHR.alloc b' in
  GHR.reveal_pts_to ghr P.full_perm b';
  let hr = GHR.reveal_ref ghr in
  rewrite_equiv (GHR.pts_to _ _ _) (HR.pts_to hr P.full_perm b');
  HR.pts_to_not_null hr;
  let r : (r: Ghost.erased (ref td) { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) }) = hr in
  vpattern_rewrite (fun hr -> HR.pts_to hr P.full_perm b') r;
  has_array_cell_intro a i r;
  let _ = ghost_array_cell_focus a i r in
  noop ();
  r

[@@ noextract_to "krml"]
let array_cell0
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: ST (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) })
    (array_pts_to a s)
    (fun r -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell a i r)
    (
      (SZ.v i < Seq.length s \/ SZ.v i < SZ.v (dsnd a))
    )
    (fun _ -> True)
= array_pts_to_length _ _;
  let _ = array_pts_to_elim a s in
  let _ = gen_elim () in
  HR.share _;
  array_pts_to_intro a s _ _ ();
  let b = HR.read (array_ptr_of a).ar_base in
  vpattern_rewrite (HR.pts_to (array_ptr_of a).ar_base _) b;
  let ar = model_array_of_array a b in
  A.ref_of_array_eq ar i;
  let b' = {
    t = _;
    td = td;
    base = b.base;
    ref = R.ref_focus ar.base (A.cell td.pcm ar.base_len (ar.offset `SZ.add`  i));
  }
  in
  let hr = HR.alloc b' in
  HR.pts_to_not_null hr;
  let r : (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) }) = hr in
  vpattern_rewrite (fun hr -> HR.pts_to hr P.full_perm b') r;
  has_array_cell_intro a i r;
  let _ = ghost_array_cell_focus a i r in
  noop ();
  return r

let array_ref_cell
  #_ #td #s a len i
= let r0 : (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd ((| a, len |) <: array td)) }) = array_cell0 _ _ in
  let r : (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v len }) = r0 in
  vpattern_rewrite (fun r -> pts_to r _) r;
  vpattern_rewrite (has_array_cell _ _) r;
  noop ();
  return r

let ar_unfocus_cell
  (#opened: _)
  (#base_t #base_t': Type)
  (#t: Type)
  (#p: pcm t)
  (r: A.array base_t p)
  (s: Seq.seq t)
  (i: SZ.t)
  (r': R.ref base_t' p)
  (v: t)
  (sq: squash (SZ.v i < SZ.v r.len /\ SZ.v i < Seq.length s))
: STGhost unit opened
    (A.pts_to r s `star` R.pts_to r' v)
    (fun _ -> A.pts_to r (Seq.upd s (SZ.v i) v))
    (
      base_t' == base_t /\
      r' == R.ref_focus (A.ref_of_array r) (A.cell p r.len i) /\
      Seq.index s (SZ.v i) == one p
    )
    (fun _ -> True)
= let r1' : R.ref base_t p = coerce_eq () r' in
  rewrite (R.pts_to r' v) (R.pts_to r1' v);
  A.unfocus_cell r s i r1' v ()

let unarray_cell
  #_ #_ #td #s #v a i r
= array_pts_to_length _ _;
  let b = array_pts_to_elim a s in
  let _ = gen_elim () in
  let w = has_array_cell_elim a i r in
  let _ = gen_elim () in
  rewrite (pts_to r v) (pts_to0 r v);
  let _ = gen_elim () in
  hr_gather (Ghost.reveal w) r;
  ar_unfocus_cell _ _ i _ _ ();
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array a b) (Seq.upd s (SZ.v i) v));
  array_pts_to_intro a (Seq.upd s (SZ.v i) v) _ _ ();
  has_array_cell_drop _ _ _

#push-options "--split_queries --z3rlimit 16"

let t_array_ref_shift
  (#t: Type)
  (#td: typedef t)
  (a: array_ref td)
  (i: SZ.t)
: Pure (array_ref td)
    (requires (SZ.v (array_ref_offset a) + SZ.v i <= SZ.v (array_ref_base_size a)))
    (ensures (fun y -> 
      array_ref_base_size y == array_ref_base_size a /\
      (forall ty r . has_array_ref_base a #ty r ==> has_array_ref_base y #ty (coerce_eq () r)) /\
      array_ref_offset y == array_ref_offset a `SZ.add` i
    ))
= {
    a with
    ar_offset = a.ar_offset `SZ.add` i
  }

let array_ref_shift
  a i
= t_array_ref_shift a i

let array_ref_shift_zero
  a
= ()

let array_ref_shift_assoc
  a i1 i2
= ()

let ghost_array_split
  #_ #_ #td #s a i
= array_pts_to_length _ _;
  let sq : squash (SZ.v i <= SZ.v (dsnd a) /\ Seq.length s == SZ.v (dsnd a)) = () in
  let br = array_pts_to_elim a s in
  let _ = gen_elim () in
  A.g_split _ _ i ();
  HR.share _;
  let p = vpattern_replace (fun p -> HR.pts_to _ p _ `star` HR.pts_to _ p _) in
  rewrite (HR.pts_to _ _ _) (HR.pts_to (array_ptr_of (array_split_l a i)).ar_base p br);
  rewrite (A.pts_to _ (Seq.slice s 0 _)) (A.pts_to (model_array_of_array (array_split_l a i) br) (Seq.slice s 0 (SZ.v i)));
  array_pts_to_intro (array_split_l a i) (Seq.slice s 0 (SZ.v i)) _ _ ();
  rewrite (HR.pts_to _ _ _) (HR.pts_to (array_ptr_of (array_split_r a i)).ar_base p br);
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array (array_split_r a i) br) (Seq.slice s (SZ.v i) (Seq.length s)));
  array_pts_to_intro (array_split_r a i) (Seq.slice s (SZ.v i) (Seq.length s)) _ _ ();
  sq

let t_array_split_r
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
: Pure (array td)
   (requires (SZ.v i <= SZ.v (dsnd a)))
   (ensures (fun _ -> True))
= let (| al, len |) = a in
  (| t_array_ref_shift al i, Ghost.hide (len `SZ.sub` i) |)

let array_ref_split
  #_ #td #s al len i
= let _ = ghost_array_split (| al, len |) i in
  let ar: (ar: array_ref td { SZ.v i <= SZ.v len /\ Seq.length s == SZ.v len}) = t_array_ref_shift al i in
  return ar

let hr_gather_by_perm
  (#opened: _)
  (#t1: Type)
  (#r1: HR.ref t1)
  (#v1: t1)
  (#t2: Type)
  (#r2: HR.ref t2)
  (#v2: t2)
  (p1: P.perm)
  (p2: P.perm)
: STGhost unit opened
    (HR.pts_to r1 p1 v1 `star` HR.pts_to r2 p2 v2)
    (fun _ -> HR.pts_to r1 (p1 `P.sum_perm` p2) v1)
    (t1 == t2 /\
      r1 == r2)
    (fun _ ->
      t1 == t2 /\
      r1 == r2 /\
      v1 == v2)
= rewrite (HR.pts_to r2 p2 v2) (HR.pts_to r1 p2 (coerce_eq () v2));
  HR.gather p2 r1

let ar_join
  (#opened: _)
  (#base_t #base_tl #base_tr: Type)
  (#t: Type)
  (#p: pcm t)
  (a: A.array base_t p)
  (i: SZ.t)
  (al: A.array base_tl p)
  (ar: A.array base_tr p)
  (sl0 sr0: Seq.seq t)
: STGhost unit opened
    (A.pts_to al sl0 `star` A.pts_to ar sr0)
    (fun _ -> A.pts_to a (sl0 `Seq.append` sr0))
    (
      SZ.v i <= SZ.v a.len /\
      base_t == base_tl /\
      base_t == base_tr /\
      al == A.split_l a i /\
      ar == A.split_r a i
    )
    (fun _ -> True)
= let al' : A.array base_t p = coerce_eq () al in
  let ar' : A.array base_t p = coerce_eq () ar in
  rewrite (A.pts_to al sl0) (A.pts_to al' sl0);
  rewrite (A.pts_to ar sr0) (A.pts_to ar' sr0);
  A.join a i al' ar' _ _

let array_join
  #_ #_ #td #sl #sr a al ar i
= let br = array_pts_to_elim al sl in
  let _ = gen_elim () in
  let pl = vpattern_replace (fun p -> HR.pts_to _ p _) in
  vpattern_rewrite (fun x -> HR.pts_to x pl _) (array_ptr_of a).ar_base;
  let _ = array_pts_to_elim ar sr in
  let _ = gen_elim () in
  let pr = vpattern_replace (fun pr -> HR.pts_to _ pl _ `star` HR.pts_to _ pr _) in
  vpattern_rewrite (fun x -> HR.pts_to x pr _) (array_ptr_of a).ar_base;
  hr_gather_by_perm pl pr;
  ar_join (model_array_of_array a br) i _ _ sl sr;
  array_pts_to_intro a (sl `Seq.append` sr) _ _ ()

let ar_share
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: A.array base_t p)
  (s s1 s2: Seq.seq t)
  (prf: (
    (i: nat) ->
    Lemma
    (requires (i < Seq.length s /\ i < Seq.length s1 /\ i < Seq.length s2))
    (ensures (
      i < Seq.length s /\ i < Seq.length s1 /\ i < Seq.length s2 /\
      composable p (Seq.index s1 i) (Seq.index s2 i) /\
      op p (Seq.index s1 i) (Seq.index s2 i) == Seq.index s i
    ))
  ))
: STGhost unit opened
    (A.pts_to r s)
    (fun _ -> A.pts_to r s1 `star` A.pts_to r s2)
    (
      Seq.length s1 == Seq.length s /\
      Seq.length s2 == Seq.length s
    )
    (fun _ -> True)
= Classical.forall_intro (Classical.move_requires prf);
  A.share r s s1 s2

let mk_fraction_seq_split_gen
  #_ #_ #td r v p p1 p2
= let br = array_pts_to_elim r (mk_fraction_seq td v p) in
  let _ = gen_elim () in
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array r br) (mk_fraction_seq td v p));
  ar_share _ _ (mk_fraction_seq td v p1) (mk_fraction_seq td v p2) (fun i ->
    td.mk_fraction_split (Seq.index v i) p1 p2;
    td.mk_fraction_join (Seq.index v i) p1 p2
  );
  HR.share _;
  array_pts_to_intro r (mk_fraction_seq td v p1) _ _ ();
  array_pts_to_intro r (mk_fraction_seq td v p2) _ _ ()

let ar_gather
  (#opened: _)
  (#base_t: Type)
  (#t: Type)
  (#p: pcm t)
  (r: A.array base_t p)
  (s s1 s2: Seq.seq t)
  (prf: (
    (i: nat) ->
    Lemma
    (requires (
      i < Seq.length s /\ i < Seq.length s1 /\ i < Seq.length s2 /\
      composable p (Seq.index s1 i) (Seq.index s2 i)
    ))
    (ensures (
      i < Seq.length s /\ i < Seq.length s1 /\ i < Seq.length s2 /\
      composable p (Seq.index s1 i) (Seq.index s2 i) /\
      op p (Seq.index s1 i) (Seq.index s2 i) == Seq.index s i
    ))
  ))
: STGhost unit opened
    (A.pts_to r s1 `star` A.pts_to r s2)
    (fun _ -> A.pts_to r s)
    (
      Seq.length s1 == Seq.length s /\
      Seq.length s2 == Seq.length s
    )
    (fun _ -> True)
= Classical.forall_intro (Classical.move_requires prf);
  A.gather r s s1 s2

let mk_fraction_seq_join
  #_ #_ #td r v p1 p2
= let br = array_pts_to_elim r (mk_fraction_seq td v p1) in
  let _ = gen_elim () in
  rewrite (A.pts_to _ _) (A.pts_to (model_array_of_array r br) (mk_fraction_seq td v p1));
  let _ = array_pts_to_elim r (mk_fraction_seq td v p2) in
  let _ = gen_elim () in
  hr_gather (Ghost.reveal br) (array_ptr_of r).ar_base;
  rewrite (A.pts_to _ (mk_fraction_seq _ _ p2)) (A.pts_to (model_array_of_array r br) (mk_fraction_seq td v p2));
  ar_gather _ (mk_fraction_seq td v (p1 `P.sum_perm` p2)) (mk_fraction_seq td v p1) (mk_fraction_seq td v p2) (fun i ->
    td.mk_fraction_join (Seq.index v i) p1 p2
  );
  array_pts_to_intro r (mk_fraction_seq td v (p1 `P.sum_perm` p2)) _ _ ()
