module Steel.ST.Array0

/// Lifting a value of universe 0 to universe 1. We could use
/// FStar.Universe, but that module is not tailored to inlining at
/// extraction.

[@@erasable]
noeq
type dummy_universe1 : Type u#1 = | DummyU1

/// This type definition supports inlining, contrary to the custom
/// type defined in FStar.Universe.fst.
inline_for_extraction
[@@ noextract_to "krml"]
let raise_t (t: Type0) : Type u#1 = (t & dummy_universe1)

inline_for_extraction
[@@noextract_to "krml"]
let raise (#t: Type) (x: t) : Tot (raise_t t) = (x, DummyU1)

inline_for_extraction
[@@noextract_to "krml"]
let lower (#t: Type) (x: raise_t t) : Tot t =
  match x with (x', _) -> x'

/// A map operation on sequences. Here we only need Ghost versions,
/// because such sequences are only used in vprops or with their
/// selectors.

let rec seq_map
  (#t: Type u#a)
  (#t' : Type u#b)
  (f: (t -> GTot t'))
  (s: Seq.seq t)
: Ghost (Seq.seq t')
  (requires True)
  (ensures (fun s' ->
    Seq.length s' == Seq.length s /\
    (forall i . {:pattern (Seq.index s' i)} Seq.index s' i == f (Seq.index s i))
  ))
  (decreases (Seq.length s))
= if Seq.length s = 0
  then Seq.empty
  else Seq.cons (f (Seq.index s 0)) (seq_map f (Seq.slice s 1 (Seq.length s)))

let seq_map_append
  (#t: Type u#a)
  (#t': Type u#b)
  (f: (t -> GTot t'))
  (s1 s2: Seq.seq t)
: Lemma
  (seq_map f (s1 `Seq.append` s2) `Seq.equal` (seq_map f s1 `Seq.append` seq_map f s2))
= ()

let seq_map_raise_inj
  (#elt: Type0)
  (s1 s2: Seq.seq elt)
: Lemma
  (requires (seq_map raise s1 == seq_map raise s2))
  (ensures (s1 == s2))
  [SMTPat (seq_map raise s1); SMTPat (seq_map raise s2)]
= assert (seq_map lower (seq_map raise s1) `Seq.equal` s1);
  assert (seq_map lower (seq_map raise s2) `Seq.equal` s2)

/// Implementation of the interface

/// base, ptr, array, pts_to

module H = Steel.ST.HigherArray0

let base_t elt = H.base_t (raise_t elt)
let base_len b = H.base_len b

let ptr elt = H.ptr (raise_t elt)
let base p = H.base p
let offset p = H.offset p
let ptr_base_offset_inj p1 p2 = H.ptr_base_offset_inj p1 p2

let pts_to a p s = H.pts_to a p (seq_map raise s)

let pts_to_length a s =
  H.pts_to_length a _

let pts_to_inj a p1 s1 p2 s2 =
  H.pts_to_inj a p1 (seq_map raise s1) p2 (seq_map raise s2)

/// Non-selector operations.

let malloc x n =
  let res = H.malloc (raise x) n in
  assert (seq_map raise (Seq.create (U32.v n) x) `Seq.equal` Seq.create (U32.v n) (raise x));
  rewrite
    (H.pts_to res _ _)
    (pts_to res _ _);
  return res

let free #_ #s x =
  rewrite
    (pts_to x _ _)
    (H.pts_to x P.full_perm (seq_map raise s));
  H.free x

let share
  #_ #_ #x a p p1 p2
= rewrite
    (pts_to a _ _)
    (H.pts_to a p (seq_map raise x));
  H.share a p p1 p2;
  rewrite
    (H.pts_to a p1 _)
    (pts_to a p1 x);
  rewrite
    (H.pts_to a p2 _)
    (pts_to a p2 x)

let gather
  #_ #_ a #x1 p1 #x2 p2
= rewrite
    (pts_to a p1 _)
    (H.pts_to a p1 (seq_map raise x1));
  rewrite
    (pts_to a p2 _)
    (H.pts_to a p2 (seq_map raise x2));
  H.gather a p1 p2;
  rewrite
    (H.pts_to a _ _)
    (pts_to _ _ _)

let index #_ #p a #s i =
  rewrite
    (pts_to a _ _)
    (H.pts_to a p (seq_map raise s));
  let res = H.index a i in
  rewrite
    (H.pts_to _ _ _)
    (pts_to _ _ _);
  return (lower res)

let upd #_ a #s i v =
  rewrite
    (pts_to a _ _)
    (H.pts_to a P.full_perm (seq_map raise s));
  H.upd a i (raise v);
  assert (seq_map raise (Seq.upd s (U32.v i) v) `Seq.equal` Seq.upd (seq_map raise s) (U32.v i) (raise v));
  rewrite
    (H.pts_to _ _ _)
    (pts_to _ _ _)

let ghost_join
  #_ #_ #x1 #x2 #p a1 a2 h
= rewrite
    (pts_to a1 _ _)
    (H.pts_to a1 p (seq_map raise x1));
  rewrite
    (pts_to a2 _ _)
    (H.pts_to a2 p (seq_map raise x2));
  H.ghost_join a1 a2 h;
  assert (seq_map raise (x1 `Seq.append` x2) `Seq.equal` (seq_map raise x1 `Seq.append` seq_map raise x2));
  rewrite
    (H.pts_to _ _ _)
    (H.pts_to (merge a1 a2) p (seq_map raise (x1 `Seq.append` x2)));
  rewrite
    (H.pts_to _ _ _)
    (pts_to (merge a1 a2) _ _)

let ptr_shift p off = H.ptr_shift p off

let ghost_split
  #_ #_ #x #p a i
=
  rewrite
    (pts_to a _ _)
    (H.pts_to a p (seq_map raise x));
  H.ghost_split a i;
  assert (seq_map raise (Seq.slice x 0 (U32.v i)) `Seq.equal` Seq.slice (seq_map raise x) 0 (U32.v i));
  rewrite
    (H.pts_to (H.split_l a i) _ _)
    (H.pts_to (split_l a i) p (seq_map raise (Seq.slice x 0 (U32.v i))));
  rewrite
    (H.pts_to (split_l a i) _ _)
    (pts_to (split_l a i) _ _);
  assert (seq_map raise (Seq.slice x (U32.v i) (Seq.length x)) `Seq.equal` Seq.slice (seq_map raise x) (U32.v i) (Seq.length (seq_map raise x)));
  Seq.lemma_split x (U32.v i);
  rewrite
    (H.pts_to (H.split_r a i) _ _)
    (H.pts_to (split_r a i) p (seq_map raise (Seq.slice x (U32.v i) (Seq.length x))));
  rewrite
    (H.pts_to (split_r a i) _ _)
    (pts_to (split_r a i) _ _)

let memcpy
  a0 a1 l
=
  H.memcpy a0 a1 l

////////////////////////////////////////////////////////////////////////////////
// compare
////////////////////////////////////////////////////////////////////////////////

module R = Steel.ST.Reference

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 2"
let equal_up_to #t
                  (s0: Seq.seq t)
                  (s1: Seq.seq t)
                  (v : option U32.t) : prop =
    Seq.length s0 = Seq.length s1 /\
    (match v with
     | None -> Ghost.reveal s0 =!= Ghost.reveal s1
     | Some v -> U32.v v <= Seq.length s0 /\ Seq.slice s0 0 (U32.v v) `Seq.equal` Seq.slice s1 0 (U32.v v))

let within_bounds (x:option U32.t) (l:U32.t) (b:Ghost.erased bool) : prop =
  if b then Some? x /\ U32.(Some?.v x <^ l)
  else None? x \/ U32.(Some?.v x >=^ l)

let compare_inv (#t:eqtype) (#p0 #p1:perm)
        (a0 a1:array t)
        (s0: Seq.seq t)
        (s1: Seq.seq t)
        (l:U32.t)
        (ctr : R.ref (option U32.t))
        (b: bool) =
    pts_to a0 p0 s0 `star`
    pts_to a1 p1 s1 `star`
    exists_ (fun (x:option U32.t) ->
        R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
        pure (equal_up_to s0 s1 x) `star`
        pure (within_bounds x l b))

let elim_compare_inv #o
        (#t:eqtype)
        (#p0 #p1:perm)
        (a0 a1:array t)
        (#s0: Seq.seq t)
        (#s1: Seq.seq t)
        (l:U32.t)
        (ctr : R.ref (option U32.t))
        (b: bool)
    : STGhostT (Ghost.erased (option U32.t)) o
        (compare_inv a0 a1 s0 s1 l ctr b)
        (fun x ->
          let open U32 in
          pts_to a0 p0 s0 `star`
          pts_to a1 p1 s1 `star`
          R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
          pure (equal_up_to s0 s1 x) `star`
          pure (within_bounds x l b))
      = let open U32 in
        assert_spinoff
          ((compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr b) ==
          (pts_to a0 p0 s0 `star`
           pts_to a1 p1 s1 `star`
           exists_ (fun (v:option U32.t) ->
             R.pts_to ctr Steel.FractionalPermission.full_perm v `star`
             pure (equal_up_to s0 s1 v)  `star`
             pure (within_bounds v l b))));
        rewrite
          (compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr b)
          (pts_to a0 p0 s0 `star`
           pts_to a1 p1 s1 `star`
           exists_ (fun (v:option U32.t) ->
             R.pts_to ctr Steel.FractionalPermission.full_perm v `star`
             pure (equal_up_to s0 s1 v) `star`
             pure (within_bounds v l b)));
        let _v = elim_exists () in
        _v

let intro_compare_inv #o
              (#t:eqtype)
              (#p0 #p1:perm)
              (a0 a1:array t)
              (#s0: Seq.seq t)
              (#s1: Seq.seq t)
              (l:U32.t)
              (ctr : R.ref (option U32.t))
              (x: Ghost.erased (option U32.t))
              (b:bool { within_bounds x l b })
    : STGhostT unit o
         (let open U32 in
          pts_to a0 p0 s0 `star`
          pts_to a1 p1 s1 `star`
          R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
          pure (equal_up_to s0 s1 x))
        (fun _ -> compare_inv a0 a1 s0 s1 l ctr (Ghost.hide b))
    = let open U32 in
      intro_pure (within_bounds x l (Ghost.hide b));
      intro_exists_erased x (fun (x:option U32.t) ->
          R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
          pure (equal_up_to s0 s1 x) `star`
          pure (within_bounds x l (Ghost.hide b)));
      assert_norm
          ((compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr (Ghost.hide b)) ==
          (pts_to a0 p0 s0 `star`
           pts_to a1 p1 s1 `star`
           exists_ (fun (v:option U32.t) ->
             R.pts_to ctr Steel.FractionalPermission.full_perm v `star`
             pure (equal_up_to s0 s1 v)  `star`
             pure (within_bounds v l (Ghost.hide b)))));
        rewrite
          (pts_to a0 p0 s0 `star`
           pts_to a1 p1 s1 `star`
           exists_ (fun (v:option U32.t) ->
             R.pts_to ctr Steel.FractionalPermission.full_perm v `star`
             pure (equal_up_to s0 s1 v) `star`
             pure (within_bounds v l (Ghost.hide b))))
          (compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr (Ghost.hide b))

let intro_exists_compare_inv #o
              (#t:eqtype)
              (#p0 #p1:perm)
              (a0 a1:array t)
              (#s0: Seq.seq t)
              (#s1: Seq.seq t)
              (l:U32.t)
              (ctr : R.ref (option U32.t))
              (x: Ghost.erased (option U32.t))
    : STGhostT unit o
         (let open U32 in
          pts_to a0 p0 s0 `star`
          pts_to a1 p1 s1 `star`
          R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
          pure (equal_up_to s0 s1 x))
        (fun _ -> exists_ (compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr))
    = let b : bool =
          match Ghost.reveal x with
          | None -> false
          | Some x -> U32.(x <^ l)
      in
      assert (within_bounds x l b);
      intro_compare_inv #_ #_ #p0 #p1 a0 a1 #s0 #s1 l ctr x b;
      intro_exists _ (compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr)

let extend_equal_up_to_lemma (#t:Type0)
                             (s0:Seq.seq t)
                             (s1:Seq.seq t)
                             (i:nat{ i < Seq.length s0 /\ Seq.length s0 == Seq.length s1 })
  : Lemma
    (requires
      Seq.equal (Seq.slice s0 0 i) (Seq.slice s1 0 i) /\
      Seq.index s0 i == Seq.index s1 i)
    (ensures
      Seq.equal (Seq.slice s0 0 (i + 1)) (Seq.slice s1 0 (i + 1)))
  = assert (forall k. k < i ==> Seq.index s0 k == Seq.index (Seq.slice s0 0 i) k /\
                           Seq.index s1 k == Seq.index (Seq.slice s1 0 i) k)

let extend_equal_up_to (#o:_)
                       (#t:Type0)
                       (#s0:Seq.seq t)
                       (#s1:Seq.seq t)
                       (len:U32.t)
                       (i:U32.t{ Seq.length s0 == Seq.length s1 /\ U32.(i <^ len) /\ U32.v len == Seq.length s0 } )
  : STGhost unit o
    (pure (equal_up_to s0 s1 (Some i)))
    (fun _ -> pure (equal_up_to s0 s1 (Some U32.(i +^ 1ul))))
    (requires
      Seq.index s0 (U32.v i) == Seq.index s1 (U32.v i))
    (ensures fun _ -> True)
  = elim_pure _;
    extend_equal_up_to_lemma s0 s1 (U32.v i);
    intro_pure (equal_up_to s0 s1 (Some U32.(i +^ 1ul)))

let extend_equal_up_to_neg (#o:_)
                           (#t:Type0)
                           (#s0:Seq.seq t)
                           (#s1:Seq.seq t)
                           (len:U32.t)
                           (i:U32.t{ Seq.length s0 == Seq.length s1 /\ U32.(i <^ len) /\ U32.v len == Seq.length s0 } )
  : STGhost unit o
    (pure (equal_up_to s0 s1 (Some i)))
    (fun _ -> pure (equal_up_to s0 s1 None))
    (requires
      Seq.index s0 (U32.v i) =!= Seq.index s1 (U32.v i))
    (ensures fun _ -> True)
  = elim_pure _;
    intro_pure _

let init_compare_inv #o
             (#t:eqtype)
             (#p0 #p1:perm)
             (a0 a1:array t)
             (#s0: Seq.seq t)
             (#s1: Seq.seq t)
             (l:U32.t)
             (ctr : R.ref (option U32.t))
    : STGhost unit o
         (let open U32 in
          pts_to a0 p0 s0 `star`
          pts_to a1 p1 s1 `star`
          R.pts_to ctr Steel.FractionalPermission.full_perm (Some 0ul))
        (fun _ -> exists_ (compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr))
        (requires (
          length a0 > 0 /\
          length a0 == length a1 /\
          U32.v l == length a0
        ))
        (ensures (fun _ -> True))
    = pts_to_length a0 _;
      pts_to_length a1 _;
      intro_pure (equal_up_to s0 s1 (Ghost.hide (Some 0ul)));
      rewrite
        (R.pts_to ctr Steel.FractionalPermission.full_perm (Some 0ul))
        (R.pts_to ctr Steel.FractionalPermission.full_perm (Ghost.hide (Some 0ul)));
      intro_exists_compare_inv a0 a1 l ctr (Ghost.hide (Some 0ul))

let compare_pts
    (#t:eqtype)
    (#p0 #p1:perm)
    (a0 a1:array t)
    (#s0: Ghost.erased (Seq.seq t))
    (#s1: Ghost.erased (Seq.seq t))
    (l:U32.t)
  : ST bool
    (pts_to a0 p0 s0 `star` pts_to a1 p1 s1)
    (fun _ -> pts_to a0 p0 s0 `star` pts_to a1 p1 s1)
    (requires
      length a0 > 0 /\ length a0 == length a1 /\ U32.v l == length a0
    )
    (ensures fun b ->
      b = (Ghost.reveal s0 = Ghost.reveal s1))
  =
   pts_to_length a0 _;
   pts_to_length a1 _;
   let ctr = R.alloc (Some 0ul) in
    let cond ()
      : STT bool
        (exists_ (compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr))
        (fun b -> compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr (Ghost.hide b))
      = let _b = elim_exists () in
        let _ = elim_compare_inv _ _ _ _ _ in
        let x = R.read ctr in
        elim_pure (within_bounds _ _ _);
        match x with
        | None ->
          intro_compare_inv #_ #_ #p0 #p1 a0 a1 l ctr _ false;
          return false

        | Some x ->
          let res = U32.(x <^ l) in
          intro_compare_inv #_ #_ #p0 #p1 a0 a1 l ctr _ res;
          return res
    in
    let body ()
      : STT unit
        (compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr (Ghost.hide true))
        (fun _ -> exists_ (compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr))
      = let _i = elim_compare_inv _ _ _ _ _ in
        elim_pure (within_bounds _ _ _);
        let Some i = R.read ctr in
        assert_spinoff
          ((pure (equal_up_to s0 s1 _i)) ==
           (pure (equal_up_to s0 s1 (Some i))));
        rewrite
          (pure (equal_up_to s0 s1 _i))
          (pure (equal_up_to s0 s1 (Some i)));
        let v0 = index a0 i in
        let v1 = index a1 i in
        if v0 = v1
        then (
          R.write ctr (Some U32.(i +^ 1ul));
          extend_equal_up_to l i;
          intro_exists_compare_inv #_ #_ #p0 #p1 a0 a1 l ctr (Ghost.hide (Some (U32.(i +^ 1ul))))
        )
        else (
          R.write ctr None;
          extend_equal_up_to_neg l i;
          intro_exists_compare_inv #_ #_ #p0 #p1 a0 a1 l ctr (Ghost.hide None)
        )
    in
    init_compare_inv a0 a1 l ctr;
    Steel.ST.Loops.while_loop (compare_inv #_ #p0 #p1 a0 a1 s0 s1 l ctr)
               cond
               body;
    let _ = elim_compare_inv _ _ _ _ _ in
    elim_pure (equal_up_to _ _ _);
    let v = R.read ctr in
    R.free ctr;
    elim_pure (within_bounds _ _ _);
    match v with
    | None -> return false
    | Some _ -> return true

let compare
  #t #p0 #p1 a0 a1 #s0 #s1 l
  =
    pts_to_length a0 _;
    pts_to_length a1 _;
    if l = 0ul
    then (
      assert (Seq.equal s0 s1);
      return true
    )
    else (
      compare_pts a0 a1 l
    )

#pop-options
