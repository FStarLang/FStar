module Steel.C.Array

let seq_equal_1
  (t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (requires (
    Seq.length s1 == 1 /\
    Seq.length s2 == 1 /\
    Seq.index s1 0 == Seq.index s2 0
  ))
  (ensures (s1 == s2))
= assert (s1 `Seq.equal` s2)

val index0 (#base: Type) (#t:Type) (r:array base t) (i:size_t)
  : Steel t
             (varray r)
             (fun _ -> varray r)
             (requires fun _ -> size_v i < length r)
             (ensures fun h0 x h1 ->
               let s = h1 (varray r) in
               size_v i < length r /\
               h0 (varray r) == s /\
               x == Seq.index s (size_v i))

#push-options "--z3rlimit 128 --fuel 1 --ifuel 2 --query_stats --z3cliopt smt.arith.nl=false"
#restart-solver

let index0
  #_ #t r i
=
  let rr = split r i () in
  let rrr = split rr one_size () in
  change_equal_slprop
    (varray rrr)
    (varray (Ghost.reveal (Ghost.hide rrr)));
  let rrl = split_left rr (GPair?.fst (gsplit rr one_size)) rrr in
  let grl = gget (varray rrl) in
  let r0 = ref_of_array rrl () in
  let res = Steel.C.Opt.ref_opt_read r0 in
  array_of_ref rrl r0 ();
  let grl' = gget (varray rrl) in
  seq_equal_1 t (Ghost.reveal grl) (Ghost.reveal grl');
  let rr' = join' rrl (Ghost.reveal (Ghost.hide rrr)) in
  let r' = join' (Ghost.reveal (Ghost.hide (GPair?.fst (gsplit r i)))) rr' in
  change_equal_slprop
    (varray r')
    (varray r);
  return res

let index_from
  #base #t r r' i
=
  let r0 : array base t = (r, r') in
  change_equal_slprop
    (varray (r, r'))
    (varray r0);
  let res = index0 r0 i in
  change_equal_slprop
    (varray r0)
    (varray (r, r'));
  return res

let seq_append_append_upd
  (t: Type)
  (i: nat)
  (x: t)
  (s1 s2 s2' s3: Seq.seq t)
: Lemma
  (requires (
    Seq.length s1 == i /\
    Seq.length s2 == 1 /\
    Seq.length s2' == 1 /\
    Seq.index s2' 0 == x
  ))
  (ensures (
    s1 `Seq.append` (s2' `Seq.append` s3) == Seq.upd (s1 `Seq.append` (s2 `Seq.append` s3)) i x
  ))
= assert (
    (s1 `Seq.append` (s2' `Seq.append` s3)) `Seq.equal` (Seq.upd (s1 `Seq.append` (s2 `Seq.append` s3)) i x)
  )

val upd0 (#base: Type) (#t:Type) (r:array base t) (i:size_t) (x:t)
  : Steel unit
             (varray r)
             (fun _ -> varray r)
             (requires fun h -> size_v i < length r)
             (ensures fun h0 _ h1 ->
               size_v i < length r /\
               h1 (varray r) == Seq.upd (h0 (varray r)) (size_v i) x)

let upd0
  #_ #t r i x
=
  let rr = split r i () in
  let rrr = split rr one_size () in
  let s3 = gget (varray rrr) in
  change_equal_slprop
    (varray rrr)
    (varray (Ghost.reveal (Ghost.hide rrr)));
  let rrl = split_left rr (GPair?.fst (gsplit rr one_size)) rrr in
  let s1 = gget (varray (Ghost.reveal (Ghost.hide (GPair?.fst (gsplit r i))))) in
  let s2 = gget (varray rrl) in
  let r0 = ref_of_array rrl () in
  Steel.C.Opt.ref_opt_write r0 x;
  array_of_ref rrl r0 ();
  let s2' = gget (varray rrl) in
  seq_append_append_upd t (size_v i) x s1 s2 s2' s3;
  let rr' = join' rrl (Ghost.reveal (Ghost.hide rrr)) in
  let r' = join' (Ghost.reveal (Ghost.hide (GPair?.fst (gsplit r i)))) rr' in
  change_equal_slprop
    (varray r')
    (varray r)

let upd_from
  #base #t r r' i x
=
  let r0 : array base t = (r, r') in
  change_equal_slprop
    (varray (r, r'))
    (varray r0);
  upd0 r0 i x;
  change_equal_slprop
    (varray r0)
    (varray (r, r'))

let varray_or_null0_rewrite
  (#base #a: Type0)
  (r: array_or_null base a)
  (_: t_of emp)
: Tot (option (array_view_type a (len r)))
= None
