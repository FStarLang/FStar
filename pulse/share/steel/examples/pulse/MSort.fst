module MSort

open FStar.Ghost
open Pulse.Lib.Pervasives
open TaskPool
module A = Pulse.Lib.Array
module S = FStar.Seq
module SZ = FStar.SizeT

#set-options "--z3rlimit 20"

assume val sort : Seq.seq int -> Seq.seq int
assume val sorted : Seq.seq int -> bool
assume val sort_is_sorted (s:Seq.seq int) : Lemma (sorted (sort s))
assume val sort_len (s:Seq.seq int)
  : Lemma (S.length (sort s) == S.length s)
          [SMTPat (S.length (sort s))]

assume val singl_is_sorted (s : S.seq int)
  : Lemma (requires S.length s < 2)
          (ensures s == sort s)

type seq_view a =
  | Nil
  | Cons : a -> S.seq a -> seq_view a

let view #a (s : S.seq a) : seq_view a =
  if S.length s = 0 then Nil else Cons (S.head s) (S.tail s)

val merge : Seq.seq int -> Seq.seq int -> Seq.seq int
let rec merge s1 s2 : Tot (S.seq int) (decreases S.length s1 + S.length s2) =
  match view s1, view s2 with
  | Nil, Nil -> S.empty
  | Nil, Cons h t -> S.cons h t
  | Cons h t, Nil -> S.cons h t
  | Cons h1 t1, Cons h2 t2 ->
    if h1 <= h2 then S.cons h1 (merge t1 s2) else S.cons h2 (merge s1 t2)

assume val merge_len (s1 s2 : S.seq int)
  : Lemma (ensures S.length (merge s1 s2) == S.length s1 + S.length s2)
          [SMTPat (merge s1 s2)]

assume val merge_sorted' (s1 s2 : S.seq int)
  : Lemma (ensures merge (sort s1) (sort s2) == sort (s1 `S.append` s2))
          [SMTPat (merge (sort s1) (sort s2))]

assume val merge_sorted (s1 s2 : S.seq int)
  : Lemma (requires sorted s1 /\ sorted s2)
          (ensures sorted (merge s1 s2))
          [SMTPat (sorted (merge s1 s2))]

assume val append_slice #a (s : S.seq a)
  (l1:nat) (l2 : nat{S.length s == l2 /\ l1 <= l2})
  : Lemma (S.append (S.slice s 0 l1) (S.slice s l1 l2) == s)
          [SMTPat (S.append (S.slice s 0 l1) (S.slice s l1 l2))]

(* These two must be total or the invariant of the loop fails to typecheck.
I think the problem is that the pure assertions within the invariant are not
used to typecheck the other components of the invariant. *)
let stake #a (i:nat) (s : S.seq a)
: Tot (S.seq a)
= if i <= S.length s
  then S.slice s 0 i
  else s

let sdrop #a (i:nat) (s : S.seq a)
: Tot (S.seq a)
= if i <= S.length s
  then S.slice s i (S.length s)
  else S.empty

let take_0_lem #a (s : S.seq a)
  : Lemma (stake 0 s == S.empty)
          [SMTPat (stake 0 s)]
  = ()

let drop_0_lem #a (s : S.seq a)
  : Lemma (sdrop 0 s == s)
          [SMTPat (sdrop 0 s)]
  = ()

let take_len_lem #a (s : S.seq a)
  : Lemma (stake (S.length s) s == s)
          [SMTPat (stake (S.length s) s)]
  = ()

let drop_len_lem #a (s : S.seq a)
  : Lemma (sdrop (S.length s) s == S.empty)
          [SMTPat (sdrop (S.length s) s)]
  = ()
//
let nil_app_l #a (s : S.seq a)
  : Lemma (S.append S.empty s == s)
          [SMTPat (S.append S.empty s)]
  = S.append_empty_l s
let nil_app_r #a (s : S.seq a)
  : Lemma (S.append s S.empty == s)
          [SMTPat (S.append s S.empty)]
  = S.append_empty_r s

let lem_upd_spliced #a (l:nat) (s1 s2 : S.seq a) (i : nat)
  : Lemma
      (requires S.length s1 == l /\ S.length s2 == l /\ 0 <= i /\ i < l )
      (ensures
        S.upd (stake i s1 `S.append` sdrop i s2) i (S.index s1 i) ==
              (stake (i+1) s1 `S.append` sdrop (i+1) s2))
  = admit ()

```pulse
fn
copy_array
  (src tgt : array int)
  (s_lo t_lo len : SZ.t)
  (#s_src : erased (S.seq int))
  (#s_tgt : erased (S.seq int))
  requires pts_to_range src (SZ.v s_lo) (SZ.v s_lo + SZ.v len) s_src
        ** pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) s_tgt
  ensures  pts_to_range src (SZ.v s_lo) (SZ.v s_lo + SZ.v len) s_src
        ** pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) s_src
{
  pts_to_range_prop src;
  pts_to_range_prop tgt;
  if (len `SZ.gt` 0sz) {
    let mut i = 0sz;

    assert (pure (SZ.v len == S.length s_src));
    assert (pure (SZ.v len == S.length s_tgt));
    assert (pure (stake 0 s_src `S.append` sdrop 0 s_tgt == s_tgt));

    with vi0. assert (pts_to i vi0 ** pure (SZ.v vi0 <= SZ.v len));

    while (
      let vi = !i;
      (vi `SZ.lt` len)
    )
      invariant b. exists* vi.
        pts_to i vi **
        pts_to_range src (SZ.v s_lo) (SZ.v s_lo + SZ.v len) s_src **
        pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len)
            (stake (SZ.v vi) s_src `S.append` sdrop (SZ.v vi) s_tgt) **
        pure (SZ.v len > 0 /\
              SZ.v vi <= SZ.v len /\
              SZ.v len == S.length s_src /\
              SZ.v len == S.length s_tgt /\
              (vi `SZ.lt` len == false ==> SZ.v vi == SZ.v len)) **
        pure (b == (SZ.v vi <  SZ.v len)) ** // can't use <==>, why?
        emp
    {
      let ii = !i;

      assert (pure (SZ.v ii <= SZ.v len));
      assert (pure (SZ.v ii < SZ.v len));

      assert (pure (SZ.v s_lo <= SZ.v s_lo + SZ.v ii));
      assert (pure (SZ.v s_lo + SZ.v ii < SZ.v s_lo + SZ.v len));
      assume_ (pure (SZ.fits (SZ.v s_lo + SZ.v ii)));


      assert (pts_to_range src (SZ.v s_lo) (SZ.v s_lo + SZ.v len) s_src);
      let v = pts_to_range_index src (s_lo `SZ.add` ii);


      assume_ (pure (SZ.fits (SZ.v t_lo + SZ.v ii)));

      assert (pure (SZ.v t_lo <= SZ.v t_lo + SZ.v ii));
      assert (pure (SZ.v t_lo + SZ.v ii < SZ.v t_lo + SZ.v len));
      assert (pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len)
        (stake (SZ.v ii) s_src `S.append` sdrop (SZ.v ii) s_tgt));

      pts_to_range_upd #int tgt (t_lo `SZ.add` ii) v
        #(SZ.v t_lo) #(SZ.v t_lo + SZ.v len)
        #(stake (SZ.v ii) s_src `S.append` sdrop (SZ.v ii) s_tgt);

      with ss. assert pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) ss;

      rewrite pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) ss
          as pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len)
                              (S.upd (stake (SZ.v ii) s_src `S.append` sdrop (SZ.v ii) s_tgt) (SZ.v ii) v);

      lem_upd_spliced (SZ.v len) s_src s_tgt (SZ.v ii);

      rewrite pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len)
                              (S.upd (stake (SZ.v ii) s_src `S.append` sdrop (SZ.v ii) s_tgt) (SZ.v ii) v)
          as pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len)
                              (stake (1 + SZ.v ii) s_src `S.append` sdrop (1 + SZ.v ii) s_tgt);

      assert (pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len)
        (stake (1 + SZ.v ii) s_src `S.append` sdrop (1 + SZ.v ii) s_tgt));

      i := ii `SZ.add` 1sz;
    };

    S.append_empty_r s_src;

    rewrite pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len)
                            (stake (SZ.v len) s_src `S.append` sdrop (SZ.v len) s_tgt)
        as pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) s_src;
    ()
  } else {
    (* len = 0 *)
    S.lemma_empty s_src;
    S.lemma_empty s_tgt;
    rewrite pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) s_tgt
         as pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) s_src;
    ()
  }
}
```

let partial_merge (s1 s2 : S.seq int) (i:nat{i <= S.length s1}) (j : nat{j <= S.length s2}) : Seq.lseq int (S.length s1 + S.length s2) =
  S.append (merge (stake i s1) (stake j s2)) (sdrop (i+j) (S.append s1 s2))

let lem_partial_merge_full_l_add (s1 s2 : S.seq int) (i:nat) (j : nat{j < S.length s2})
  : Lemma (requires i == S.length s1)
          (ensures Seq.upd (partial_merge s1 s2 i j)
                           (i+j) (S.index s2 j)
                    == partial_merge s1 s2 i (j+1))
  = admit ()

let lem_partial_merge_full_r_add (s1 s2 : S.seq int) (i : nat{i < S.length s1}) (j : nat)
  : Lemma (requires j == S.length s2)
          (ensures Seq.upd (partial_merge s1 s2 i j)
                           (i+j) (S.index s1 i)
                    == partial_merge s1 s2 (i+1) j)
  = admit ()

let lem_partial_merge_full_left_add (s1 s2 : S.seq int) (i : nat{i < S.length s1}) (j : nat{j < S.length s2})
  : Lemma (requires Seq.index s1 i <= Seq.index s2 j)
          (ensures Seq.upd (partial_merge s1 s2 i j)
                           (i+j) (S.index s1 i)
                    == partial_merge s1 s2 (i+1) j)
  = admit ()

let lem_partial_merge_full_right_add (s1 s2 : S.seq int) (i : nat{i < S.length s1}) (j : nat{j < S.length s2})
  : Lemma (requires Seq.index s1 i >= Seq.index s2 j)
          (ensures Seq.upd (partial_merge s1 s2 i j)
                           (i+j) (S.index s2 j)
                    == partial_merge s1 s2 i (j+1))
  = admit ()

```pulse
fn
merge_impl
  (a : array int) (lo mid hi : SZ.t)
  (_:squash (SZ.v lo <= SZ.v mid /\ SZ.v mid <= SZ.v hi))
  (s1 : erased (S.seq int))
  (s2 : erased (S.seq int))
  requires pts_to_range a (SZ.v lo) (SZ.v mid) s1
        ** pts_to_range a (SZ.v mid) (SZ.v hi) s2
  ensures pts_to_range a (SZ.v lo) (SZ.v hi) (merge s1 s2)
{
  let l1 = mid `SZ.sub` lo;
  let l2 = hi  `SZ.sub` mid;

  pts_to_range_prop a #(SZ.v lo) #(SZ.v mid);
  pts_to_range_prop a #(SZ.v mid) #(SZ.v hi);

  assert (pure (SZ.v l1 == S.length s1));
  assert (pure (SZ.v l2 == S.length s2));

  let sw1 = A.alloc 0 (mid `SZ.sub` lo);
  let sw2 = A.alloc 0 (hi `SZ.sub` mid);

  pts_to_range_intro sw1 full_perm (S.create (SZ.v l1) 0);
  copy_array a sw1 lo 0sz (mid `SZ.sub` lo);
  pts_to_range_elim sw1 full_perm s1;

  pts_to_range_intro sw2 full_perm (S.create (SZ.v l2) 0);
  copy_array a sw2 mid 0sz (hi `SZ.sub` mid);
  pts_to_range_elim sw2 full_perm s2;

  let mut i = 0sz;
  let mut j = 0sz;
  let mut k = 0sz;

  pts_to_range_join a (SZ.v lo) (SZ.v mid) (SZ.v hi);

  assert (pure (S.append (merge (stake 0 (reveal s1)) (stake 0 (reveal s2)))
                   (sdrop 0 (S.append s1 s2))
                 == S.append s1 s2));

  rewrite
      pts_to_range a (SZ.v lo) (SZ.v hi)
                     (S.append s1 s2)
  as
      pts_to_range a (SZ.v lo)
                     (SZ.v hi)
                     (S.append (merge (stake 0 (reveal s1)) (stake 0 (reveal s2)))
                               (sdrop 0 (S.append s1 s2)));

  assert
      pts_to_range a (SZ.v lo)
                     (SZ.v hi)
                     (S.append (merge (stake 0 (reveal s1)) (stake 0 (reveal s2)))
                               (sdrop 0 (S.append s1 s2)));

  while (
    let vi = !i;
    let vj = !j;
    (vi `SZ.lt` l1 || vj `SZ.lt` l2)
  )
    invariant b.
      exists* vi vj vk.
      pts_to i vi **
      pts_to j vj **
      pts_to k vk **
      A.pts_to sw1 (reveal s1) **
      A.pts_to sw2 (reveal s2) **
      pts_to_range a (SZ.v lo)
                     (SZ.v hi)
                     (S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                               (sdrop (SZ.v vk) (S.append s1 s2)))
                     **
      pure (SZ.v vi <= SZ.v l1 /\ SZ.v vj <= SZ.v l2 /\ vk == vi `SZ.add` vj) **
      pure (b == (vi `SZ.lt` l1 || vj `SZ.lt` l2)) **
      emp
  {
    (* End of l1 *)
    let vi = !i;
    let vj = !j;
    let vk = !k;
    if (vi = l1) {
      let x = sw2.(vj);
      pts_to_range_upd a (lo `SZ.add` vk) x; //a.(lo + vk) <- x;
      j := vj `SZ.add` 1sz;
      k := vk `SZ.add` 1sz;

      lem_partial_merge_full_l_add (reveal s1) (reveal s2) (SZ.v vi) (SZ.v vj);

      rewrite
        pts_to_range a (SZ.v lo) (SZ.v hi)
              (Seq.upd
                  (S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                                                (sdrop (SZ.v vk) (S.append s1 s2)))
                  (SZ.v vk) x)
      as
         pts_to_range a (SZ.v lo) (SZ.v hi)
              (S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v (vj `SZ.add` 1sz)) (reveal s2)))
                        (sdrop (SZ.v (vk `SZ.add` 1sz)) (S.append s1 s2)));

    } else if (vj = l2) {
      let x = sw1.(vi);
      pts_to_range_upd a (lo `SZ.add` vk) x; //a.(lo + vk) <- x;
      i := vi `SZ.add` 1sz;
      k := vk `SZ.add` 1sz;

      lem_partial_merge_full_r_add (reveal s1) (reveal s2) (SZ.v vi) (SZ.v vj);

      rewrite
        pts_to_range a (SZ.v lo) (SZ.v hi)
              (Seq.upd
                  (S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                                                (sdrop (SZ.v vk) (S.append s1 s2)))
                  (SZ.v vk) x)
      as
         pts_to_range a (SZ.v lo) (SZ.v hi)
              (S.append (merge (stake (SZ.v (vi `SZ.add` 1sz)) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                        (sdrop (SZ.v (vk `SZ.add` 1sz)) (S.append s1 s2)));
    } else {
      let x = sw1.(vi);
      let y = sw2.(vj);
      if (x <= y) {
        pts_to_range_upd a (lo `SZ.add` vk) x; //a.(lo + vk) <- x;
        i := vi `SZ.add` 1sz;
        k := vk `SZ.add` 1sz;
        lem_partial_merge_full_left_add (reveal s1) (reveal s2) (SZ.v vi) (SZ.v vj);

        rewrite
          pts_to_range a (SZ.v lo) (SZ.v hi)
                (Seq.upd
                    (S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                                                  (sdrop (SZ.v vk) (S.append s1 s2)))
                    (SZ.v vk) x)
        as
          pts_to_range a (SZ.v lo) (SZ.v hi)
                (S.append (merge (stake (SZ.v (vi `SZ.add` 1sz)) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                          (sdrop (SZ.v (vk `SZ.add` 1sz)) (S.append s1 s2)));

      } else {
        pts_to_range_upd a (lo `SZ.add` vk) y; //a.(lo + vk) <- y;
        j := vj `SZ.add` 1sz;
        k := vk `SZ.add` 1sz;
        lem_partial_merge_full_right_add (reveal s1) (reveal s2) (SZ.v vi) (SZ.v vj);

        rewrite
          pts_to_range a (SZ.v lo) (SZ.v hi)
                (Seq.upd
                    (S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                                                  (sdrop (SZ.v vk) (S.append s1 s2)))
                    (SZ.v vk) y)
        as
          pts_to_range a (SZ.v lo) (SZ.v hi)
                (S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v (vj `SZ.add` 1sz)) (reveal s2)))
                          (sdrop (SZ.v (vk `SZ.add` 1sz)) (S.append s1 s2)));
      };
    }
  };

  assume_ (pure (
        (S.append (merge s1 s2) (sdrop (SZ.v l1 + SZ.v l2) (S.append s1 s2)))
        ==
        merge s1 s2)
  );

  with vi.
    assert (pts_to i vi ** pure (SZ.v vi == SZ.v l1));
  with vj.
    assert (pts_to j vj ** pure (SZ.v vj == SZ.v l2));

  A.free sw1;
  A.free sw2;

  rewrite
    pts_to_range a (SZ.v lo) (SZ.v hi)
        (S.append (merge s1 s2) (sdrop (SZ.v l1 + SZ.v l2) (S.append s1 s2)))
  as
    pts_to_range a (SZ.v lo) (SZ.v hi) (merge s1 s2);

  assert pts_to_range a (SZ.v lo) (SZ.v hi) (merge s1 s2)
}
```


```pulse
fn
rec
msort
  (a : array int)
  (lo hi : SZ.t)
  (s : erased (S.seq int))
  requires pts_to_range a (SZ.v lo) (SZ.v hi) (reveal s)
  ensures  pts_to_range a (SZ.v lo) (SZ.v hi) (sort (reveal s))
{
  pts_to_range_prop a;
  if ((hi `SZ.sub` lo) `SZ.lt` 2sz) {
    pts_to_range_prop a;
    singl_is_sorted s;
    ()
  } else {
    let mid : SZ.t = lo `SZ.add` ((hi `SZ.sub` lo) `SZ.div` 2sz);

    pts_to_range_split a (SZ.v lo) (SZ.v mid) (SZ.v hi);

    with s1. assert (pts_to_range a (SZ.v lo) (SZ.v mid) s1);
    with s2. assert (pts_to_range a (SZ.v mid) (SZ.v hi) s2);

    msort a lo mid s1;
    msort a mid hi s2;

    merge_impl a lo mid hi () (sort s1) (sort s2);
  }
}
```
