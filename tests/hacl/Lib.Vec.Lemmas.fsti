module Lib.Vec.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.Sequence.Lemmas

module Loops = Lib.LoopCombinators

#push-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 \
  --using_facts_from '-* +Prims +FStar.Pervasives +FStar.Math.Lemmas +FStar.Seq -FStar.Seq.Properties.slice_slice \
    +Lib.IntTypes +Lib.Sequence +Lib.Sequence.Lemmas +Lib.LoopCombinators +Lib.Vec.Lemmas'"


val lemma_repeat_gen_vec:
    w:pos
  -> n:nat
  -> a:(i:nat{i <= w * n} -> Type)
  -> a_vec:(i:nat{i <= n} -> Type)
  -> normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i))
  -> f:(i:nat{i < w * n} -> a i -> a (i + 1))
  -> f_v:(i:nat{i < n} -> a_vec i -> a_vec (i + 1))
  -> acc_v0:a_vec 0 ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc_v:a_vec i).
   (assert (w * (i + 1) <= w * n);
    normalize_v (i + 1) (f_v i acc_v) ==
    Loops.repeat_right (w * i) (w * (i + 1)) a f (normalize_v i acc_v))))
  (ensures
    normalize_v n (Loops.repeat_right 0 n a_vec f_v acc_v0) ==
    Loops.repeat_right 0 (w * n) a f (normalize_v 0 acc_v0))


val lemma_repeati_vec:
    #a:Type0
  -> #a_vec:Type0
  -> w:pos
  -> n:nat
  -> normalize_v:(a_vec -> a)
  -> f:(i:nat{i < w * n} -> a -> a)
  -> f_v:(i:nat{i < n} -> a_vec -> a_vec)
  -> acc_v0:a_vec ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc_v:a_vec).
   (assert (w * (i + 1) <= w * n);
    normalize_v (f_v i acc_v) ==
    Loops.repeat_right (w * i) (w * (i + 1)) (Loops.fixed_a a) f (normalize_v acc_v))))
  (ensures
    normalize_v (Loops.repeati n f_v acc_v0) ==
    Loops.repeati (w * n) f (normalize_v acc_v0))

///
///  Lemma
///   (repeat_gen_blocks (w * blocksize) 0 n inp a_vec f_v l_v acc_v0 ==
///    repeat_gen_blocks blocksize 0 (w * n + w) inp a f l (normalize_v 0 acc_v0))
///

val len_is_w_n_blocksize: w:pos -> blocksize:pos -> n:nat -> Lemma
  (let len = w * n * blocksize in
   len / blocksize = w * n /\ len / (w * blocksize) = n /\
   len % blocksize = 0 /\ len % (w * blocksize) = 0)


let repeat_gen_blocks_multi_vec_equiv_pre
  (#inp_t:Type0)
  (w:pos)
  (blocksize:pos{w * blocksize <= max_size_t})
  (n:nat)
  (hi_f:nat{w * n <= hi_f})
  (a:(i:nat{i <= hi_f} -> Type))
  (a_vec:(i:nat{i <= n} -> Type))
  (f:(i:nat{i < hi_f} -> lseq inp_t blocksize -> a i -> a (i + 1)))
  (f_v:(i:nat{i < n} -> lseq inp_t (w * blocksize) -> a_vec i -> a_vec (i + 1)))
  (normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i)))
  (i:nat{i < n})
  (b_v:lseq inp_t (w * blocksize))
  (acc_v:a_vec i)
  : prop
=
  Math.Lemmas.lemma_mult_le_right w (i + 1) n;

  normalize_v (i + 1) (f_v i b_v acc_v) ==
  repeat_gen_blocks_multi blocksize (w * i) hi_f w b_v a f (normalize_v i acc_v)


val lemma_repeat_gen_blocks_multi_vec:
    #inp_t:Type0
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> hi_f:nat{w * n <= hi_f}
  -> inp:seq inp_t{length inp = w * n * blocksize}
  -> a:(i:nat{i <= hi_f} -> Type)
  -> a_vec:(i:nat{i <= n} -> Type)
  -> f:(i:nat{i < hi_f} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> f_v:(i:nat{i < n} -> lseq inp_t (w * blocksize) -> a_vec i -> a_vec (i + 1))
  -> normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i))
  -> acc_v0:a_vec 0 ->
  Lemma
  (requires
    (forall (i:nat{i < n}) (b_v:lseq inp_t (w * blocksize)) (acc_v:a_vec i).
      repeat_gen_blocks_multi_vec_equiv_pre w blocksize n hi_f a a_vec f f_v normalize_v i b_v acc_v))
  (ensures
   (len_is_w_n_blocksize w blocksize n;
    normalize_v n (repeat_gen_blocks_multi (w * blocksize) 0 n n inp a_vec f_v acc_v0) ==
    repeat_gen_blocks_multi blocksize 0 hi_f (w * n) inp a f (normalize_v 0 acc_v0)))


let repeat_gen_blocks_vec_equiv_pre
  (#inp_t:Type0)
  (#c:Type0)
  (w:pos)
  (blocksize:pos{w * blocksize <= max_size_t})
  (n:nat)
  (a:(i:nat{i <= w * n + w} -> Type))
  (a_vec:(i:nat{i <= n} -> Type))
  (f:(i:nat{i < w * n + w} -> lseq inp_t blocksize -> a i -> a (i + 1)))
  (l:(i:nat{i <= w * n + w} -> len:nat{len < blocksize} -> lseq inp_t len -> a i -> c))
  (l_v:(i:nat{i <= n} -> len:nat{len < w * blocksize} -> lseq inp_t len -> a_vec i -> c))
  (normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i)))
  (rem:nat{rem < w * blocksize})
  (b_v:lseq inp_t rem)
  (acc_v:a_vec n)
  : prop
=
  l_v n rem b_v acc_v ==
  repeat_gen_blocks #inp_t #c blocksize (w * n) (w * n + w) b_v a f l (normalize_v n acc_v)


val lemma_repeat_gen_blocks_vec:
    #inp_t:Type0
  -> #c:Type0
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> inp:seq inp_t
  -> n:nat{n = length inp / (w * blocksize)}
  -> a:(i:nat{i <= w * n + w} -> Type)
  -> a_vec:(i:nat{i <= n} -> Type)
  -> f:(i:nat{i < w * n + w} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> l:(i:nat{i <= w * n + w} -> len:nat{len < blocksize} -> lseq inp_t len -> a i -> c)
  -> f_v:(i:nat{i < n} -> lseq inp_t (w * blocksize) -> a_vec i -> a_vec (i + 1))
  -> l_v:(i:nat{i <= n} -> len:nat{len < w * blocksize} -> lseq inp_t len -> a_vec i -> c)
  -> normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i))
  -> acc_v0:a_vec 0 ->
  Lemma
  (requires
    (forall (i:nat{i < n}) (b_v:lseq inp_t (w * blocksize)) (acc_v:a_vec i).
      repeat_gen_blocks_multi_vec_equiv_pre w blocksize n (w * n + w) a a_vec f f_v normalize_v i b_v acc_v) /\
    (forall (rem:nat{rem < w * blocksize}) (b_v:lseq inp_t rem) (acc_v:a_vec n).
      repeat_gen_blocks_vec_equiv_pre w blocksize n a a_vec f l l_v normalize_v rem b_v acc_v))
  (ensures
    repeat_gen_blocks (w * blocksize) 0 n inp a_vec f_v l_v acc_v0 ==
    repeat_gen_blocks blocksize 0 (w * n + w) inp a f l (normalize_v 0 acc_v0))

///
///  Lemma
///   (repeat_blocks (w * blocksize) inp f_v l_v acc_v0 ==
///    repeat_blocks blocksize inp f l (normalize_v acc_v0))
///

let repeat_blocks_multi_vec_equiv_pre
  (#a:Type0)
  (#b:Type0)
  (#b_vec:Type0)
  (w:pos)
  (blocksize:pos{w * blocksize <= max_size_t})
  (f:(lseq a blocksize -> b -> b))
  (f_v:(lseq a (w * blocksize) -> b_vec -> b_vec))
  (normalize_v:(b_vec -> b))
  (b_v:lseq a (w * blocksize))
  (acc_v:b_vec)
  : prop
=
  Math.Lemmas.cancel_mul_mod w blocksize;
  normalize_v (f_v b_v acc_v) == repeat_blocks_multi blocksize b_v f (normalize_v acc_v)


val lemma_repeat_blocks_multi_vec:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> inp:seq a{length inp % (w * blocksize) = 0 /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> f_v:(lseq a (w * blocksize) -> b_vec -> b_vec)
  -> normalize_v:(b_vec -> b)
  -> acc_v0:b_vec ->
  Lemma
  (requires
    (forall (b_v:lseq a (w * blocksize)) (acc_v:b_vec).
      repeat_blocks_multi_vec_equiv_pre w blocksize f f_v normalize_v b_v acc_v))
  (ensures
    normalize_v (repeat_blocks_multi #a #b_vec (w * blocksize) inp f_v acc_v0) ==
    repeat_blocks_multi #a #b blocksize inp f (normalize_v acc_v0))


let repeat_blocks_vec_equiv_pre
  (#a:Type0)
  (#b:Type0)
  (#b_vec:Type0)
  (#c:Type0)
  (w:pos)
  (blocksize:pos{w * blocksize <= max_size_t})
  (f:(lseq a blocksize -> b -> b))
  (l:(len:nat{len < blocksize} -> lseq a len -> b -> c))
  (l_v:(len:nat{len < w * blocksize} -> lseq a len -> b_vec -> c))
  (normalize_v:(b_vec -> b))
  (rem:nat{rem < w * blocksize})
  (b_v:lseq a rem)
  (acc_v:b_vec)
  : prop
=
  l_v rem b_v acc_v ==
  repeat_blocks blocksize b_v f l (normalize_v acc_v)


val lemma_repeat_blocks_vec:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> #c:Type0
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> inp:seq a
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:nat{len < blocksize} -> lseq a len -> b -> c)
  -> f_v:(lseq a (w * blocksize) -> b_vec -> b_vec)
  -> l_v:(len:nat{len < w * blocksize} -> lseq a len -> b_vec -> c)
  -> normalize_v:(b_vec -> b)
  -> acc_v0:b_vec ->
  Lemma
  (requires
    (forall (b_v:lseq a (w * blocksize)) (acc_v:b_vec).
      repeat_blocks_multi_vec_equiv_pre w blocksize f f_v normalize_v b_v acc_v) /\
    (forall (rem:nat{rem < w * blocksize}) (b_v:lseq a rem) (acc_v:b_vec).
      repeat_blocks_vec_equiv_pre w blocksize f l l_v normalize_v rem b_v acc_v))
  (ensures
    repeat_blocks (w * blocksize) inp f_v l_v acc_v0 ==
    repeat_blocks blocksize inp f l (normalize_v acc_v0))

///
///   Lemma
///    (map_blocks (w * blocksize) inp f_v l_v == map_blocks blocksize inp f l)
///

val lemma_f_map_ind: w:pos -> blocksize:pos -> n:nat -> i:nat{i < n} -> k:nat{k < w * blocksize} ->
  Lemma (w * i + k / blocksize < w * n)


let map_blocks_multi_vec_equiv_pre_k
  (#a:Type)
  (w:pos)
  (blocksize:pos{w * blocksize <= max_size_t})
  (n:nat)
  (hi_f:nat{w * n <= hi_f})
  (f:(i:nat{i < hi_f} -> lseq a blocksize -> lseq a blocksize))
  (f_v:(i:nat{i < n} -> lseq a (w * blocksize) -> lseq a (w * blocksize)))
  (i:nat{i < n})
  (b_v:lseq a (w * blocksize))
  (k:nat{k < w * blocksize})
  : prop
 =
  Math.Lemmas.cancel_mul_div w blocksize;
  let block = get_block_s #a #(w * blocksize) blocksize b_v k in
  lemma_f_map_ind w blocksize n i k;
  Seq.index (f_v i b_v) k == Seq.index (f (w * i + k / blocksize) block) (k % blocksize)


val lemma_map_blocks_multi_vec:
     #a:Type
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> inp:seq a{length inp = w * n * blocksize}
  -> f:(i:nat{i < w * n} -> lseq a blocksize -> lseq a blocksize)
  -> f_v:(i:nat{i < n} -> lseq a (w * blocksize) -> lseq a (w * blocksize)) ->
  Lemma
  (requires
    (forall (i:nat{i < n}) (b_v:lseq a (w * blocksize)) (k:nat{k < w * blocksize}).
      map_blocks_multi_vec_equiv_pre_k w blocksize n (w * n) f f_v i b_v k))
  (ensures
   (len_is_w_n_blocksize w blocksize n;
    map_blocks_multi (w * blocksize) n n inp f_v ==
    map_blocks_multi blocksize (w * n) (w * n) inp f))

#push-options "--z3rlimit_factor 2"
let map_blocks_vec_equiv_pre_k
  (#a:Type)
  (w:pos)
  (blocksize:pos{w * blocksize <= max_size_t})
  (n:nat)
  (f:(i:nat{i < w * n + w} -> lseq a blocksize -> lseq a blocksize))
  (l:(i:nat{i <= w * n + w} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem))
  (l_v:(i:nat{i <= n} -> rem:nat{rem < w * blocksize} -> lseq a rem -> lseq a rem))
  (rem:nat{rem < w * blocksize})
  (b_v:lseq a rem)
  (k:nat{k < rem})
  : prop
 =
  let j = w * n + k / blocksize in
  div_mul_lt blocksize k w;

  if k < rem / blocksize * blocksize then begin
    let block = get_block_s #a #rem blocksize b_v k in
    Seq.index (l_v n rem b_v) k == Seq.index (f j block) (k % blocksize) end
  else begin
    let block_l = get_last_s blocksize b_v in
    mod_div_lt blocksize k rem;
    assert (k % blocksize < rem % blocksize);
    Seq.index (l_v n rem b_v) k == Seq.index (l j (rem % blocksize) block_l) (k % blocksize) end
#pop-options

val lemma_map_blocks_vec:
     #a:Type
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> inp:seq a
  -> n:nat{n == length inp / (w * blocksize)}
  -> f:(i:nat{i < w * n + w} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= w * n + w} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> f_v:(i:nat{i < n} -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> l_v:(i:nat{i <= n} -> rem:nat{rem < w * blocksize} -> lseq a rem -> lseq a rem) ->
  Lemma
  (requires
    (forall (i:nat{i < n}) (b_v:lseq a (w * blocksize)) (k:nat{k < w * blocksize}).
      map_blocks_multi_vec_equiv_pre_k w blocksize n (w * n) f f_v i b_v k) /\
    (forall (rem:nat{rem < w * blocksize}) (b_v:lseq a rem) (k:nat{k < rem}).
      map_blocks_vec_equiv_pre_k w blocksize n f l l_v rem b_v k))
  (ensures
    map_blocks (w * blocksize) inp f_v l_v == map_blocks blocksize inp f l)
