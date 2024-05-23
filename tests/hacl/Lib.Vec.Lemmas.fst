module Lib.Vec.Lemmas

#set-options ""
#push-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 \
  --using_facts_from '-* +Prims +FStar.Pervasives +FStar.Math.Lemmas +FStar.Seq -FStar.Seq.Properties.slice_slice \
    +Lib.IntTypes +Lib.Sequence +Lib.Sequence.Lemmas +Lib.LoopCombinators +Lib.Vec.Lemmas'"


let rec lemma_repeat_gen_vec w n a a_vec normalize_v f f_v acc_v0 =
  if n = 0 then begin
    Loops.eq_repeat_right 0 n a_vec f_v acc_v0;
    Loops.eq_repeat_right 0 (w * n) a f (normalize_v 0 acc_v0) end
  else begin
    let next_p = Loops.repeat_right 0 (n - 1) a_vec f_v acc_v0 in
    let next_v = Loops.repeat_right 0 (w * (n - 1)) a f (normalize_v 0 acc_v0) in

    calc (==) {
      Loops.repeat_right 0 (w * n) a f (normalize_v 0 acc_v0);
      (==) { Loops.repeat_right_plus 0 (w * (n - 1)) (w * n) a f (normalize_v 0 acc_v0) }
      Loops.repeat_right (w * (n - 1)) (w * n) a f next_v;
      (==) { lemma_repeat_gen_vec w (n - 1) a a_vec normalize_v f f_v acc_v0 }
      Loops.repeat_right (w * (n - 1)) (w * n) a f (normalize_v (n - 1) next_p);
      (==) { }
      normalize_v n (f_v (n - 1) next_p);
      (==) { Loops.unfold_repeat_right 0 n a_vec f_v acc_v0 (n - 1) }
      normalize_v n (Loops.repeat_right 0 n a_vec f_v acc_v0);
    } end


let lemma_repeati_vec #a #a_vec w n normalize_v f f_v acc_v0 =
  lemma_repeat_gen_vec w n (Loops.fixed_a a) (Loops.fixed_a a_vec) (Loops.fixed_i normalize_v) f f_v acc_v0;
  Loops.repeati_def n f_v acc_v0;
  Loops.repeati_def (w * n) f (normalize_v acc_v0)


let len_is_w_n_blocksize w blocksize n =
  let len = w * n * blocksize in
  Math.Lemmas.cancel_mul_mod (w * n) blocksize;
  //assert (len % blocksize = 0);
  Math.Lemmas.cancel_mul_div (w * n) blocksize;
  //assert (len / blocksize = w * n);

  Math.Lemmas.paren_mul_right n w blocksize;
  Math.Lemmas.cancel_mul_mod n (w * blocksize);
  Math.Lemmas.cancel_mul_div n (w * blocksize)


////////////////////////
// Start of proof of lemma_repeat_gen_blocks_multi_vec
////////////////////////

val get_block_v:
    #a:Type0
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> s:seq a{length s = w * n * blocksize}
  -> i:nat{i < n} ->
  lseq a (w * blocksize)

let get_block_v #a w blocksize n s i =
  let blocksize_v = w * blocksize in
  Math.Lemmas.lemma_mult_le_right blocksize_v (i + 1) n;
  Math.Lemmas.paren_mul_right n w blocksize;
  let b_v = Seq.slice s (i * blocksize_v) ((i + 1) * blocksize_v) in
  b_v


val repeat_gen_blocks_slice_k:
    #inp_t:Type0
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> hi_f:nat{w * n <= hi_f}
  -> inp:seq inp_t{length inp = w * n * blocksize}
  -> a:(i:nat{i <= hi_f} -> Type)
  -> f:(i:nat{i < hi_f} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> i:nat{i < n /\ w * i + w <= w * n}
  -> k:nat{w * i <= k /\ k < w * i + w}
  -> acc:a k ->
  Lemma
   (let b_v = get_block_v w blocksize n inp i in
    let f_rep_s = repeat_gen_blocks_f blocksize (w * i) hi_f w b_v a f in
    Math.Lemmas.paren_mul_right w n blocksize;
    let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in

    f_rep_s k acc == f_rep k acc)

let repeat_gen_blocks_slice_k #inp_t w blocksize n hi_f inp a f i k acc =
  // Math.Lemmas.paren_mul_right w n blocksize;
  // let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in
  // Math.Lemmas.lemma_mult_le_right blocksize (k + 1) (w * n);
  // assert ((k + 1) * blocksize <= w * n * blocksize);
  // let block = Seq.slice inp (k * blocksize) (k * blocksize + blocksize) in
  // assert (f_rep k acc == f k block acc);

  let b_v = get_block_v w blocksize n inp i in
  //let f_rep_s = repeat_gen_blocks_f blocksize (w * i) hi_f w b_v a f in
  let i_b = k - w * i in
  Math.Lemmas.lemma_mult_le_right blocksize (i_b + 1) w;
  let block1 = Seq.slice b_v (i_b * blocksize) (i_b * blocksize + blocksize) in
  //assert (f_rep_s k acc == f k block1 acc);

  let blocksize_v = w * blocksize in
  calc (<=) {
    (i + 1) * blocksize_v;
    (<=) { Math.Lemmas.lemma_mult_le_right blocksize_v (i + 1) n }
    n * blocksize_v;
    (==) { Math.Lemmas.paren_mul_right n w blocksize }
    length inp;
    };

  calc (==) {
    i * blocksize_v + (k - w * i) * blocksize;
    (==) { Math.Lemmas.paren_mul_right i w blocksize }
    i * w * blocksize + (k - w * i) * blocksize;
    (==) { Math.Lemmas.distributivity_add_left (i * w) (k - w * i) blocksize }
    (i * w + (k - w * i)) * blocksize;
    (==) { }
    (i * w + (k + (- w * i))) * blocksize;
    (==) { Math.Lemmas.paren_add_right (i * w) k (- w * i) }
    (i * w + k + (- w * i)) * blocksize;
    (==) { Math.Lemmas.swap_mul i w } // JP: this was the important one that made the proof brittle
    k * blocksize;
    };

  Seq.Properties.slice_slice inp (i * blocksize_v) ((i + 1) * blocksize_v) (i_b * blocksize) (i_b * blocksize + blocksize)

val repeat_gen_blocks_slice:
    #inp_t:Type0
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> hi_f:nat{w * n <= hi_f}
  -> inp:seq inp_t{length inp = w * n * blocksize}
  -> a:(i:nat{i <= hi_f} -> Type)
  -> f:(i:nat{i < hi_f} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> i:nat{i < n /\ w * i + w <= w * n}
  -> acc:a (w * i) ->
  Lemma
   (let b_v = get_block_v w blocksize n inp i in
    let f_rep_s = repeat_gen_blocks_f blocksize (w * i) hi_f w b_v a f in
    Math.Lemmas.paren_mul_right w n blocksize;
    let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in

    Loops.repeat_right (w * i) (w * i + w) a f_rep acc ==
    Loops.repeat_right (w * i) (w * i + w) a f_rep_s acc)

let repeat_gen_blocks_slice #inp_t w blocksize n hi_f inp a f i acc =
  let b_v = get_block_v w blocksize n inp i in
  let f_rep_s = repeat_gen_blocks_f blocksize (w * i) hi_f w b_v a f in
  Math.Lemmas.paren_mul_right w n blocksize;
  let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in

  Classical.forall_intro_2 (repeat_gen_blocks_slice_k #inp_t w blocksize n hi_f inp a f i);
  repeat_right_extensionality w (w * i) a a f_rep f_rep_s acc


val repeat_gen_blocks_multi_vec_step:
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
  -> pre:squash(forall (i:nat{i < n}) (b_v:lseq inp_t (w * blocksize)) (acc_v:a_vec i).
      repeat_gen_blocks_multi_vec_equiv_pre w blocksize n hi_f a a_vec f f_v normalize_v i b_v acc_v)
  -> i:nat{i < n}
  -> acc_v:a_vec i ->
  Lemma
   (let blocksize_v = w * blocksize in
    len_is_w_n_blocksize w blocksize n;

    let f_rep_v = repeat_gen_blocks_f blocksize_v 0 n n inp a_vec f_v in
    let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in
    Math.Lemmas.lemma_mult_le_right w (i + 1) n;

    normalize_v (i + 1) (f_rep_v i acc_v) ==
    Loops.repeat_right (w * i) (w * (i + 1)) a f_rep (normalize_v i acc_v))

let repeat_gen_blocks_multi_vec_step #inp_t w blocksize n hi_f inp a a_vec f f_v normalize_v pre i acc_v =
  let b_v = get_block_v w blocksize n inp i in

  //let f_rep_v = repeat_gen_blocks_f blocksize_v 0 n n inp a_vec f_v in
  let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in
  Math.Lemmas.lemma_mult_le_left w (i + 1) n;
  let f_rep_s = repeat_gen_blocks_f blocksize (w * i) hi_f w b_v a f in

  let acc0 = normalize_v i acc_v in
  calc (==) {
    repeat_gen_blocks_multi blocksize (w * i) hi_f w b_v a f acc0;
    (==) { lemma_repeat_gen_blocks_multi blocksize (w * i) hi_f w b_v a f acc0 }
    Loops.repeat_right (w * i) (w * i + w) a f_rep_s acc0;
    (==) { repeat_gen_blocks_slice #inp_t w blocksize n hi_f inp a f i acc0 }
    Loops.repeat_right (w * i) (w * i + w) a f_rep acc0;
  };

  assert (repeat_gen_blocks_multi_vec_equiv_pre w blocksize n hi_f a a_vec f f_v normalize_v i b_v acc_v)

#push-options "--z3rlimit_factor 16 --retry 2"
let lemma_repeat_gen_blocks_multi_vec #inp_t w blocksize n hi_f inp a a_vec f f_v normalize_v acc_v0 =
  let len = length inp in
  let blocksize_v = w * blocksize in
  len_is_w_n_blocksize w blocksize n;

  let f_rep_v = repeat_gen_blocks_f blocksize_v 0 n n inp a_vec f_v in
  let f_rep   = repeat_gen_blocks_f blocksize 0 (w * n) (w * n) inp a f in

  let acc0 = normalize_v 0 acc_v0 in

  calc (==) {
    normalize_v n (repeat_gen_blocks_multi blocksize_v 0 n n inp a_vec f_v acc_v0);
    (==) { lemma_repeat_gen_blocks_multi blocksize_v 0 n n inp a_vec f_v acc_v0 }
    normalize_v n (Loops.repeat_right 0 n a_vec f_rep_v acc_v0);
    (==) {
      Classical.forall_intro_2 (repeat_gen_blocks_multi_vec_step w blocksize n hi_f inp a a_vec f f_v normalize_v ());
      lemma_repeat_gen_vec w n a a_vec normalize_v f_rep f_rep_v acc_v0 }
    Loops.repeat_right 0 (w * n) a f_rep acc0;
    (==) { lemma_repeat_gen_blocks_multi blocksize 0 (w * n) (w * n) inp a f acc0 }
    repeat_gen_blocks_multi blocksize 0 (w * n) (w * n) inp a f acc0;
    (==) { repeat_gen_blocks_multi_extensionality_zero blocksize 0 (w * n) hi_f (w * n) inp a a f f acc0 }
    repeat_gen_blocks_multi blocksize 0 hi_f (w * n) inp a f acc0;
  }
#pop-options

////////////////////////
// End of proof of lemma_repeat_gen_blocks_multi_vec
////////////////////////

#push-options "--z3rlimit 100 --retry 2"
let lemma_repeat_gen_blocks_vec #inp_t #c w blocksize inp n a a_vec f l f_v l_v normalize_v acc_v0 =
  let len = length inp in
  let blocksize_v = w * blocksize in
  let rem_v = len % blocksize_v in

  let res_v = repeat_gen_blocks blocksize_v 0 n inp a_vec f_v l_v acc_v0 in
  lemma_repeat_gen_blocks blocksize_v 0 n inp a_vec f_v l_v acc_v0;

  let len0 = w * n * blocksize in
  let blocks_v = Seq.slice inp 0 len0 in
  let last_v = Seq.slice inp len0 len in
  let acc_v = repeat_gen_blocks_multi blocksize_v 0 n n blocks_v a_vec f_v acc_v0 in
  assert (res_v == l_v n rem_v last_v acc_v);

  let acc0 = normalize_v 0 acc_v0 in
  calc (==) {
    l_v n rem_v last_v acc_v;
    (==) { assert (repeat_gen_blocks_vec_equiv_pre w blocksize n a a_vec f l l_v normalize_v rem_v last_v acc_v) }
    repeat_gen_blocks blocksize (w * n) (w * n + w) last_v a f l (normalize_v n acc_v);
    (==) { lemma_repeat_gen_blocks_multi_vec w blocksize n (w * n + w) blocks_v a a_vec f f_v normalize_v acc_v0 }
    repeat_gen_blocks blocksize (w * n) (w * n + w) last_v a f l
      (repeat_gen_blocks_multi blocksize 0 (w * n + w) (w * n) blocks_v a f acc0);
  };

  len_is_w_n_blocksize w blocksize n;
  //assert (len0 % blocksize = 0 /\ len0 / blocksize = w * n);
  //Math.Lemmas.paren_mul_right n w blocksize;
  //div_mul_lt blocksize rem_v w;
  //assert (rem_v / blocksize < w);
  repeat_gen_blocks_split blocksize len0 (w * n + w) 0 inp a f l acc0
#pop-options


val lemma_repeat_blocks_multi_vec_equiv_pre:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> hi_f:nat{w * n <= hi_f}
  -> f:(lseq a blocksize -> b -> b)
  -> f_v:(lseq a (w * blocksize) -> b_vec -> b_vec)
  -> normalize_v:(b_vec -> b)
  -> pre:squash (forall (b_v:lseq a (w * blocksize)) (acc_v:b_vec).
         repeat_blocks_multi_vec_equiv_pre w blocksize f f_v normalize_v b_v acc_v)
  -> i:nat{i < n}
  -> b_v:lseq a (w * blocksize)
  -> acc_v:b_vec ->
  Lemma
   (repeat_gen_blocks_multi_vec_equiv_pre #a w blocksize n hi_f
     (Loops.fixed_a b) (Loops.fixed_a b_vec)
     (Loops.fixed_i f) (Loops.fixed_i f_v)
     (Loops.fixed_i normalize_v) i b_v acc_v)

let lemma_repeat_blocks_multi_vec_equiv_pre #a #b #b_vec w blocksize n hi_f f f_v normalize_v pre i b_v acc_v =
  assert (repeat_blocks_multi_vec_equiv_pre w blocksize f f_v normalize_v b_v acc_v);
  Math.Lemmas.cancel_mul_mod w blocksize;
  assert (normalize_v (f_v b_v acc_v) == repeat_blocks_multi blocksize b_v f (normalize_v acc_v));
  Math.Lemmas.cancel_mul_div w blocksize;

  Math.Lemmas.lemma_mult_le_right w (i + 1) n;

  calc (==) {
    repeat_blocks_multi blocksize b_v f (normalize_v acc_v);
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi w blocksize b_v f (normalize_v acc_v) }
    repeat_gen_blocks_multi blocksize 0 w w b_v (Loops.fixed_a b) (Loops.fixed_i f) (normalize_v acc_v);
    (==) { repeat_gen_blocks_multi_extensionality_zero blocksize (w * i) hi_f w w b_v
           (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i f) (normalize_v acc_v) }
    repeat_gen_blocks_multi blocksize (w * i) hi_f w b_v (Loops.fixed_a b) (Loops.fixed_i f) (normalize_v acc_v);
    }


let lemma_repeat_blocks_multi_vec #a #b #b_vec w blocksize inp f f_v normalize_v acc_v0 =
  let blocksize_v = w * blocksize in
  let len = length inp in
  let nw = len / blocksize_v in
  len_is_w_n_blocksize w blocksize nw;

  let acc0 = normalize_v acc_v0 in

  calc (==) {
    normalize_v (repeat_blocks_multi #a #b_vec blocksize_v inp f_v acc_v0);
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi nw blocksize_v inp f_v acc_v0 }
    normalize_v (repeat_gen_blocks_multi blocksize_v 0 nw nw inp (Loops.fixed_a b_vec) (Loops.fixed_i f_v) acc_v0);
    (==) {
      Classical.forall_intro_3 (lemma_repeat_blocks_multi_vec_equiv_pre w blocksize nw (w * nw) f f_v normalize_v ());
      lemma_repeat_gen_blocks_multi_vec w blocksize nw (w * nw) inp (Loops.fixed_a b) (Loops.fixed_a b_vec)
	(Loops.fixed_i f) (Loops.fixed_i f_v) (Loops.fixed_i normalize_v) acc_v0 }
    repeat_gen_blocks_multi blocksize 0 (nw * w) (nw * w) inp (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi (nw * w) blocksize inp f acc0 }
    repeat_blocks_multi blocksize inp f acc0;
    }


val lemma_repeat_blocks_vec_equiv_pre:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> #c:Type0
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:nat{len < blocksize} -> lseq a len -> b -> c)
  -> l_v:(len:nat{len < w * blocksize} -> lseq a len -> b_vec -> c)
  -> normalize_v:(b_vec -> b)
  -> pre:squash (forall (rem:nat{rem < w * blocksize}) (b_v:lseq a rem) (acc_v:b_vec).
      repeat_blocks_vec_equiv_pre w blocksize f l l_v normalize_v rem b_v acc_v)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq a rem
  -> acc_v:b_vec ->
  Lemma
   (repeat_gen_blocks_vec_equiv_pre #a #c w blocksize n
     (Loops.fixed_a b) (Loops.fixed_a b_vec)
     (Loops.fixed_i f) (Loops.fixed_i l) (Loops.fixed_i l_v)
     (Loops.fixed_i normalize_v) rem b_v acc_v)

let lemma_repeat_blocks_vec_equiv_pre #a #b #b_vec #c w blocksize n f l l_v normalize_v pre rem b_v acc_v =
  let nb_rem = rem / blocksize in
  div_mul_lt blocksize rem w;
  assert (nb_rem < w);

  let acc0 = normalize_v acc_v in

  calc (==) {
    Loops.fixed_i l_v n rem b_v acc_v;
    (==) { }
    l_v rem b_v acc_v;
    (==) { assert (repeat_blocks_vec_equiv_pre w blocksize f l l_v normalize_v rem b_v acc_v) }
    repeat_blocks blocksize b_v f l acc0;
    (==) { repeat_blocks_is_repeat_gen_blocks nb_rem blocksize b_v f l acc0 }
    repeat_gen_blocks blocksize 0 nb_rem b_v (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0;
    (==) { repeat_gen_blocks_extensionality_zero blocksize (w * n) (w * n + w) nb_rem nb_rem b_v
           (Loops.fixed_a b) (Loops.fixed_a b)
	   (Loops.fixed_i f) (Loops.fixed_i l)
	   (Loops.fixed_i f) (Loops.fixed_i l) acc0 }
    repeat_gen_blocks blocksize (w * n) (w * n + w) b_v (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0;
    }


let lemma_repeat_blocks_vec #a #b #b_vec #c w blocksize inp f l f_v l_v normalize_v acc_v0 =
  let blocksize_v = w * blocksize in
  let nb_v = length inp / blocksize_v in

  calc (==) {
    repeat_blocks blocksize_v inp f_v l_v acc_v0;
    (==) { repeat_blocks_is_repeat_gen_blocks nb_v blocksize_v inp f_v l_v acc_v0 }
    repeat_gen_blocks blocksize_v 0 nb_v inp (Loops.fixed_a b_vec) (Loops.fixed_i f_v) (Loops.fixed_i l_v) acc_v0;
    (==) { Classical.forall_intro_3 (lemma_repeat_blocks_multi_vec_equiv_pre w blocksize nb_v (w * nb_v + w) f f_v normalize_v ());
           Classical.forall_intro_3 (lemma_repeat_blocks_vec_equiv_pre #a #b #b_vec #c w blocksize nb_v f l l_v normalize_v ());
           lemma_repeat_gen_blocks_vec w blocksize inp nb_v
             (Loops.fixed_a b) (Loops.fixed_a b_vec) (Loops.fixed_i f) (Loops.fixed_i l)
             (Loops.fixed_i f_v) (Loops.fixed_i l_v) (Loops.fixed_i normalize_v) acc_v0 }
    repeat_gen_blocks blocksize 0 (w * nb_v + w) inp (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) (normalize_v acc_v0);
    (==) { repeat_blocks_is_repeat_gen_blocks (w * nb_v + w) blocksize inp f l (normalize_v acc_v0) }
    repeat_blocks blocksize inp f l (normalize_v acc_v0);
  }


////////////////////////
// Start of proof of map_blocks_multi_vec lemma
////////////////////////

let lemma_f_map_ind w blocksize n i k =
  calc (<) {
    w * i + k / blocksize;
    (<) { div_mul_lt blocksize k w }
    w * i + w;
    (==) { Math.Lemmas.distributivity_add_right w i 1 }
    w * (i + 1);
    (<=) { Math.Lemmas.lemma_mult_le_left w (i + 1) n }
    w * n;
    }


val normalize_v_map:
    #a:Type
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> i:nat{i <= n}
  -> map_blocks_a a (w * blocksize) n i ->
  map_blocks_a a blocksize (w * n) (w * i)

let normalize_v_map #a w blocksize n i b =
  Math.Lemmas.lemma_mult_le_right w i n;
  b


#push-options "--z3rlimit 75"
let map_blocks_multi_vec_equiv_pre
  (#a:Type)
  (w:pos)
  (blocksize:pos{w * blocksize <= max_size_t})
  (n:nat)
  (hi_f:nat{w * n <= hi_f})
  (f:(i:nat{i < hi_f} -> lseq a blocksize -> lseq a blocksize))
  (f_v:(i:nat{i < n} -> lseq a (w * blocksize) -> lseq a (w * blocksize)))
  (i:nat{i < n})
  (b_v:lseq a (w * blocksize))
  (acc_v:map_blocks_a a (w * blocksize) n i)
  : prop
 =
  Math.Lemmas.lemma_mult_le_right w (i + 1) n;
  repeat_gen_blocks_map_f #a (w * blocksize) n f_v i b_v acc_v `Seq.equal`
  map_blocks_multi_acc blocksize (w * i) hi_f w b_v f acc_v
#pop-options

// It means the following
// Seq.append acc_v (f_v i b_v) ==
// map_blocks_multi_acc blocksize (w * i) (w * n) w b_v f acc_v


val lemma_map_blocks_multi_vec_equiv_pre_k:
    #a:Type
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> hi_f:nat{w * n <= hi_f}
  -> f:(i:nat{i < hi_f} -> lseq a blocksize -> lseq a blocksize)
  -> f_v:(i:nat{i < n} -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> i:nat{i < n}
  -> b_v:lseq a (w * blocksize)
  -> pre:squash (forall (k:nat{k < w * blocksize}). map_blocks_multi_vec_equiv_pre_k w blocksize n (w * n) f f_v i b_v k)
  -> acc_v:map_blocks_a a (w * blocksize) n i ->
  Lemma (map_blocks_multi_vec_equiv_pre #a w blocksize n hi_f f f_v i b_v acc_v)

#push-options "--z3rlimit 150"
let lemma_map_blocks_multi_vec_equiv_pre_k #a w blocksize n hi_f f f_v i b_v pre acc_v =
  //let lp = repeat_gen_blocks_map_f #a (w * blocksize) n f_v i b_v acc_v in
  //assert (lp == Seq.append acc_v (f_v i b_v));

  Math.Lemmas.lemma_mult_le_right w (i + 1) n;
  let f_sh = f_shift blocksize (w * i) hi_f w f in

  let aux (k:nat{k < w * blocksize}) : Lemma (Seq.index (f_v i b_v) k == Seq.index (map_blocks_multi blocksize w w b_v f_sh) k) =
    Math.Lemmas.cancel_mul_div w blocksize;
    let block = get_block_s #a #(w * blocksize) blocksize b_v k in
    let j = k / blocksize in // j < w
    div_mul_lt blocksize k w;

    calc (==) {
      Seq.index (map_blocks_multi blocksize w w b_v f_sh) k;
      (==) { index_map_blocks_multi blocksize w w b_v f_sh k }
      Seq.index (f_sh j block) (k % blocksize);
      (==) { assert (map_blocks_multi_vec_equiv_pre_k w blocksize n hi_f f f_v i b_v k) }
      Seq.index (f_v i b_v) k;
    } in

  calc (==) {
    map_blocks_multi_acc blocksize (w * i) hi_f w b_v f acc_v;
    (==) { map_blocks_multi_acc_is_map_blocks_multi blocksize (w * i) hi_f w b_v f acc_v }
    Seq.append acc_v (map_blocks_multi blocksize w w b_v f_sh);
    (==) { Classical.forall_intro aux; Seq.lemma_eq_intro (f_v i b_v) (map_blocks_multi blocksize w w b_v f_sh) }
    Seq.append acc_v (f_v i b_v);
    (==) { Seq.lemma_eq_intro (Seq.append acc_v (f_v i b_v)) (repeat_gen_blocks_map_f #a (w * blocksize) n f_v i b_v acc_v) }
    repeat_gen_blocks_map_f #a (w * blocksize) n f_v i b_v acc_v;
    }
#pop-options

val lemma_map_blocks_multi_vec_equiv_pre:
    #a:Type
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> hi_f:nat{w * n <= hi_f}
  -> f:(i:nat{i < hi_f} -> lseq a blocksize -> lseq a blocksize)
  -> f_v:(i:nat{i < n} -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> pre:squash (forall (i:nat{i < n}) (b_v:lseq a (w * blocksize)) (k:nat{k < w * blocksize}).
      map_blocks_multi_vec_equiv_pre_k w blocksize n (w * n) f f_v i b_v k)
  -> i:nat{i < n}
  -> b_v:lseq a (w * blocksize)
  -> acc_v:map_blocks_a a (w * blocksize) n i ->
  Lemma
   (repeat_gen_blocks_multi_vec_equiv_pre #a w blocksize n hi_f
     (map_blocks_a a blocksize hi_f)
     (map_blocks_a a (w * blocksize) n)
     (repeat_gen_blocks_map_f blocksize hi_f f)
     (repeat_gen_blocks_map_f (w * blocksize) n f_v)
     (normalize_v_map #a w blocksize n) i b_v acc_v)

#push-options "--z3rlimit 75"
let lemma_map_blocks_multi_vec_equiv_pre #a w blocksize n hi_f f f_v pre i b_v acc_v =
  lemma_map_blocks_multi_vec_equiv_pre_k #a w blocksize n hi_f f f_v i b_v pre acc_v;
  Math.Lemmas.cancel_mul_div w blocksize;
  Math.Lemmas.cancel_mul_mod w blocksize;
  Math.Lemmas.lemma_mult_le_right w (i + 1) n;
  map_blocks_multi_acc_is_repeat_gen_blocks_multi blocksize (w * i) hi_f w b_v f acc_v
#pop-options

let lemma_map_blocks_multi_vec #a w blocksize n inp f f_v =
  let blocksize_v = w * blocksize in
  len_is_w_n_blocksize w blocksize n;

  calc (==) {
    map_blocks_multi blocksize_v n n inp f_v;
    (==) { map_blocks_multi_acc_is_map_blocks_multi0 blocksize_v n n inp f_v }
    map_blocks_multi_acc blocksize_v 0 n n inp f_v Seq.empty;
    (==) { map_blocks_multi_acc_is_repeat_gen_blocks_multi blocksize_v 0 n n inp f_v Seq.empty }
    repeat_gen_blocks_multi blocksize_v 0 n n inp
     (map_blocks_a a blocksize_v n)
     (repeat_gen_blocks_map_f blocksize_v n f_v) Seq.empty;
    (==) { Classical.forall_intro_3 (lemma_map_blocks_multi_vec_equiv_pre #a w blocksize n (w * n) f f_v ());
           lemma_repeat_gen_blocks_multi_vec w blocksize n (w * n) inp
             (map_blocks_a a blocksize (w * n)) (map_blocks_a a blocksize_v n)
             (repeat_gen_blocks_map_f blocksize (w * n) f)
             (repeat_gen_blocks_map_f blocksize_v n f_v)
             (normalize_v_map #a w blocksize n) Seq.empty }
    repeat_gen_blocks_multi blocksize 0 (w * n) (w * n) inp
     (map_blocks_a a blocksize (w * n))
     (repeat_gen_blocks_map_f blocksize (w * n) f) Seq.empty;
    (==) { map_blocks_multi_acc_is_repeat_gen_blocks_multi blocksize 0 (w * n) (w * n) inp f Seq.empty }
    map_blocks_multi_acc blocksize 0 (w * n) (w * n) inp f Seq.empty;
    (==) { map_blocks_multi_acc_is_map_blocks_multi0 blocksize (w * n) (w * n) inp f }
    map_blocks_multi blocksize (w * n) (w * n) inp f;
  }

////////////////////////
// End of proof of map_blocks_multi_vec lemma
////////////////////////

#push-options "--z3rlimit 75"
let map_blocks_vec_equiv_pre
  (#a:Type)
  (w:pos)
  (blocksize:pos{w * blocksize <= max_size_t})
  (n:nat)
  (f:(i:nat{i < w * n + w} -> lseq a blocksize -> lseq a blocksize))
  (l:(i:nat{i <= w * n + w} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem))
  (l_v:(i:nat{i <= n} -> rem:nat{rem < w * blocksize} -> lseq a rem -> lseq a rem))
  (rem:nat{rem < w * blocksize})
  (b_v:lseq a rem)
  (acc_v:map_blocks_a a (w * blocksize) n n)
  : prop
 =
  //Math.Lemmas.small_mod rem (w * blocksize);
  //Math.Lemmas.small_div rem (w * blocksize);
  repeat_gen_blocks_map_l_length (w * blocksize) n l_v n rem b_v acc_v;

  repeat_gen_blocks_map_l (w * blocksize) n l_v n rem b_v acc_v `Seq.equal`
  map_blocks_acc blocksize (w * n) (w * n + w) b_v f l acc_v
#pop-options

val lemma_map_blocks_vec_equiv_pre_k_aux:
    #a:Type
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> f:(i:nat{i < w * n + w} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= w * n + w} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> l_v:(i:nat{i <= n} -> rem:nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq a rem
  -> pre:squash (forall (rem:nat{rem < w * blocksize}) (b_v:lseq a rem) (k:nat{k < rem}).
      map_blocks_vec_equiv_pre_k w blocksize n f l l_v rem b_v k)
  -> k:nat{k < rem} ->
  Lemma
   (let nb = rem / blocksize in
    let f_sh = f_shift blocksize (w * n) (w * n + w) nb f in
    let l_sh = l_shift blocksize (w * n) (w * n + w) nb l in
    Seq.index (l_v n rem b_v) k == Seq.index (map_blocks blocksize b_v f_sh l_sh) k)

let lemma_map_blocks_vec_equiv_pre_k_aux #a w blocksize n f l l_v rem b_v pre k =
  let nb = rem / blocksize in
  let f_sh = f_shift blocksize (w * n) (w * n + w) nb f in
  let l_sh = l_shift blocksize (w * n) (w * n + w) nb l in

  let j = w * n + k / blocksize in
  div_mul_lt blocksize k w;

  if k < rem / blocksize * blocksize then begin
    let block = get_block_s #a #rem blocksize b_v k in
    calc (==) {
      Seq.index (map_blocks blocksize b_v f_sh l_sh) k;
      (==) { index_map_blocks blocksize b_v f_sh l_sh k }
      Seq.index (f j block) (k % blocksize);
      (==) { assert (map_blocks_vec_equiv_pre_k w blocksize n f l l_v rem b_v k) }
      Seq.index (l_v n rem b_v) k;
    }  end
  else begin
    let block_l = get_last_s #_ #rem blocksize b_v in
    mod_div_lt blocksize k rem;
    calc (==) {
      Seq.index (map_blocks blocksize b_v f_sh l_sh) k;
      (==) { index_map_blocks blocksize b_v f_sh l_sh k }
      Seq.index (l_sh (rem / blocksize) (rem % blocksize) block_l) (k % blocksize);
      (==) { div_interval blocksize (rem / blocksize) k }
      Seq.index (l j (rem % blocksize) block_l) (k % blocksize);
      (==) { assert (map_blocks_vec_equiv_pre_k w blocksize n f l l_v rem b_v k) }
      Seq.index (l_v n rem b_v) k;
    } end


val lemma_map_blocks_vec_equiv_pre_k:
    #a:Type
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> f:(i:nat{i < w * n + w} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= w * n + w} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> l_v:(i:nat{i <= n} -> rem:nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq a rem
  -> pre:squash (forall (rem:nat{rem < w * blocksize}) (b_v:lseq a rem) (k:nat{k < rem}).
      map_blocks_vec_equiv_pre_k w blocksize n f l l_v rem b_v k)
  -> acc_v:map_blocks_a a (w * blocksize) n n ->
  Lemma (map_blocks_vec_equiv_pre w blocksize n f l l_v rem b_v acc_v)

let lemma_map_blocks_vec_equiv_pre_k #a w blocksize n f l l_v rem b_v pre acc_v =
  let nb = rem / blocksize in
  let f_sh = f_shift blocksize (w * n) (w * n + w) nb f in
  let l_sh = l_shift blocksize (w * n) (w * n + w) nb l in

  if rem = 0 then begin
    calc (==) {
      map_blocks_acc blocksize (w * n) (w * n + w) b_v f l acc_v;
      (==) { map_blocks_acc_is_map_blocks blocksize (w * n) (w * n + w) b_v f l acc_v}
      Seq.append acc_v (map_blocks blocksize b_v f_sh l_sh);
      (==) { map_blocks_is_empty blocksize nb b_v f_sh l_sh }
      Seq.append acc_v Seq.empty;
      (==) { Seq.Base.append_empty_r acc_v }
      acc_v;
      (==) { }
      repeat_gen_blocks_map_l (w * blocksize) n l_v n rem b_v acc_v;
      } end
  else begin
    calc (==) {
      map_blocks_acc blocksize (w * n) (w * n + w) b_v f l acc_v;
      (==) { map_blocks_acc_is_map_blocks blocksize (w * n) (w * n + w) b_v f l acc_v}
      Seq.append acc_v (map_blocks blocksize b_v f_sh l_sh);
      (==) { Classical.forall_intro (lemma_map_blocks_vec_equiv_pre_k_aux #a w blocksize n f l l_v rem b_v ());
             Seq.lemma_eq_intro (l_v n rem b_v) (map_blocks blocksize b_v f_sh l_sh) }
      Seq.append acc_v (l_v n rem b_v);
      (==) { }
      repeat_gen_blocks_map_l (w * blocksize) n l_v n rem b_v acc_v;
      } end


val lemma_map_blocks_vec_equiv_pre:
    #a:Type
  -> w:pos
  -> blocksize:pos{w * blocksize <= max_size_t}
  -> n:nat
  -> f:(i:nat{i < w * n + w} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= w * n + w} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> l_v:(i:nat{i <= n} -> rem:nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> pre:squash (forall (rem:nat{rem < w * blocksize}) (b_v:lseq a rem) (k:nat{k < rem}).
      map_blocks_vec_equiv_pre_k w blocksize n f l l_v rem b_v k)
  -> rem:nat{rem < w * blocksize}
  -> b_v:lseq a rem
  -> acc_v:map_blocks_a a (w * blocksize) n n ->
  Lemma
    (repeat_gen_blocks_vec_equiv_pre w blocksize n
      (map_blocks_a a blocksize (w * n + w))
      (map_blocks_a a (w * blocksize) n)
      (repeat_gen_blocks_map_f blocksize (w * n + w) f)
      (repeat_gen_blocks_map_l blocksize (w * n + w) l)
      (repeat_gen_blocks_map_l (w * blocksize) n l_v)
      (normalize_v_map #a w blocksize n) rem b_v acc_v)

let lemma_map_blocks_vec_equiv_pre #a w blocksize n f l l_v pre rem b_v acc_v =
  lemma_map_blocks_vec_equiv_pre_k #a w blocksize n f l l_v rem b_v pre acc_v;
  Math.Lemmas.small_mod rem (w * blocksize);
  Math.Lemmas.small_div rem (w * blocksize);
  assert (w * n >= 0);
  map_blocks_acc_is_repeat_gen_blocks blocksize (w * n) (w * n + w) b_v f l acc_v


let lemma_map_blocks_vec #a w blocksize inp n f l f_v l_v =
  let len = length inp in
  let blocksize_v = w * blocksize in

  calc (==) {
    map_blocks_acc blocksize_v 0 n inp f_v l_v Seq.empty;
    (==) { map_blocks_acc_is_repeat_gen_blocks blocksize_v 0 n inp f_v l_v Seq.empty }
    repeat_gen_blocks blocksize_v 0 n inp
      (map_blocks_a a blocksize_v n)
      (repeat_gen_blocks_map_f blocksize_v n f_v)
      (repeat_gen_blocks_map_l blocksize_v n l_v)
      Seq.empty;

    (==) {
      Classical.forall_intro_3 (lemma_map_blocks_multi_vec_equiv_pre #a w blocksize n (w * n + w) f f_v ());
      Classical.forall_intro_3 (lemma_map_blocks_vec_equiv_pre #a w blocksize n f l l_v ());
      lemma_repeat_gen_blocks_vec w blocksize inp n
    	(map_blocks_a a blocksize (w * n + w))
    	(map_blocks_a a (w * blocksize) n)
    	(repeat_gen_blocks_map_f blocksize (w * n + w) f)
    	(repeat_gen_blocks_map_l blocksize (w * n + w) l)
    	(repeat_gen_blocks_map_f (w * blocksize) n f_v)
    	(repeat_gen_blocks_map_l (w * blocksize) n l_v)
    	(normalize_v_map #a w blocksize n) Seq.empty }

    repeat_gen_blocks blocksize 0 (w * n + w) inp
      (map_blocks_a a blocksize (w * n + w))
      (repeat_gen_blocks_map_f blocksize (w * n + w) f)
      (repeat_gen_blocks_map_l blocksize (w * n + w) l)
      Seq.empty;

    (==) { map_blocks_acc_is_repeat_gen_blocks blocksize 0 (w * n + w) inp f l Seq.empty }
    map_blocks_acc blocksize 0 (w * n + w) inp f l Seq.empty;
  };

  map_blocks_acc_is_map_blocks0 blocksize_v n inp f_v l_v;
  map_blocks_acc_is_map_blocks0 blocksize (w * n + w) inp f l
