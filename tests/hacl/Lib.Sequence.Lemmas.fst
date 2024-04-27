module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 \
  --using_facts_from '-* +Prims +FStar.Pervasives +FStar.Math.Lemmas +FStar.Seq \
    +Lib.IntTypes +Lib.Sequence +Lib.Sequence.Lemmas +Lib.LoopCombinators'"


let rec repeati_extensionality #a n f g acc0 =
  if n = 0 then begin
    Loops.eq_repeati0 n f acc0;
    Loops.eq_repeati0 n g acc0 end
  else begin
    Loops.unfold_repeati n f acc0 (n-1);
    Loops.unfold_repeati n g acc0 (n-1);
    repeati_extensionality #a (n-1) f g acc0 end


let rec repeat_right_extensionality n lo a_f a_g f g acc0 =
  if n = 0 then begin
    Loops.eq_repeat_right lo (lo + n) a_f f acc0;
    Loops.eq_repeat_right lo (lo + n) a_g g acc0 end
  else begin
    Loops.unfold_repeat_right lo (lo + n) a_f f acc0 (lo + n - 1);
    Loops.unfold_repeat_right lo (lo + n) a_g g acc0 (lo + n - 1);
    repeat_right_extensionality (n - 1) lo a_f a_g f g acc0 end


let rec repeat_gen_right_extensionality n lo_g a_f a_g f g acc0 =
  if n = 0 then begin
    Loops.eq_repeat_right 0 n a_f f acc0;
    Loops.eq_repeat_right lo_g (lo_g+n) a_g g acc0 end
  else begin
    Loops.unfold_repeat_right 0 n a_f f acc0 (n-1);
    Loops.unfold_repeat_right lo_g (lo_g+n) a_g g acc0 (lo_g+n-1);
    repeat_gen_right_extensionality (n-1) lo_g a_f a_g f g acc0 end


let repeati_right_extensionality #a n lo_g f g acc0 =
  repeat_gen_right_extensionality n lo_g (Loops.fixed_a a) (Loops.fixed_a a) f g acc0


let repeati_right_shift #a n f g acc0 =
  let acc1 = g 0 acc0 in
  repeati_right_extensionality n 1 f g acc1;
  // Got:
  // repeat_right 0 n (fun _ -> a) f acc1 == repeat_right 1 (n + 1) (fun _ -> a) g acc1
  Loops.repeati_def n f acc1;
  // Got:
  // repeati n f acc1 == repeat_right 0 n (fun _ -> a) f acc1
  Loops.repeat_right_plus 0 1 (n + 1) (Loops.fixed_a a) g acc0;
  // Got:
  // repeat_right 0 (n + 1) (fixed_a a) g acc0 ==
  //   repeat_right 1 (n + 1) (fixed_a a) g (repeat_right 0 1 (fixed_a a) g acc0)
  Loops.unfold_repeat_right 0 (n + 1) (Loops.fixed_a a) g acc0 0;
  Loops.eq_repeat_right 0 (n + 1) (Loops.fixed_a a) g acc0;
  Loops.repeati_def (n + 1) g acc0


let repeat_gen_blocks_multi #inp_t blocksize mi hi n inp a f acc0 =
  Loops.repeat_right mi (mi + n) a (repeat_gen_blocks_f blocksize mi hi n inp a f) acc0


let lemma_repeat_gen_blocks_multi #inp_t blocksize mi hi n inp a f acc0 = ()


let repeat_gen_blocks #inp_t #c blocksize mi hi inp a f l acc0 =
  let len = length inp in
  let nb = len / blocksize in
  let rem = len % blocksize in
  let blocks = Seq.slice inp 0 (nb * blocksize) in
  let last = Seq.slice inp (nb * blocksize) len in
  Math.Lemmas.cancel_mul_div nb blocksize;
  let acc = repeat_gen_blocks_multi #inp_t blocksize mi hi nb blocks a f acc0 in
  l (mi + nb) rem last acc


let lemma_repeat_gen_blocks #inp_t #c blocksize mi hi inp a f l acc0 = ()


let repeat_gen_blocks_multi_extensionality_zero #inp_t blocksize mi hi_f hi_g n inp a_f a_g f g acc0 =
  let f_rep = repeat_gen_blocks_f blocksize mi hi_f n inp a_f f in
  let g_rep = repeat_gen_blocks_f blocksize 0 hi_g n inp a_g g in
  repeat_gen_right_extensionality n mi a_g a_f g_rep f_rep acc0


let repeat_gen_blocks_extensionality_zero #inp_t #c blocksize mi hi_f hi_g n inp a_f a_g f l_f g l_g acc0 =
  let len = length inp in
  let rem = len % blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  Math.Lemmas.cancel_mul_mod n blocksize;
  let blocks = Seq.slice inp 0 (n * blocksize) in
  let block_l = Seq.slice inp (n * blocksize) len in
  let acc_f = repeat_gen_blocks_multi blocksize mi hi_f n blocks a_f f acc0 in
  let acc_g = repeat_gen_blocks_multi blocksize 0 hi_g n blocks a_g g acc0 in

  calc (==) {
    repeat_gen_blocks blocksize mi hi_f inp a_f f l_f acc0;
    (==) { }
    l_f (mi + n) rem block_l acc_f;
    (==) { repeat_gen_blocks_multi_extensionality_zero #inp_t blocksize mi hi_f hi_g n blocks a_f a_g f g acc0 }
    l_f (mi + n) rem block_l acc_g;
    (==) { }
    l_g n rem block_l acc_g;
    (==) { }
    repeat_gen_blocks blocksize 0 hi_g inp a_g g l_g acc0;
    }


let len0_div_bs blocksize len len0 =
  let k = len0 / blocksize in
  calc (==) {
    k + (len - len0) / blocksize;
    == { Math.Lemmas.lemma_div_exact len0 blocksize }
    k + (len - k * blocksize) / blocksize;
    == { Math.Lemmas.division_sub_lemma len blocksize k }
    k + len / blocksize - k;
    == { }
    len / blocksize;
  }


let split_len_lemma0 blocksize n len0 =
  let len = n * blocksize in
  let len1 = len - len0 in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  Math.Lemmas.cancel_mul_mod n blocksize;
  //assert (len % blocksize = 0);

  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
  //assert (len1 % blocksize = 0);

  Math.Lemmas.lemma_div_exact len0 blocksize;
  //assert (n0 * blocksize = len0);

  Math.Lemmas.lemma_div_exact len1 blocksize;
  //assert (n1 * blocksize = len1);

  len0_div_bs blocksize len len0
  //assert (n0 + n1 = n)


let split_len_lemma blocksize len len0 =
  let len1 = len - len0 in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  let n = len / blocksize in

  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
  //assert (len % blocksize = len1 % blocksize);

  Math.Lemmas.lemma_div_exact len0 blocksize;
  //assert (n0 * blocksize = len0);

  len0_div_bs blocksize len len0
  //assert (n0 + n1 = n)

////////////////////////
// Start of proof of repeat_gen_blocks_multi_split lemma
////////////////////////

val aux_repeat_bf_s0:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq inp_t{len0 <= length inp /\ length inp == n * blocksize}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> i:nat{mi <= i /\ i < mi + len0 / blocksize /\ i < hi} // i < hi is needed to type-check the definition
  -> acc:a i ->
  Lemma
   (let len = length inp in
    let n0 = len0 / blocksize in
    split_len_lemma0 blocksize n len0;

    let t0 = Seq.slice inp 0 len0 in
    let repeat_bf_s0 = repeat_gen_blocks_f blocksize mi hi n0 t0 a f in
    let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

    repeat_bf_s0 i acc == repeat_bf_t i acc)

let aux_repeat_bf_s0 #inp_t blocksize len0 mi hi n inp a f i acc =
  let len = length inp in
  let n0 = len0 / blocksize in
  split_len_lemma0 blocksize n len0;

  let t0 = Seq.slice inp 0 len0 in
  let repeat_bf_s0 = repeat_gen_blocks_f blocksize mi hi n0 t0 a f in
  let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

  let i_b = i - mi in
  Math.Lemmas.lemma_mult_le_right blocksize (i_b + 1) n;
  let block = Seq.slice inp (i_b * blocksize) (i_b * blocksize + blocksize) in
  assert (repeat_bf_t i acc == f i block acc);

  Math.Lemmas.lemma_mult_le_right blocksize (i_b + 1) n0;
  Seq.slice_slice inp 0 len0 (i_b * blocksize) (i_b * blocksize + blocksize);
  assert (repeat_bf_s0 i acc == f i block acc)


val aux_repeat_bf_s1:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq inp_t{len0 <= length inp /\ length inp == n * blocksize}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> i:nat{mi + len0 / blocksize <= i /\ i < mi + n}
  -> acc:a i ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    let n0 = len0 / blocksize in
    let n1 = len1 / blocksize in
    split_len_lemma0 blocksize n len0;

    let t1 = Seq.slice inp len0 len in
    let repeat_bf_s1 = repeat_gen_blocks_f blocksize (mi + n0) hi n1 t1 a f in
    let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

    repeat_bf_s1 i acc == repeat_bf_t i acc)

let aux_repeat_bf_s1 #inp_t blocksize len0 mi hi n inp a f i acc =
  let len = length inp in
  let len1 = len - len0 in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  split_len_lemma0 blocksize n len0;

  let t1 = Seq.slice inp len0 len in
  let repeat_bf_s1 = repeat_gen_blocks_f blocksize (mi + n0) hi n1 t1 a f in
  let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

  let i_b = i - mi in
  Math.Lemmas.lemma_mult_le_right blocksize (i_b + 1) n;
  let block = Seq.slice inp (i_b * blocksize) (i_b * blocksize + blocksize) in
  assert (repeat_bf_t i acc == f i block acc);

  let i_b1 = i - mi - n0 in
  calc (<=) {
    i_b1 * blocksize + blocksize;
    (<=) { Math.Lemmas.lemma_mult_le_right blocksize (i_b1 + 1) n1 }
    n1 * blocksize;
    (==) { Math.Lemmas.div_exact_r len1 blocksize }
    len1;
    };

  calc (==) {
    len0 + i_b1 * blocksize;
    (==) { Math.Lemmas.div_exact_r len0 blocksize }
    n0 * blocksize + i_b1 * blocksize;
    (==) { Math.Lemmas.distributivity_add_left n0 i_b1 blocksize }
    (n0 + i_b1) * blocksize;
    };

  Seq.slice_slice inp len0 len (i_b1 * blocksize) (i_b1 * blocksize + blocksize);
  assert (repeat_bf_s1 i acc == f i block acc)


let repeat_gen_blocks_multi_split #inp_t blocksize len0 mi hi n inp a f acc0 =
  let len = length inp in
  let len1 = len - len0 in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  split_len_lemma0 blocksize n len0;

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  let repeat_bf_s0 = repeat_gen_blocks_f blocksize mi hi n0 t0 a f in
  let repeat_bf_s1 = repeat_gen_blocks_f blocksize (mi + n0) hi n1 t1 a f in
  let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

  let acc1 : a (mi + n0) = repeat_gen_blocks_multi blocksize mi hi n0 t0 a f acc0 in
  //let acc2 = repeat_gen_blocks_multi blocksize (mi + n0) hi n1 t1 a f acc1 in

  calc (==) {
    repeat_gen_blocks_multi blocksize mi hi n0 t0 a f acc0;
    (==) { }
    Loops.repeat_right mi (mi + n0) a repeat_bf_s0 acc0;
    (==) { Classical.forall_intro_2 (aux_repeat_bf_s0 #inp_t blocksize len0 mi hi n inp a f);
           repeat_right_extensionality n0 mi a a repeat_bf_s0 repeat_bf_t acc0 }
    Loops.repeat_right mi (mi + n0) a repeat_bf_t acc0;
    };

  calc (==) {
    repeat_gen_blocks_multi blocksize (mi + n0) hi n1 t1 a f acc1;
    (==) { }
    Loops.repeat_right (mi + n0) (mi + n) a repeat_bf_s1 acc1;
    (==) { Classical.forall_intro_2 (aux_repeat_bf_s1 #inp_t blocksize len0 mi hi n inp a f);
           repeat_right_extensionality n1 (mi + n0) a a repeat_bf_s1 repeat_bf_t acc1 }
    Loops.repeat_right (mi + n0) (mi + n) a repeat_bf_t acc1;
    (==) { Loops.repeat_right_plus mi (mi + n0) (mi + n) a repeat_bf_t acc0 }
    Loops.repeat_right mi (mi + n) a repeat_bf_t acc0;
    (==) { }
    repeat_gen_blocks_multi blocksize mi hi n inp a f acc0;
  }

////////////////////////
// End of proof of repeat_gen_blocks_multi_split lemma
////////////////////////


val repeat_gen_blocks_multi_split_slice:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> mi:nat
  -> hi:nat
  -> inp:seq inp_t{len0 <= length inp / blocksize * blocksize /\ mi + length inp / blocksize <= hi}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> acc0:a mi ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    let n = len / blocksize in
    let n0 = len0 / blocksize in
    let n1 = len1 / blocksize in
    split_len_lemma blocksize len len0;
    split_len_lemma0 blocksize n len0;

    let blocks = Seq.slice inp 0 (n * blocksize) in
    let t0 = Seq.slice inp 0 len0 in
    let t1 = Seq.slice inp len0 (n * blocksize) in

    let acc1 : a (mi + n0) = repeat_gen_blocks_multi blocksize mi hi n0 t0 a f acc0 in
    repeat_gen_blocks_multi blocksize mi hi n blocks a f acc0 ==
    repeat_gen_blocks_multi blocksize (mi + n0) hi n1 t1 a f acc1)

let repeat_gen_blocks_multi_split_slice #inp_t blocksize len0 mi hi inp a f acc0 =
  let len = length inp in
  let n = len / blocksize in
  split_len_lemma blocksize len len0;
  let blocks = Seq.slice inp 0 (n * blocksize) in
  split_len_lemma0 blocksize n len0;
  repeat_gen_blocks_multi_split blocksize len0 mi hi n blocks a f acc0


val slice_slice_last:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq inp_t{len0 <= length inp} ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    let n = len / blocksize in
    let n1 = len1 / blocksize in
    let t1 = Seq.slice inp len0 len in
    Seq.slice t1 (n1 * blocksize) len1 `Seq.equal`
    Seq.slice inp (n * blocksize) len)

let slice_slice_last #inp_t blocksize len0 inp =
  let len = length inp in
  let len1 = len - len0 in
  let n = len / blocksize in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in

  calc (==) {
    len0 + n1 * blocksize;
    (==) { len0_div_bs blocksize len len0 }
    len0 + (n - n0) * blocksize;
    (==) { Math.Lemmas.distributivity_sub_left n n0 blocksize }
    len0 + n * blocksize - n0 * blocksize;
    (==) { Math.Lemmas.div_exact_r len0 blocksize }
    n * blocksize;
  };

  let t1 = Seq.slice inp len0 len in
  Seq.slice_slice inp len0 len (n1 * blocksize) len1


val len0_le_len_fraction: blocksize:pos -> len:nat -> len0:nat ->
  Lemma
  (requires len0 <= len /\ len0 % blocksize = 0)
  (ensures  len0 <= len / blocksize * blocksize)

let len0_le_len_fraction blocksize len len0 =
  Math.Lemmas.lemma_div_le len0 len blocksize;
  Math.Lemmas.lemma_mult_le_right blocksize (len0 / blocksize) (len / blocksize)

#push-options "--z3rlimit 100"
let repeat_gen_blocks_split #inp_t #c blocksize len0 hi mi inp a f l acc0 =
  let len = length inp in
  let len1 = len - len0 in
  let n = len / blocksize in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  len0_le_len_fraction blocksize len len0;
  split_len_lemma blocksize len len0;
  split_len_lemma0 blocksize n len0;

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  let acc = repeat_gen_blocks_multi blocksize mi hi n0 t0 a f acc0 in
  let blocks1 = Seq.slice t1 0 (n1 * blocksize) in
  Math.Lemmas.cancel_mul_mod n1 blocksize;
  let acc1 = repeat_gen_blocks_multi blocksize (mi + n0) hi n1 blocks1 a f acc in

  calc (==) {
    repeat_gen_blocks_multi blocksize (mi + n0) hi n1 blocks1 a f acc;
    (==) { repeat_gen_blocks_multi_split_slice #inp_t blocksize len0 mi hi inp a f acc0 }
    repeat_gen_blocks_multi blocksize mi hi n (Seq.slice inp 0 (n * blocksize)) a f acc0;
    };

  calc (==) {
    repeat_gen_blocks blocksize (mi + n0) hi t1 a f l acc;
    (==) { len0_div_bs blocksize len len0 }
    l (mi + n) (len1 % blocksize) (Seq.slice t1 (n1 * blocksize) len1) acc1;
    (==) { Math.Lemmas.lemma_mod_sub_distr len len0 blocksize }
    l (mi + n) (len % blocksize) (Seq.slice t1 (n1 * blocksize) len1) acc1;
    (==) { slice_slice_last #inp_t blocksize len0 inp }
    l (mi + n) (len % blocksize) (Seq.slice inp (n * blocksize) len) acc1;
    }
#pop-options

////////////////////////
// Start of repeat_blocks-related properties
////////////////////////

let repeat_blocks_extensionality #a #b #c blocksize inp f1 f2 l1 l2 acc0 =
  let len = length inp in
  let nb = len / blocksize in

  let f_rep1 = repeat_blocks_f blocksize inp f1 nb in
  let f_rep2 = repeat_blocks_f blocksize inp f2 nb in

  let acc1 = Loops.repeati nb f_rep1 acc0 in
  let acc2 = Loops.repeati nb f_rep2 acc0 in
  lemma_repeat_blocks blocksize inp f1 l1 acc0;
  lemma_repeat_blocks blocksize inp f2 l2 acc0;

  let aux (i:nat{i < nb}) (acc:b) : Lemma (f_rep1 i acc == f_rep2 i acc) =
    Math.Lemmas.lemma_mult_le_right blocksize (i + 1) nb;
    Seq.Properties.slice_slice inp 0 (nb * blocksize) (i * blocksize) (i * blocksize + blocksize) in

  Classical.forall_intro_2 aux;
  repeati_extensionality nb f_rep1 f_rep2 acc0


let lemma_repeat_blocks_via_multi #a #b #c blocksize inp f l acc0 =
  let len = length inp in
  let nb = len / blocksize in

  let blocks = Seq.slice inp 0 (nb * blocksize) in
  Math.Lemmas.cancel_mul_div nb blocksize;
  Math.Lemmas.cancel_mul_mod nb blocksize;

  let f_rep_b = repeat_blocks_f blocksize blocks f nb in
  let f_rep = repeat_blocks_f blocksize inp f nb in

  let aux (i:nat{i < nb}) (acc:b) : Lemma (f_rep_b i acc == f_rep i acc) =
    Math.Lemmas.lemma_mult_le_right blocksize (i + 1) nb;
    Seq.Properties.slice_slice inp 0 (nb * blocksize) (i * blocksize) (i * blocksize + blocksize) in

  lemma_repeat_blocks #a #b #c blocksize inp f l acc0;
  calc (==) {
    Loops.repeati nb f_rep acc0;
    (==) { Classical.forall_intro_2 aux; repeati_extensionality nb f_rep f_rep_b acc0 }
    Loops.repeati nb f_rep_b acc0;
    (==) { lemma_repeat_blocks_multi blocksize blocks f acc0 }
    repeat_blocks_multi blocksize blocks f acc0;
  }


let repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b hi blocksize inp f acc0 =
  let len = length inp in
  let n = len / blocksize in
  Math.Lemmas.div_exact_r len blocksize;

  let f_rep = repeat_blocks_f blocksize inp f n in
  let f_gen = repeat_gen_blocks_f blocksize 0 hi n inp (Loops.fixed_a b) (Loops.fixed_i f) in

  let aux (i:nat{i < n}) (acc:b) : Lemma (f_rep i acc == f_gen i acc) = () in

  calc (==) {
    repeat_blocks_multi #a #b blocksize inp f acc0;
    (==) { lemma_repeat_blocks_multi #a #b blocksize inp f acc0 }
    Loops.repeati n f_rep acc0;
    (==) { Loops.repeati_def n (repeat_blocks_f blocksize inp f n) acc0 }
    Loops.repeat_right 0 n (Loops.fixed_a b) f_rep acc0;
    (==) { Classical.forall_intro_2 aux;
           repeat_gen_right_extensionality n 0 (Loops.fixed_a b) (Loops.fixed_a b) f_rep f_gen acc0 }
    Loops.repeat_right 0 n (Loops.fixed_a b) f_gen acc0;
    }


let repeat_blocks_is_repeat_gen_blocks #a #b #c hi blocksize inp f l acc0 =
  let len = length inp in
  let nb = len / blocksize in
  //let rem = len % blocksize in

  Math.Lemmas.cancel_mul_div nb blocksize;
  Math.Lemmas.cancel_mul_mod nb blocksize;

  let blocks = Seq.slice inp 0 (nb * blocksize) in
  lemma_repeat_blocks_via_multi #a #b #c blocksize inp f l acc0;
  calc (==) {
    repeat_blocks_multi blocksize blocks f acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b hi blocksize blocks f acc0 }
    repeat_gen_blocks_multi blocksize 0 hi nb blocks (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    }


let repeat_blocks_multi_split #a #b blocksize len0 inp f acc0 =
  let len = length inp in
  let len1 = len - len0 in
  let n = len / blocksize in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  len0_le_len_fraction blocksize len len0;
  split_len_lemma0 blocksize n len0;

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in
  let acc1 = repeat_gen_blocks_multi blocksize 0 n n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0 in

  calc (==) {
    repeat_gen_blocks_multi blocksize 0 n n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_gen_blocks_multi_extensionality_zero blocksize 0 n0 n n0 t0
            (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i f) acc0}
    repeat_gen_blocks_multi blocksize 0 n0 n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b n0 blocksize t0 f acc0 }
    repeat_blocks_multi blocksize t0 f acc0;
  };

  calc (==) {
    repeat_blocks_multi blocksize inp f acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b n blocksize inp f acc0 }
    repeat_gen_blocks_multi blocksize 0 n n inp (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_gen_blocks_multi_split #a blocksize len0 0 n n inp (Loops.fixed_a b) (Loops.fixed_i f) acc0 }
    repeat_gen_blocks_multi blocksize n0 n n1 t1 (Loops.fixed_a b) (Loops.fixed_i f) acc1;
    (==) { repeat_gen_blocks_multi_extensionality_zero blocksize n0 n n1 n1 t1
            (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i f) acc1 }
    repeat_gen_blocks_multi blocksize 0 n1 n1 t1 (Loops.fixed_a b) (Loops.fixed_i f) acc1;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b n1 blocksize t1 f acc1 }
    repeat_blocks_multi blocksize t1 f acc1;
    }


let repeat_blocks_split #a #b #c blocksize len0 inp f l acc0 =
  let len = length inp in
  let len1 = len - len0 in
  let n = len / blocksize in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  len0_le_len_fraction blocksize len len0;
  split_len_lemma blocksize len len0;

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in
  let acc1 = repeat_gen_blocks_multi blocksize 0 n n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0 in

  calc (==) {
    repeat_gen_blocks_multi blocksize 0 n n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_gen_blocks_multi_extensionality_zero blocksize 0 n0 n n0 t0
            (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i f) acc0}
    repeat_gen_blocks_multi blocksize 0 n0 n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b n0 blocksize t0 f acc0 }
    repeat_blocks_multi blocksize t0 f acc0;
  };

  calc (==) {
    repeat_blocks blocksize inp f l acc0;
    (==) { repeat_blocks_is_repeat_gen_blocks n blocksize inp f l acc0 }
    repeat_gen_blocks blocksize 0 n inp (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0;
    (==) { repeat_gen_blocks_split #a #c blocksize len0 n 0 inp
             (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0 }
    repeat_gen_blocks blocksize n0 n t1 (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc1;
    (==) { repeat_gen_blocks_extensionality_zero blocksize n0 n n1 n1 t1
            (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l)
	    (Loops.fixed_i f) (Loops.fixed_i l) acc1 }
    repeat_gen_blocks blocksize 0 n1 t1 (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc1;
    (==) { repeat_blocks_is_repeat_gen_blocks #a #b #c n1 blocksize t1 f l acc1 }
    repeat_blocks blocksize t1 f l acc1;
    }

let repeat_blocks_multi_extensionality #a #b blocksize inp f g init =
  let len = length inp in
  let nb = len / blocksize in
  let f_rep = repeat_blocks_f blocksize inp f nb in
  let g_rep = repeat_blocks_f blocksize inp g nb in

  lemma_repeat_blocks_multi blocksize inp f init;
  lemma_repeat_blocks_multi blocksize inp g init;

  let aux (i:nat{i < nb}) (acc:b) : Lemma (f_rep i acc == g_rep i acc) =
    Math.Lemmas.lemma_mult_le_right blocksize (i + 1) nb;
    Seq.Properties.slice_slice inp 0 (nb * blocksize) (i * blocksize) (i * blocksize + blocksize) in

  Classical.forall_intro_2 aux;
  repeati_extensionality nb f_rep g_rep init


////////////////////////
// End of repeat_blocks-related properties
////////////////////////

let map_blocks_multi_extensionality #a blocksize max n inp f g =
  let a_map = map_blocks_a a blocksize max in
  let acc0 : a_map 0 = Seq.empty #a in

  calc (==) {
    map_blocks_multi blocksize max n inp f;
    (==) { lemma_map_blocks_multi blocksize max n inp f }
    Loops.repeat_gen n a_map (map_blocks_f #a blocksize max inp f) acc0;
    (==) { Loops.repeat_gen_def n a_map (map_blocks_f #a blocksize max inp f) acc0 }
    Loops.repeat_right 0 n a_map (map_blocks_f #a blocksize max inp f) acc0;
    (==) { repeat_right_extensionality n 0 a_map a_map
      (map_blocks_f #a blocksize max inp f) (map_blocks_f #a blocksize max inp g) acc0 }
    Loops.repeat_right 0 n a_map (map_blocks_f #a blocksize max inp g) acc0;
    (==) { Loops.repeat_gen_def n a_map (map_blocks_f #a blocksize max inp g) acc0 }
    Loops.repeat_gen n a_map (map_blocks_f #a blocksize max inp g) acc0;
    (==) { lemma_map_blocks_multi blocksize max n inp g }
    map_blocks_multi blocksize max n inp g;
    }


let map_blocks_extensionality #a blocksize inp f l_f g l_g =
  let len = length inp in
  let n = len / blocksize in
  let blocks = Seq.slice inp 0 (n * blocksize) in

  lemma_map_blocks blocksize inp f l_f;
  lemma_map_blocks blocksize inp g l_g;
  map_blocks_multi_extensionality #a blocksize n n blocks f g


let repeat_gen_blocks_map_l_length #a blocksize hi l i rem block_l acc = ()


let map_blocks_multi_acc #a blocksize mi hi n inp f acc0 =
  repeat_gen_blocks_multi #a blocksize mi hi n inp
    (map_blocks_a a blocksize hi)
    (repeat_gen_blocks_map_f blocksize hi f) acc0


let map_blocks_acc #a blocksize mi hi inp f l acc0 =
  repeat_gen_blocks #a blocksize mi hi inp
    (map_blocks_a a blocksize hi)
    (repeat_gen_blocks_map_f blocksize hi f)
    (repeat_gen_blocks_map_l blocksize hi l) acc0

let map_blocks_acc_length #a blocksize mi hi inp f l acc0 = ()

let map_blocks_multi_acc_is_repeat_gen_blocks_multi #a blocksize mi hi n inp f acc0 = ()

let map_blocks_acc_is_repeat_gen_blocks #a blocksize mi hi inp f l acc0 = ()

#push-options "--z3rlimit 150"
val map_blocks_multi_acc_is_map_blocks_multi_:
    #a:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi_f:nat
  -> hi_g:nat
  -> n:nat{mi + hi_g <= hi_f /\ n <= hi_g}
  -> inp:seq a{length inp == hi_g * blocksize}
  -> f:(i:nat{i < hi_f} -> lseq a blocksize -> lseq a blocksize)
  -> acc0:map_blocks_a a blocksize hi_f mi ->
  Lemma
   (let a_f = map_blocks_a a blocksize hi_f in
    let a_g = map_blocks_a a blocksize hi_g in
    let f_gen_map = repeat_gen_blocks_map_f blocksize hi_f f in
    let f_gen = repeat_gen_blocks_f blocksize mi hi_f hi_g inp a_f f_gen_map in

    let f_map = map_blocks_f #a blocksize hi_g inp (f_shift blocksize mi hi_f hi_g f) in

    Loops.repeat_right mi (mi + n) a_f f_gen acc0 ==
    Seq.append acc0 (Loops.repeat_right 0 n a_g f_map (Seq.empty #a)))

let rec map_blocks_multi_acc_is_map_blocks_multi_ #a blocksize mi hi_f hi_g n inp f acc0 =
  let a_f = map_blocks_a a blocksize hi_f in
  let a_g = map_blocks_a a blocksize hi_g in
  let f_gen_map = repeat_gen_blocks_map_f blocksize hi_f f in
  let f_gen = repeat_gen_blocks_f blocksize mi hi_f hi_g inp a_f f_gen_map in

  let f_sh = f_shift blocksize mi hi_f hi_g f in
  let f_map = map_blocks_f #a blocksize hi_g inp f_sh in
  let lp = Loops.repeat_right mi (mi + n) a_f f_gen acc0 in
  let rp = Loops.repeat_right 0 n a_g f_map (Seq.empty #a) in

  if n = 0 then begin
    Loops.eq_repeat_right mi (mi + n) a_f f_gen acc0;
    Loops.eq_repeat_right 0 n a_g f_map (Seq.empty #a);
    Seq.Base.append_empty_r acc0 end
  else begin
    let lp1 = Loops.repeat_right mi (mi + n - 1) a_f f_gen acc0 in
    let rp1 = Loops.repeat_right 0 (n - 1) a_g f_map (Seq.empty #a) in
    let block = Seq.slice inp ((n - 1) * blocksize) (n * blocksize) in
    Loops.unfold_repeat_right 0 n a_g f_map (Seq.empty #a) (n - 1);
    assert (rp == f_map (n - 1) rp1);
    assert (rp == Seq.append rp1 (f (mi + n - 1) block));

    calc (==) {
      Loops.repeat_right mi (mi + n) a_f f_gen acc0;
      (==) { Loops.unfold_repeat_right mi (mi + n) a_f f_gen acc0 (mi + n - 1) }
      Seq.append lp1 (f (mi + n - 1) block);
      (==) { map_blocks_multi_acc_is_map_blocks_multi_ #a blocksize mi hi_f hi_g (n - 1) inp f acc0 }
      Seq.append (Seq.append acc0 rp1) (f (mi + n - 1) block);
      (==) { Seq.Base.append_assoc acc0 rp1 (f (mi + n - 1) block) }
      Seq.append acc0 (Seq.append rp1 (f (mi + n - 1) block));
      } end
#pop-options

let map_blocks_multi_acc_is_map_blocks_multi #a blocksize mi hi n inp f acc0 =
  let f_map = repeat_gen_blocks_map_f blocksize hi f in
  let a_map = map_blocks_a a blocksize hi in
  let f_gen = repeat_gen_blocks_f blocksize mi hi n inp a_map f_map in

  let f_map_s = f_shift blocksize mi hi n f in
  let a_map_s = map_blocks_a a blocksize n in
  let f_gen_s = map_blocks_f #a blocksize n inp f_map_s in

  calc (==) {
    Seq.append acc0 (map_blocks_multi blocksize n n inp f_map_s);
    (==) { lemma_map_blocks_multi blocksize n n inp f_map_s }
    Seq.append acc0 (Loops.repeat_gen n a_map_s f_gen_s (Seq.empty #a));
    (==) { Loops.repeat_gen_def n a_map_s f_gen_s (Seq.empty #a) }
    Seq.append acc0 (Loops.repeat_right 0 n a_map_s f_gen_s (Seq.empty #a));
    (==) { map_blocks_multi_acc_is_map_blocks_multi_ #a blocksize mi hi n n inp f acc0 }
    Loops.repeat_right mi (mi + n) a_map f_gen acc0;
    (==) { }
    map_blocks_multi_acc #a blocksize mi hi n inp f acc0;
  }


let map_blocks_acc_is_map_blocks #a blocksize mi hi inp f l acc0 =
  let len = length inp in
  let n = len / blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  let blocks = Seq.slice inp 0 (n * blocksize) in

  let f_sh = f_shift blocksize mi hi n f in
  let l_sh = l_shift blocksize mi hi n l in
  lemma_map_blocks #a blocksize inp f_sh l_sh;
  map_blocks_multi_acc_is_map_blocks_multi #a blocksize mi hi n blocks f acc0


let map_blocks_multi_acc_is_map_blocks_multi0 #a blocksize hi n inp f =
  let f_sh = f_shift blocksize 0 hi n f in
  let a_map = map_blocks_a a blocksize n in
  let acc0 : a_map 0 = Seq.empty #a in

  calc (==) {
    map_blocks_multi_acc blocksize 0 hi n inp f Seq.empty;
    (==) { map_blocks_multi_acc_is_map_blocks_multi #a blocksize 0 hi n inp f Seq.empty }
    Seq.append Seq.empty (map_blocks_multi blocksize n n inp f_sh);
    (==) { Seq.Base.append_empty_l (map_blocks_multi blocksize n n inp f_sh) }
    map_blocks_multi blocksize n n inp f_sh;
    (==) { map_blocks_multi_extensionality blocksize n n inp f_sh f }
    map_blocks_multi blocksize n n inp f;
    }


let map_blocks_acc_is_map_blocks0 #a blocksize hi inp f l =
  let len = length inp in
  let n = len / blocksize in
  let f_sh = f_shift blocksize 0 hi n f in
  let l_sh = l_shift blocksize 0 hi n l in

  calc (==) {
    map_blocks_acc #a blocksize 0 hi inp f l Seq.empty;
    (==) { map_blocks_acc_is_map_blocks blocksize 0 hi inp f l Seq.empty }
    Seq.append Seq.empty (map_blocks #a blocksize inp f_sh l_sh);
    (==) { Seq.Base.append_empty_l (map_blocks #a blocksize inp f_sh l_sh) }
    map_blocks #a blocksize inp f_sh l_sh;
    (==) { map_blocks_extensionality #a blocksize inp f l f_sh l_sh }
    map_blocks #a blocksize inp f l;
    }


let map_blocks_is_empty #a blocksize hi inp f l =
  let len = length inp in
  let nb = len / blocksize in
  let rem = len % blocksize in
  let blocks = Seq.slice inp 0 (nb * blocksize) in

  assert (rem == 0);
  calc (==) {
    map_blocks blocksize inp f l;
    (==) { lemma_map_blocks blocksize inp f l }
    map_blocks_multi #a blocksize nb nb blocks f;
    (==) { lemma_map_blocks_multi blocksize nb nb blocks f }
    Loops.repeat_gen nb (map_blocks_a a blocksize nb) (map_blocks_f #a blocksize nb inp f) Seq.empty;
    (==) { Loops.eq_repeat_gen0 nb (map_blocks_a a blocksize nb) (map_blocks_f #a blocksize nb inp f) Seq.empty }
    Seq.empty;
    }
