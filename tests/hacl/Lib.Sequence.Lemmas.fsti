module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 \
  --using_facts_from '-* +Prims +FStar.Math.Lemmas +FStar.Seq +Lib.IntTypes +Lib.Sequence +Lib.Sequence.Lemmas'"


let get_block_s
  (#a:Type)
  (#len:nat)
  (blocksize:size_pos)
  (inp:seq a{length inp == len})
  (i:nat{i < len / blocksize * blocksize}) :
  lseq a blocksize
=
  div_mul_lt blocksize i (len / blocksize);
  let j = i / blocksize in
  let b: lseq a blocksize = Seq.slice inp (j * blocksize) ((j + 1) * blocksize) in
  b


let get_last_s
  (#a:Type)
  (#len:nat)
  (blocksize:size_pos)
  (inp:seq a{length inp == len}) :
  lseq a (len % blocksize)
=
  let rem = len % blocksize in
  let b: lseq a rem = Seq.slice inp (len - rem) len in
  b


val repeati_extensionality:
    #a:Type0
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{i < n} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g i acc))
  (ensures  Loops.repeati n f acc0 == Loops.repeati n g acc0)


val repeat_right_extensionality:
     n:nat
  -> lo:nat
  -> a_f:(i:nat{lo <= i /\ i <= lo + n} -> Type)
  -> a_g:(i:nat{lo <= i /\ i <= lo + n} -> Type)
  -> f:(i:nat{lo <= i /\ i < lo + n} -> a_f i -> a_f (i + 1))
  -> g:(i:nat{lo <= i /\ i < lo + n} -> a_g i -> a_g (i + 1))
  -> acc0:a_f lo ->
  Lemma
  (requires
    (forall (i:nat{lo <= i /\ i <= lo + n}). a_f i == a_g i) /\
    (forall (i:nat{lo <= i /\ i < lo + n}) (acc:a_f i). f i acc == g i acc))
  (ensures
    Loops.repeat_right lo (lo + n) a_f f acc0 ==
    Loops.repeat_right lo (lo + n) a_g g acc0)


// Loops.repeat_gen n a_f f acc0 ==
// Loops.repeat_right lo_g (lo_g + n) a_g g acc0)
val repeat_gen_right_extensionality:
    n:nat
  -> lo_g:nat
  -> a_f:(i:nat{i <= n} -> Type)
  -> a_g:(i:nat{lo_g <= i /\ i <= lo_g + n} -> Type)
  -> f:(i:nat{i < n} -> a_f i -> a_f (i + 1))
  -> g:(i:nat{lo_g <= i /\ i < lo_g + n} -> a_g i -> a_g (i + 1))
  -> acc0:a_f 0 ->
  Lemma
  (requires
    (forall (i:nat{i <= n}). a_f i == a_g (lo_g + i)) /\
    (forall (i:nat{i < n}) (acc:a_f i). f i acc == g (lo_g + i) acc))
  (ensures
    Loops.repeat_right 0 n a_f f acc0 ==
    Loops.repeat_right lo_g (lo_g + n) a_g g acc0)


// Loops.repeati n a f acc0 ==
// Loops.repeat_right lo_g (lo_g + n) (Loops.fixed_a a) g acc0
val repeati_right_extensionality:
    #a:Type
  -> n:nat
  -> lo_g:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{lo_g <= i /\ i < lo_g + n} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g (lo_g + i) acc))
  (ensures
    Loops.repeat_right 0 n (Loops.fixed_a a) f acc0 ==
    Loops.repeat_right lo_g (lo_g + n) (Loops.fixed_a a) g acc0)

/// A specialized version of the lemma above, for only shifting one computation,
/// but specified using repeati instead
val repeati_right_shift:
    #a:Type
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{i < 1 + n} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g (i + 1) acc))
  (ensures Loops.repeati n f (g 0 acc0) == Loops.repeati (n + 1) g acc0)

///
///   `repeat_gen_blocks` is defined here to prove all the properties
///   needed for `map_blocks` and `repeat_blocks` once
///

let repeat_gen_blocks_f
  (#inp_t:Type0)
  (blocksize:size_pos)
  (mi:nat)
  (hi:nat)
  (n:nat{mi + n <= hi})
  (inp:seq inp_t{length inp == n * blocksize})
  (a:(i:nat{i <= hi} -> Type))
  (f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1)))
  (i:nat{mi <= i /\ i < mi + n})
  (acc:a i) : a (i + 1)
=
  let i_b = i - mi in
  Math.Lemmas.lemma_mult_le_right blocksize (i_b + 1) n;
  let block = Seq.slice inp (i_b * blocksize) (i_b * blocksize + blocksize) in
  f i block acc


//lo = 0
val repeat_gen_blocks_multi:
    #inp_t:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq inp_t{length inp == n * blocksize}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> acc0:a mi ->
  a (mi + n)


val lemma_repeat_gen_blocks_multi:
    #inp_t:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq inp_t{length inp == n * blocksize}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> acc0:a mi ->
  Lemma
   (repeat_gen_blocks_multi #inp_t blocksize mi hi n inp a f acc0 ==
    Loops.repeat_right mi (mi + n) a (repeat_gen_blocks_f blocksize mi hi n inp a f) acc0)


val repeat_gen_blocks:
    #inp_t:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> inp:seq inp_t{mi + length inp / blocksize <= hi}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> l:(i:nat{i <= hi} -> len:nat{len < blocksize} -> lseq inp_t len -> a i -> c)
  -> acci:a mi ->
  c


val lemma_repeat_gen_blocks:
    #inp_t:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> inp:seq inp_t{mi + length inp / blocksize <= hi}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> l:(i:nat{i <= hi} -> len:nat{len < blocksize} -> lseq inp_t len -> a i -> c)
  -> acc0:a mi ->
  Lemma
   (let len = length inp in
    let nb = len / blocksize in
    let rem = len % blocksize in
    let blocks = Seq.slice inp 0 (nb * blocksize) in
    let last = Seq.slice inp (nb * blocksize) len in
    Math.Lemmas.cancel_mul_div nb blocksize;
    Math.Lemmas.cancel_mul_mod nb blocksize;
    let acc = repeat_gen_blocks_multi #inp_t blocksize mi hi nb blocks a f acc0 in
    repeat_gen_blocks blocksize mi hi inp a f l acc0 == l (mi + nb) rem last acc)


val repeat_gen_blocks_multi_extensionality_zero:
    #inp_t:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi_f:nat
  -> hi_g:nat
  -> n:nat{mi + n <= hi_f /\ n <= hi_g}
  -> inp:seq inp_t{length inp == n * blocksize}
  -> a_f:(i:nat{i <= hi_f} -> Type)
  -> a_g:(i:nat{i <= hi_g} -> Type)
  -> f:(i:nat{i < hi_f} -> lseq inp_t blocksize -> a_f i -> a_f (i + 1))
  -> g:(i:nat{i < hi_g} -> lseq inp_t blocksize -> a_g i -> a_g (i + 1))
  -> acc0:a_f mi ->
  Lemma
  (requires
    (forall (i:nat{i <= n}). a_f (mi + i) == a_g i) /\
    (forall (i:nat{i < n}) (block:lseq inp_t blocksize) (acc:a_f (mi + i)).
      f (mi + i) block acc == g i block acc))
  (ensures
    repeat_gen_blocks_multi blocksize mi hi_f n inp a_f f acc0 ==
    repeat_gen_blocks_multi blocksize 0 hi_g n inp a_g g acc0)


val repeat_gen_blocks_extensionality_zero:
    #inp_t:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi_f:nat
  -> hi_g:nat
  -> n:nat{mi + n <= hi_f /\ n <= hi_g}
  -> inp:seq inp_t{n == length inp / blocksize}
  -> a_f:(i:nat{i <= hi_f} -> Type)
  -> a_g:(i:nat{i <= hi_g} -> Type)
  -> f:(i:nat{i < hi_f} -> lseq inp_t blocksize -> a_f i -> a_f (i + 1))
  -> l_f:(i:nat{i <= hi_f} -> len:nat{len < blocksize} -> lseq inp_t len -> a_f i -> c)
  -> g:(i:nat{i < hi_g} -> lseq inp_t blocksize -> a_g i -> a_g (i + 1))
  -> l_g:(i:nat{i <= hi_g} -> len:nat{len < blocksize} -> lseq inp_t len -> a_g i -> c)
  -> acc0:a_f mi ->
  Lemma
  (requires
    (forall (i:nat{i <= n}). a_f (mi + i) == a_g i) /\
    (forall (i:nat{i < n}) (block:lseq inp_t blocksize) (acc:a_f (mi + i)).
      f (mi + i) block acc == g i block acc) /\
    (forall (i:nat{i <= n}) (len:nat{len < blocksize}) (block:lseq inp_t len) (acc:a_f (mi + i)).
      l_f (mi + i) len block acc == l_g i len block acc))
  (ensures
    repeat_gen_blocks blocksize mi hi_f inp a_f f l_f acc0 ==
    repeat_gen_blocks blocksize 0 hi_g inp a_g g l_g acc0)


val len0_div_bs: blocksize:pos -> len:nat -> len0:nat ->
  Lemma
  (requires len0 <= len /\ len0 % blocksize == 0)
  (ensures  len0 / blocksize + (len - len0) / blocksize == len / blocksize)


val split_len_lemma0: blocksize:pos -> n:nat -> len0:nat ->
  Lemma
  (requires len0 <= n * blocksize /\ len0 % blocksize = 0)
  (ensures
   (let len = n * blocksize in
    let len1 = len - len0 in
    let n0 = len0 / blocksize in
    let n1 = len1 / blocksize in
    len % blocksize = 0 /\ len1 % blocksize = 0 /\ n0 + n1 = n /\
    n0 * blocksize = len0 /\ n1 * blocksize = len1))


val split_len_lemma: blocksize:pos -> len:nat -> len0:nat ->
  Lemma
  (requires len0 <= len /\ len0 % blocksize = 0)
  (ensures
   (let len1 = len - len0 in
    let n0 = len0 / blocksize in
    let n1 = len1 / blocksize in
    let n = len / blocksize in
    len % blocksize = len1 % blocksize /\
    n0 * blocksize = len0 /\ n0 + n1 = n))


val repeat_gen_blocks_multi_split:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq inp_t{len0 <= length inp /\ length inp == n * blocksize}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> acc0:a mi ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    let n0 = len0 / blocksize in
    let n1 = len1 / blocksize in
    split_len_lemma0 blocksize n len0;

    let t0 = Seq.slice inp 0 len0 in
    let t1 = Seq.slice inp len0 len in

    let acc : a (mi + n0) = repeat_gen_blocks_multi blocksize mi hi n0 t0 a f acc0 in
    repeat_gen_blocks_multi blocksize mi hi n inp a f acc0 ==
    repeat_gen_blocks_multi blocksize (mi + n0) hi n1 t1 a f acc)


val repeat_gen_blocks_split:
    #inp_t:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> hi:nat
  -> mi:nat{mi <= hi}
  -> inp:seq inp_t{len0 <= length inp /\ mi + length inp / blocksize <= hi}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> l:(i:nat{i <= hi} -> len:nat{len < blocksize} -> lseq inp_t len -> a i -> c)
  -> acc0:a mi ->
  Lemma
   (let len = length inp in
    let n = len / blocksize in
    let n0 = len0 / blocksize in
    split_len_lemma blocksize len len0;

    let t0 = Seq.slice inp 0 len0 in
    let t1 = Seq.slice inp len0 len in

    let acc : a (mi + n0) = repeat_gen_blocks_multi blocksize mi hi n0 t0 a f acc0 in
    repeat_gen_blocks blocksize mi hi inp a f l acc0 ==
    repeat_gen_blocks blocksize (mi + n0) hi t1 a f l acc)

///
///  Properties related to the repeat_blocks combinator
///

val repeat_blocks_extensionality:
    #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f1:(lseq a blocksize -> b -> b)
  -> f2:(lseq a blocksize -> b -> b)
  -> l1:(len:nat{len < blocksize} -> s:lseq a len -> b -> c)
  -> l2:(len:nat{len < blocksize} -> s:lseq a len -> b -> c)
  -> acc0:b ->
  Lemma
  (requires
    (forall (block:lseq a blocksize) (acc:b). f1 block acc == f2 block acc) /\
    (forall (rem:nat{rem < blocksize}) (last:lseq a rem) (acc:b). l1 rem last acc == l2 rem last acc))
  (ensures
    repeat_blocks blocksize inp f1 l1 acc0 == repeat_blocks blocksize inp f2 l2 acc0)


val lemma_repeat_blocks_via_multi:
    #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:nat{len < blocksize} -> s:lseq a len -> b -> c)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    let nb = len / blocksize in
    let rem = len % blocksize in
    let blocks = Seq.slice inp 0 (nb * blocksize) in
    let last = Seq.slice inp (nb * blocksize) len in
    Math.Lemmas.cancel_mul_mod nb blocksize;
    let acc = repeat_blocks_multi blocksize blocks f acc0 in
    repeat_blocks #a #b blocksize inp f l acc0 == l rem last acc)


val repeat_blocks_multi_is_repeat_gen_blocks_multi:
    #a:Type0
  -> #b:Type0
  -> hi:nat
  -> blocksize:size_pos
  -> inp:seq a{length inp % blocksize = 0 /\ length inp / blocksize <= hi}
  -> f:(lseq a blocksize -> b -> b)
  -> acc0:b ->
  Lemma
   (let n = length inp / blocksize in
    Math.Lemmas.div_exact_r (length inp) blocksize;
    repeat_blocks_multi #a #b blocksize inp f acc0 ==
    repeat_gen_blocks_multi #a blocksize 0 hi n inp (Loops.fixed_a b) (Loops.fixed_i f) acc0)


val repeat_blocks_is_repeat_gen_blocks:
    #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> hi:nat
  -> blocksize:size_pos
  -> inp:seq a{length inp / blocksize <= hi}
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:nat{len < blocksize} -> s:lseq a len -> b -> c)
  -> acc0:b ->
  Lemma
   (repeat_blocks #a #b #c blocksize inp f l acc0 ==
    repeat_gen_blocks #a #c blocksize 0 hi inp
      (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0)


val repeat_blocks_multi_split:
     #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    Math.Lemmas.lemma_div_exact len blocksize;
    split_len_lemma0 blocksize (len / blocksize) len0;
    Math.Lemmas.swap_mul blocksize (len / blocksize);

    repeat_blocks_multi blocksize inp f acc0 ==
    repeat_blocks_multi blocksize (Seq.slice inp len0 len) f
      (repeat_blocks_multi blocksize (Seq.slice inp 0 len0) f acc0))


val repeat_blocks_split:
     #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:nat{len < blocksize} -> s:lseq a len -> b -> c)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    split_len_lemma blocksize len len0;

    repeat_blocks blocksize inp f l acc0 ==
    repeat_blocks blocksize (Seq.slice inp len0 len) f l
      (repeat_blocks_multi blocksize (Seq.slice inp 0 len0) f acc0))

///
val repeat_blocks_multi_extensionality:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> inp:seq a{length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> g:(lseq a blocksize -> b -> b)
  -> init:b ->
  Lemma
  (requires
    (forall (block:lseq a blocksize) (acc:b). f block acc == g block acc))
  (ensures
    repeat_blocks_multi blocksize inp f init ==
    repeat_blocks_multi blocksize inp g init)

///  Properties related to the map_blocks combinator
///

val map_blocks_multi_extensionality:
    #a:Type0
  -> blocksize:size_pos
  -> max:nat
  -> n:nat{n <= max}
  -> inp:seq a{length inp == max * blocksize}
  -> f:(i:nat{i < max} -> lseq a blocksize -> lseq a blocksize)
  -> g:(i:nat{i < max} -> lseq a blocksize -> lseq a blocksize) ->
  Lemma
  (requires
    (forall (i:nat{i < max}) (b_v:lseq a blocksize). f i b_v == g i b_v))
  (ensures
    map_blocks_multi blocksize max n inp f ==
    map_blocks_multi blocksize max n inp g)


val map_blocks_extensionality:
    #a:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(block (length inp) blocksize -> lseq a blocksize -> lseq a blocksize)
  -> l_f:(last (length inp) blocksize -> rem:size_nat{rem < blocksize} -> s:lseq a rem -> lseq a rem)
  -> g:(block (length inp) blocksize -> lseq a blocksize -> lseq a blocksize)
  -> l_g:(last (length inp) blocksize -> rem:size_nat{rem < blocksize} -> s:lseq a rem -> lseq a rem) ->
  Lemma
  (requires
    (let n = length inp / blocksize in
    (forall (i:nat{i < n}) (b_v:lseq a blocksize). f i b_v == g i b_v) /\
    (forall (rem:nat{rem < blocksize}) (b_v:lseq a rem). l_f n rem b_v == l_g n rem b_v)))
  (ensures
    map_blocks blocksize inp f l_f == map_blocks blocksize inp g l_g)

///
///   New definition of `map_blocks` that takes extra parameter `acc`.
///   When `acc` = Seq.empty, map_blocks == map_blocks_acc
///

let repeat_gen_blocks_map_f
  (#a:Type0)
  (blocksize:size_pos)
  (hi:nat)
  (f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize))
  (i:nat{i < hi})
  (block:lseq a blocksize)
  (acc:map_blocks_a a blocksize hi i) : map_blocks_a a blocksize hi (i + 1)
 =
   Seq.append acc (f i block)


let repeat_gen_blocks_map_l
  (#a:Type0)
  (blocksize:size_pos)
  (hi:nat)
  (l:(i:nat{i <= hi} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem))
  (i:nat{i <= hi})
  (rem:nat{rem < blocksize})
  (block_l:lseq a rem)
  (acc:map_blocks_a a blocksize hi i) : seq a
 =
   if rem > 0 then Seq.append acc (l i rem block_l) else acc


val repeat_gen_blocks_map_l_length:
    #a:Type0
  -> blocksize:size_pos
  -> hi:nat
  -> l:(i:nat{i <= hi} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> i:nat{i <= hi}
  -> rem:nat{rem < blocksize}
  -> block_l:lseq a rem
  -> acc:map_blocks_a a blocksize hi i ->
  Lemma (length (repeat_gen_blocks_map_l blocksize hi l i rem block_l acc) == i * blocksize + rem)


val map_blocks_multi_acc:
    #a:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq a{length inp == n * blocksize}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> acc0:map_blocks_a a blocksize hi mi ->
  out:seq a {length out == length acc0 + length inp}


val map_blocks_acc:
    #a:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> inp:seq a{mi + length inp / blocksize <= hi}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= hi} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> acc0:map_blocks_a a blocksize hi mi ->
  seq a


val map_blocks_acc_length:
    #a:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> inp:seq a{mi + length inp / blocksize <= hi}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= hi} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> acc0:map_blocks_a a blocksize hi mi ->
  Lemma (length (map_blocks_acc blocksize mi hi inp f l acc0) == length acc0 + length inp)
  [SMTPat (map_blocks_acc blocksize mi hi inp f l acc0)]


val map_blocks_multi_acc_is_repeat_gen_blocks_multi:
    #a:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq a{length inp == n * blocksize}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> acc0:map_blocks_a a blocksize hi mi ->
  Lemma
   (map_blocks_multi_acc #a blocksize mi hi n inp f acc0 ==
    repeat_gen_blocks_multi #a blocksize mi hi n inp
      (map_blocks_a a blocksize hi)
      (repeat_gen_blocks_map_f blocksize hi f) acc0)


val map_blocks_acc_is_repeat_gen_blocks:
    #a:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> inp:seq a{mi + length inp / blocksize <= hi}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= hi} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> acc0:map_blocks_a a blocksize hi mi ->
  Lemma
   (map_blocks_acc #a blocksize mi hi inp f l acc0 ==
    repeat_gen_blocks #a blocksize mi hi inp
      (map_blocks_a a blocksize hi)
      (repeat_gen_blocks_map_f blocksize hi f)
      (repeat_gen_blocks_map_l blocksize hi l) acc0)


let f_shift (#a:Type0) (blocksize:size_pos) (mi:nat) (hi:nat) (n:nat{mi + n <= hi})
  (f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)) (i:nat{i < n}) = f (mi + i)


let l_shift (#a:Type0) (blocksize:size_pos) (mi:nat) (hi:nat) (n:nat{mi + n <= hi})
  (l:(i:nat{i <= hi} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)) (i:nat{i <= n}) = l (mi + i)


val map_blocks_multi_acc_is_map_blocks_multi:
    #a:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq a{length inp == n * blocksize}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> acc0:map_blocks_a a blocksize hi mi ->
  Lemma
   (map_blocks_multi_acc blocksize mi hi n inp f acc0 `Seq.equal`
    Seq.append acc0 (map_blocks_multi blocksize n n inp (f_shift blocksize mi hi n f)))


val map_blocks_acc_is_map_blocks:
    #a:Type0
  -> blocksize:size_pos
  -> mi:nat
  -> hi:nat
  -> inp:seq a{mi + length inp / blocksize <= hi}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= hi} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> acc0:map_blocks_a a blocksize hi mi ->
  Lemma
   (let n = length inp / blocksize in
    map_blocks_acc #a blocksize mi hi inp f l acc0 `Seq.equal`
    Seq.append acc0 (map_blocks #a blocksize inp (f_shift blocksize mi hi n f) (l_shift blocksize mi hi n l)))


val map_blocks_multi_acc_is_map_blocks_multi0:
    #a:Type0
  -> blocksize:size_pos
  -> hi:nat
  -> n:nat{n <= hi}
  -> inp:seq a{length inp == n * blocksize}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize) ->
  Lemma (map_blocks_multi_acc blocksize 0 hi n inp f Seq.empty `Seq.equal` map_blocks_multi blocksize n n inp f)


val map_blocks_acc_is_map_blocks0:
    #a:Type0
  -> blocksize:size_pos
  -> hi:nat
  -> inp:seq a{length inp / blocksize <= hi}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= hi} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem) ->
  Lemma (map_blocks_acc #a blocksize 0 hi inp f l Seq.empty `Seq.equal` map_blocks #a blocksize inp f l)


val map_blocks_is_empty:
    #a:Type0
  -> blocksize:size_pos
  -> hi:nat
  -> inp:seq a{length inp == 0}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i <= hi} -> rem:nat{rem < blocksize} -> lseq a rem -> lseq a rem) ->
  Lemma (map_blocks #a blocksize inp f l == Seq.empty)


(*
//Now it's possible to prove the following lemma:

val map_blocks_multi_split:
    #a:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> hi:nat
  -> mi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq a{len0 <= length inp /\ length inp == n * blocksize}
  -> f:(i:nat{i < hi} -> lseq a blocksize -> lseq a blocksize)
  -> acc:map_blocks_a a blocksize hi mi ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    let n0 = len0 / blocksize in
    let n1 = len1 / blocksize in
    split_len_lemma0 blocksize n len0;

    let t0 = Seq.slice inp 0 len0 in
    let t1 = Seq.slice inp len0 len in

    map_blocks_multi_acc blocksize mi hi n inp f acc  ==
    map_blocks_multi_acc blocksize (mi + n0) hi n1 t1 f
      (map_blocks_multi_acc blocksize mi hi n0 t0 f acc))
*)
