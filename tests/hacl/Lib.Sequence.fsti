module Lib.Sequence

open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0 --using_facts_from '-* +Prims +FStar.Math.Lemmas +FStar.Seq +Lib.IntTypes +Lib.Sequence'"
#set-options "--z3refresh"
/// Variable length Sequences, derived from FStar.Seq

(* This is the type of unbounded sequences.
   Use this only when dealing with, say, user input whose length is unbounded.
   As far as possible use the API for bounded sequences defined later in this file.*)

(** Definition of a Sequence *)
let seq (a:Type0) = Seq.seq a

(** Length of a Sequence *)
let length (#a:Type0) (s:seq a) : nat = Seq.length s

/// Fixed length Sequences

(* This is the type of bounded sequences.
   Use this as much as possible.
   It adds additional length checks that you'd have to prove in the implementation otherwise *)

(** Definition of a fixed-length Sequence *)
let lseq (a:Type0) (len:size_nat) = s:seq a{Seq.length s == len}
let to_seq (#a:Type0) (#len:size_nat) (l:lseq a len) : seq a = l
let to_lseq (#a:Type0) (s:seq a{length s <= max_size_t}) : l:lseq a (length s){l == s} = s

(* If you want to prove your code with an abstract lseq use the following: *)
// val lseq: a:Type0 -> len:size_nat -> Type0
// val to_seq: #a:Type0 -> #len:size_nat -> lseq a len -> s:seq a{length s == len}
// val to_lseq: #a:Type0 -> s:seq a{length s <= max_size_t} -> lseq a (length s)

val index:
    #a:Type
  -> #len:size_nat
  -> s:lseq a len
  -> i:size_nat{i < len} ->
  Tot (r:a{r == Seq.index (to_seq s) i})

(** Creation of a fixed-length Sequence from an initial value *)
val create:
    #a:Type
  -> len:size_nat
  -> init:a ->
  Tot (s:lseq a len{to_seq s == Seq.create len init /\ (forall (i:nat).
    {:pattern (index s i)} i < len ==> index s i == init)})


(** Concatenate sequences: use with care, may make implementation hard to verify *)
val concat:
    #a:Type
  -> #len0:size_nat
  -> #len1:size_nat{len0 + len1 <= max_size_t}
  -> s0:lseq a len0
  -> s1:lseq a len1 ->
  Tot (s2:lseq a (len0 + len1){to_seq s2 == Seq.append (to_seq s0) (to_seq s1)})

let ( @| ) #a #len0 #len1 s0 s1 = concat #a #len0 #len1 s0 s1


(** Conversion of a Sequence to a list *)
val to_list:
    #a:Type
  -> s:seq a ->
  Tot (l:list a{List.Tot.length l = length s /\ l == Seq.seq_to_list s})

(** Creation of a fixed-length Sequence from a list of values *)
val of_list:
    #a:Type
  -> l:list a{List.Tot.length l <= max_size_t} ->
  Tot (s:lseq a (List.Tot.length l){to_seq s == Seq.seq_of_list l})

val of_list_index:
    #a:Type
  -> l:list a{List.Tot.length l <= max_size_t}
  -> i:nat{i < List.Tot.length l} ->
  Lemma (index (of_list l) i == List.Tot.index l i)
    [SMTPat (index (of_list l) i)]

val equal (#a:Type) (#len:size_nat) (s1:lseq a len) (s2:lseq a len) : Type0

val eq_intro: #a:Type -> #len:size_nat -> s1:lseq a len -> s2:lseq a len ->
  Lemma
  (requires forall i. {:pattern index s1 i; index s2 i} index s1 i == index s2 i)
  (ensures equal s1 s2)
  [SMTPat (equal s1 s2)]

val eq_elim: #a:Type -> #len:size_nat -> s1:lseq a len -> s2:lseq a len ->
  Lemma
  (requires equal s1 s2)
  (ensures  s1 == s2)
  [SMTPat (equal s1 s2)]

(* Alias for creation from a list *)
unfold let createL #a l = of_list #a l

(** Updating an element of a fixed-length Sequence *)
val upd:
    #a:Type
  -> #len:size_nat
  -> s:lseq a len
  -> n:size_nat{n < len}
  -> x:a ->
  Tot (o:lseq a len{to_seq o == Seq.upd (to_seq s) n x /\ index o n == x /\ (forall (i:size_nat).
    {:pattern (index s i)} (i < len /\ i <> n) ==> index o i == index s i)})

(** Membership of an element to a fixed-length Sequence *)
val member: #a:eqtype -> #len: size_nat -> a -> lseq a len -> Tot bool

(** Operator for accessing an element of a fixed-length Sequence *)
unfold
let op_String_Access #a #len = index #a #len

(** Operator for updating an element of a fixed-length Sequence *)
unfold
let op_String_Assignment #a #len = upd #a #len

(** Selecting a subset of a fixed-length Sequence *)
val sub:
    #a:Type
  -> #len:size_nat
  -> s1:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len} ->
  Tot (s2:lseq a n{to_seq s2 == Seq.slice (to_seq s1) start (start + n) /\
             (forall (k:nat{k < n}). {:pattern (index s2 k)} index s2 k == index s1 (start + k))})

(** Selecting a subset of a fixed-length Sequence *)
let slice
    (#a:Type)
    (#len:size_nat)
    (s1:lseq a len)
    (start:size_nat)
    (fin:size_nat{start <= fin /\ fin <= len})
  =
  sub #a s1 start (fin - start)

(** Updating a sub-Sequence from another fixed-length Sequence *)
val update_sub:
    #a:Type
  -> #len:size_nat
  -> i:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len}
  -> x:lseq a n ->
  Tot (o:lseq a len{sub o start n == x /\
    (forall (k:nat{(0 <= k /\ k < start) \/ (start + n <= k /\ k < len)}).
      {:pattern (index o k)} index o k == index i k)})

(** Lemma regarding updating a sub-Sequence with another Sequence *)
val lemma_update_sub:
    #a:Type
  -> #len:size_nat
  -> dst:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len}
  -> src:lseq a n
  -> res:lseq a len ->
  Lemma
    (requires
      sub res 0 start == sub dst 0 start /\
      sub res start n == src /\
      sub res (start + n) (len - start - n) ==
      sub dst (start + n) (len - start - n))
    (ensures
      res == update_sub dst start n src)

val lemma_concat2:
    #a:Type0
  -> len0:size_nat
  -> s0:lseq a len0
  -> len1:size_nat{len0 + len1 <= max_size_t}
  -> s1:lseq a len1
  -> s:lseq a (len0 + len1) ->
  Lemma
    (requires
      sub s 0 len0 == s0 /\
      sub s len0 len1 == s1)
    (ensures s == concat s0 s1)

val lemma_concat3:
    #a:Type0
  -> len0:size_nat
  -> s0:lseq a len0
  -> len1:size_nat{len0 + len1 <= max_size_t}
  -> s1:lseq a len1
  -> len2:size_nat{len0 + len1 + len2 <= max_size_t}
  -> s2:lseq a len2
  -> s:lseq a (len0 + len1 + len2) ->
  Lemma
    (requires
      sub s 0 len0 == s0 /\
      sub s len0 len1 == s1 /\
      sub s (len0 + len1) len2 == s2)
    (ensures s == concat (concat s0 s1) s2)

(** Updating a sub-Sequence from another fixed-length Sequence *)
let update_slice
    (#a:Type)
    (#len:size_nat)
    (i:lseq a len)
    (start:size_nat)
    (fin:size_nat{start <= fin /\ fin <= len})
    (upd:lseq a (fin - start))
  =
  update_sub #a i start (fin - start) upd

(** Creation of a fixed-length Sequence from an initialization function *)
val createi: #a:Type
  -> len:size_nat
  -> init:(i:nat{i < len} -> a) ->
  Tot (s:lseq a len{(forall (i:nat).
    {:pattern (index s i)} i < len ==> index s i == init i)})

(** Mapi function for fixed-length Sequences *)
val mapi:#a:Type -> #b:Type -> #len:size_nat
  -> f:(i:nat{i < len} -> a -> Tot b)
  -> s1:lseq a len ->
  Tot (s2:lseq b len{(forall (i:nat).
    {:pattern (index s2 i)} i < len ==> index s2 i == f i s1.[i])})

(** Map function for fixed-length Sequences *)
val map:#a:Type -> #b:Type -> #len:size_nat
  -> f:(a -> Tot b)
  -> s1:lseq a len ->
  Tot (s2:lseq b len{(forall (i:nat).
    {:pattern (index s2 i)} i < len ==> index s2 i == f s1.[i])})

(** Map2i function for fixed-length Sequences *)
val map2i:#a:Type -> #b:Type -> #c:Type -> #len:size_nat
  -> f:(i:nat{i < len} -> a -> b -> Tot c)
  -> s1:lseq a len
  -> s2:lseq b len ->
  Tot (s3:lseq c len{(forall (i:nat).
    {:pattern (index s3 i)} i < len ==> index s3 i == f i s1.[i] s2.[i])})

(** Map2 function for fixed-length Sequences *)
val map2:#a:Type -> #b:Type -> #c:Type -> #len:size_nat
  -> f:(a -> b -> Tot c)
  -> s1:lseq a len
  -> s2:lseq b len ->
  Tot (s3:lseq c len{(forall (i:nat).
    {:pattern (index s3 i)} i < len ==> index s3 i == f s1.[i] s2.[i])})

(** Forall function for fixed-length Sequences *)
val for_all:#a:Type -> #len:size_nat -> (a -> Tot bool) -> lseq a len -> bool

(** Forall2 function for fixed-length Sequences *)
val for_all2:#a:Type -> #b:Type -> #len:size_nat
  -> (a -> b -> Tot bool)
  -> s1:lseq a len
  -> s2:lseq b len ->
  Tot bool

val repeati_blocks:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(i:nat{i < length inp / blocksize} -> lseq a blocksize -> b -> b)
  -> l:(i:nat{i == length inp / blocksize} -> len:size_nat{len == length inp % blocksize} -> s:lseq a len -> b -> b)
  -> init:b ->
  Tot b

let repeat_blocks_f
  (#a:Type0)
  (#b:Type0)
  (bs:size_nat{bs > 0})
  (inp:seq a)
  (f:(lseq a bs -> b -> b))
  (nb:nat{nb == length inp / bs})
  (i:nat{i < nb})
  (acc:b) : b
 =
  assert ((i+1) * bs <= nb * bs);
  let block = Seq.slice inp (i * bs) (i * bs + bs) in
  f block acc

val repeat_blocks:
    #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:nat{len < blocksize} -> s:lseq a len -> b -> c)
  -> init:b ->
  Tot c

val lemma_repeat_blocks:
    #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> bs:size_pos
  -> inp:seq a
  -> f:(lseq a bs -> b -> b)
  -> l:(len:nat{len < bs} -> s:lseq a len -> b -> c)
  -> init:b ->
  Lemma (
    let len = length inp in
    let nb = len / bs in
    let rem = len % bs in
    let acc = Lib.LoopCombinators.repeati nb (repeat_blocks_f bs inp f nb) init in
    let last = Seq.slice inp (nb * bs) len in
    let acc = l rem last acc in
    repeat_blocks #a #b bs inp f l init == acc)

val repeat_blocks_multi:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> inp:seq a{length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> init:b ->
  Tot b

val lemma_repeat_blocks_multi:
    #a:Type0
  -> #b:Type0
  -> bs:size_pos
  -> inp:seq a{length inp % bs = 0}
  -> f:(lseq a bs -> b -> b)
  -> init:b ->
  Lemma (
    let len = length inp in
    let nb = len / bs in
    repeat_blocks_multi #a #b bs inp f init ==
    Lib.LoopCombinators.repeati nb (repeat_blocks_f bs inp f nb) init)

(** Generates `n` blocks of length `len` by iteratively applying a function with an accumulator *)
val generate_blocks:
    #t:Type0
  -> len:size_nat
  -> max:nat
  -> n:nat{n <= max}
  -> a:(i:nat{i <= max} -> Type)
  -> f:(i:nat{i < max} -> a i -> a (i + 1) & s:seq t{length s == len})
  -> init:a 0 ->
  Tot (a n & s:seq t{length s == n * len})

(** Generates `n` blocks of length `len` by iteratively applying a function without an accumulator *)

val generate_blocks_simple:
   #a:Type0
 -> blocksize:size_pos
 -> max:nat
 -> n:nat{n <= max}
 -> f:(i:nat{i < max} -> lseq a blocksize) ->
 Tot (s:seq a{length s == n * blocksize})

(** The following functions allow us to bridge between unbounded and bounded sequences *)


val div_interval: b:pos -> n:int -> i:int -> Lemma
  (requires n * b <= i /\ i < (n + 1) * b)
  (ensures  i / b = n)

val mod_interval_lt: b:pos -> n:int -> i:int -> j:int -> Lemma
  (requires n * b <= i /\ i < j /\ j < (n + 1) * b)
  (ensures  i % b < j % b)

val div_mul_lt: b:pos -> a:int -> n:int -> Lemma
  (requires a < n * b)
  (ensures  a / b < n)

val mod_div_lt: b:pos -> i:int -> j:int -> Lemma
  (requires (j / b) * b <= i /\ i < j)
  (ensures  i % b < j % b)

val div_mul_l: a:int -> b:int -> c:pos -> d:pos -> Lemma
  (requires a / d = b / d)
  (ensures  a / (c * d) = b / (c * d))


let map_blocks_a (a:Type) (bs:size_nat) (max:nat) (i:nat{i <= max}) = s:seq a{length s == i * bs}

let map_blocks_f
  (#a:Type)
  (bs:size_nat{bs > 0})
  (max:nat)
  (inp:seq a{length inp == max * bs})
  (f:(i:nat{i < max} -> lseq a bs -> lseq a bs))
  (i:nat{i < max})
  (acc:map_blocks_a a bs max i) : map_blocks_a a bs max (i + 1)
=
  Math.Lemmas.lemma_mult_le_right bs (i+1) max;
  let block = Seq.slice inp (i*bs) ((i+1)*bs) in
  Seq.append acc (f i block)


val map_blocks_multi:
    #a:Type0
  -> blocksize:size_pos
  -> max:nat
  -> n:nat{n <= max}
  -> inp:seq a{length inp == max * blocksize}
  -> f:(i:nat{i < max} -> lseq a blocksize -> lseq a blocksize) ->
  Tot (out:seq a {length out == n * blocksize})


val lemma_map_blocks_multi:
    #a:Type0
  -> blocksize:size_pos
  -> max:nat
  -> n:nat{n <= max}
  -> inp:seq a{length inp == max * blocksize}
  -> f:(i:nat{i < max} -> lseq a blocksize -> lseq a blocksize)
  -> Lemma
  (map_blocks_multi #a blocksize max n inp f ==
   LoopCombinators.repeat_gen n (map_blocks_a a blocksize max) (map_blocks_f #a blocksize max inp f) Seq.empty)


#restart-solver
val index_map_blocks_multi:
    #a:Type0
  -> bs:size_pos
  -> max:pos
  -> n:pos{n <= max}
  -> inp:seq a{length inp == max * bs}
  -> f:(i:nat{i < max} -> lseq a bs -> lseq a bs)
  -> i:nat{i < n * bs}
  -> Lemma (
    div_mul_lt bs i n;
    let j = i / bs in
    let block: lseq a bs = Seq.slice inp (j * bs) ((j + 1) * bs) in
    Seq.index (map_blocks_multi bs max n inp f) i == Seq.index (f j block) (i % bs))

(* A full block index *)
unfold
let block (len:nat) (blocksize:size_pos) = i:nat{i < len / blocksize}

(* Index of last (incomplete) block *)
unfold
let last  (len:nat) (blocksize:size_pos) = i:nat{i = len / blocksize}

val map_blocks:
    #a:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(block (length inp) blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last (length inp) blocksize -> rem:size_nat{rem < blocksize} -> s:lseq a rem -> lseq a rem) ->
  Tot (out:seq a{length out == length inp})

val lemma_map_blocks:
    #a:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(block (length inp) blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last (length inp) blocksize -> rem:size_nat{rem < blocksize} -> s:lseq a rem -> lseq a rem) ->
  Lemma (
    let len = length inp in
    let nb = len / blocksize in
    let rem = len % blocksize in
    let blocks = Seq.slice inp 0 (nb * blocksize) in
    let last = Seq.slice inp (nb * blocksize) len in
    Math.Lemmas.cancel_mul_div nb blocksize;
    let bs = map_blocks_multi #a blocksize nb nb blocks f in
    let res = if (rem > 0) then Seq.append bs (g nb rem last) else bs in
    res == map_blocks #a blocksize inp f g)


(* Computes the block of the i-th element of (map_blocks blocksize input f g) *)
let get_block
  (#a:Type)
  (#len:nat)
  (blocksize:size_pos)
  (inp:seq a{length inp == len})
  (f:(block len blocksize -> lseq a blocksize -> lseq a blocksize))
  (i:nat{i < (len / blocksize) * blocksize}) :
  Pure (lseq a blocksize) True (fun _ -> i / blocksize < len / blocksize)
=
  div_mul_lt blocksize i (len / blocksize);
  let j: block len blocksize = i / blocksize in
  let b: lseq a blocksize = Seq.slice inp (j * blocksize) ((j + 1) * blocksize) in
  f j b


(* Computes the last block of (map_blocks blocksize input f g) *)
#push-options "--z3rlimit_factor 2"
let get_last
  (#a:Type)
  (#len:nat)
  (blocksize:size_pos)
  (inp:seq a{length inp == len})
  (g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem))
  (i:nat{(len / blocksize) * blocksize <= i /\ i < len}) :
  Pure (lseq a (len % blocksize)) True (fun _ -> i % blocksize < len % blocksize)
=
  mod_div_lt blocksize i len;
  let rem = len % blocksize in
  let b: lseq a rem = Seq.slice inp (len - rem) len in
  g (len / blocksize) rem b
#pop-options

val index_map_blocks:
    #a:Type
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(block (length inp) blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last (length inp) blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> i:nat{i < length inp} ->
  Lemma (
    let output = map_blocks blocksize inp f g in
    let j = i % blocksize in
    if i < (length inp / blocksize) * blocksize
    then
      let block_i = get_block blocksize inp f i in
      Seq.index output i == Seq.index block_i j
    else
      let block_i = get_last blocksize inp g i in
      Seq.index output i == Seq.index block_i j
  )


val eq_generate_blocks0:
    #t:Type0
  -> len:size_nat
  -> n:nat
  -> a:(i:nat{i <= n} -> Type)
  -> f:(i:nat{i < n} -> a i -> a (i + 1) & s:seq t{length s == len})
  -> init:a 0 ->
  Lemma (generate_blocks #t len n 0 a f init ==
         (init,Seq.empty))

val unfold_generate_blocks:
    #t:Type0
  -> len:size_nat
  -> n:nat
  -> a:(i:nat{i <= n} -> Type)
  -> f:(i:nat{i < n} -> a i -> a (i + 1) & s:seq t{length s == len})
  -> init:a 0
  -> i:nat{i < n} ->
  Lemma (generate_blocks #t len n (i+1) a f init ==
           (let (acc,s) = generate_blocks #t len n i a f init in
            let (acc',s') = f i acc in
            (acc',Seq.append s s')))

val index_generate_blocks:
    #t:Type0
  -> len:size_pos
  -> max:nat
  -> n:pos{n <= max}
  -> f:(i:nat{i < max} -> unit -> unit & s:seq t{length s == len})
  -> i:nat{i < n * len}
  -> Lemma (Math.Lemmas.lemma_mult_le_right len n max;
           div_mul_lt len i max;
           let a_spec (i:nat{i <= max}) = unit in
           let _,s1 = generate_blocks len max n a_spec f () in
           let _,s2 = f (i / len) () in
           Seq.index s1 i == Seq.index s2 (i % len))

#push-options "--using_facts_from '+FStar.Math.Lemmas.pow2_values'"

val create2: #a:Type -> x0:a -> x1:a -> lseq a 2

val create2_lemma: #a:Type -> x0:a -> x1:a ->
  Lemma (let s = create2 x0 x1 in
    s.[0] == x0 /\ s.[1] == x1)
  [SMTPat (create2 #a x0 x1)]

val create4: #a:Type -> x0:a -> x1:a -> x2:a -> x3:a -> lseq a 4

val create4_lemma: #a:Type -> x0:a -> x1:a -> x2:a -> x3:a ->
  Lemma (let s = create4 x0 x1 x2 x3 in
    s.[0] == x0 /\ s.[1] == x1 /\ s.[2] == x2 /\ s.[3] == x3)
  [SMTPat (create4 #a x0 x1 x2 x3)]

val create8: #a:Type -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a -> lseq a 8

val create8_lemma: #a:Type -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a ->
  Lemma (let s = create8 x0 x1 x2 x3 x4 x5 x6 x7 in
    s.[0] == x0 /\ s.[1] == x1 /\ s.[2] == x2 /\ s.[3] == x3 /\
    s.[4] == x4 /\ s.[5] == x5 /\ s.[6] == x6 /\ s.[7] == x7)
  [SMTPat (create8 #a x0 x1 x2 x3 x4 x5 x6 x7)]

val create16: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a
  -> x8:a -> x9:a -> x10:a -> x11:a -> x12:a -> x13:a -> x14:a -> x15:a -> lseq a 16

val create16_lemma: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a
  -> x8:a -> x9:a -> x10:a -> x11:a -> x12:a -> x13:a -> x14:a -> x15:a ->
  Lemma (let s = create16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 in
    s.[0] == x0 /\ s.[1] == x1 /\ s.[2] == x2 /\ s.[3] == x3 /\
    s.[4] == x4 /\ s.[5] == x5 /\ s.[6] == x6 /\ s.[7] == x7 /\
    s.[8] == x8 /\ s.[9] == x9 /\ s.[10] == x10 /\ s.[11] == x11 /\
    s.[12] == x12 /\ s.[13] == x13 /\ s.[14] == x14 /\ s.[15] == x15)
  [SMTPat (create16 #a x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)]

val create32: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a
  -> x8:a -> x9:a -> x10:a -> x11:a -> x12:a -> x13:a -> x14:a -> x15:a
  -> x16:a -> x17:a -> x18:a -> x19:a -> x20:a -> x21:a -> x22:a -> x23:a
  -> x24:a -> x25:a -> x26:a -> x27:a -> x28:a -> x29:a -> x30:a -> x31:a -> lseq a 32

val create32_lemma: #a:Type
  -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a
  -> x8:a -> x9:a -> x10:a -> x11:a -> x12:a -> x13:a -> x14:a -> x15:a
  -> x16:a -> x17:a -> x18:a -> x19:a -> x20:a -> x21:a -> x22:a -> x23:a
  -> x24:a -> x25:a -> x26:a -> x27:a -> x28:a -> x29:a -> x30:a -> x31:a ->
  Lemma (let s = create32 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
    s.[0] == x0 /\ s.[1] == x1 /\ s.[2] == x2 /\ s.[3] == x3 /\
    s.[4] == x4 /\ s.[5] == x5 /\ s.[6] == x6 /\ s.[7] == x7 /\
    s.[8] == x8 /\ s.[9] == x9 /\ s.[10] == x10 /\ s.[11] == x11 /\
    s.[12] == x12 /\ s.[13] == x13 /\ s.[14] == x14 /\ s.[15] == x15 /\
    s.[16] == x16 /\ s.[17] == x17 /\ s.[18] == x18 /\ s.[19] == x19 /\
    s.[20] == x20 /\ s.[21] == x21 /\ s.[22] == x22 /\ s.[23] == x23 /\
    s.[24] == x24 /\ s.[25] == x25 /\ s.[26] == x26 /\ s.[27] == x27 /\
    s.[28] == x28 /\ s.[29] == x29 /\ s.[30] == x30 /\ s.[31] == x31)
  [SMTPat (create32 #a x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)]

#pop-options
