module FStar.Buffer.Quantifiers

open FStar.Seq
open FStar.UInt32
open FStar.HyperStack
open FStar.Ghost
open FStar.HST
open FStar.Buffer

val lemma_create_quantifiers: #a:Type -> h:mem -> b:buffer a -> init:a -> len:FStar.UInt32.t -> Lemma
  (requires (live h b /\ as_seq h b == Seq.create (v len) init))
  (ensures  (live h b /\ length b = v len
    /\ (forall (i:nat). {:pattern (get h b i)} i < length b ==> get h b i == init)))
  [SMTPat (as_seq h b); SMTPat (Seq.create (v len) init)]
let lemma_create_quantifiers #a h b init len =
  assert(forall (i:nat). i < length b ==> get h b i == Seq.index (as_seq h b) i)

val lemma_upd_quantifiers: #a:Type -> h0:mem -> h1:mem -> b:buffer a -> n:FStar.UInt32.t -> z:a -> Lemma
  (requires (live h0 b /\ live h1 b /\ v n < length b /\ as_seq h1 b == Seq.upd (as_seq h0 b) (v n) z))
  (ensures  (live h0 b /\ live h1 b /\ v n < length b
    /\ (forall (i:nat). {:pattern (get h1 b i)} (i < length b /\ i <> v n)
      ==> get h1 b i == get h0 b i)
    /\ get h1 b (v n) == z))
  [SMTPat (as_seq h1 b); SMTPat (Seq.upd (as_seq h0 b) (v n) z)]
let lemma_upd_quantifiers #a h0 h1 b n z =
  assert(forall (i:nat). i < length b ==> get h1 b i == Seq.index (as_seq h1 b) i)

val lemma_sub_quantifiers: #a:Type -> h:mem -> b:buffer a -> b':buffer a -> i:FStar.UInt32.t -> len:FStar.UInt32.t{v len <= length b /\ v i + v len <= length b} -> Lemma
  (requires (live h b /\ live h b' /\ Seq.slice (as_seq h b) (v i) (v i + v len) == as_seq h b'))
  (ensures  (live h b /\ live h b' /\ Seq.slice (as_seq h b) (v i) (v i + v len) == as_seq h b'
    /\ length b' = v len
    /\ (forall (j:nat). {:pattern (get h b' j)} j < length b' ==> get h b' j == get h b (j + v i)) ))
  [SMTPat (Seq.slice (as_seq h b) (v i) (v i + v len)); SMTPat (as_seq h b')]
let lemma_sub_quantifiers #a h b b' i len =
  assert(forall (j:nat). j < v len ==> Seq.index (Seq.slice (as_seq h b) (v i) (v i + v len)) j
    == Seq.index (as_seq h b) (j + v i))

val lemma_offset_quantifiers: #a:Type -> h:mem -> b:buffer a -> b':buffer a -> i:FStar.UInt32.t{v i <= length b} -> Lemma
  (requires (live h b /\ live h b' /\ Seq.slice (as_seq h b) (v i) (length b) == as_seq h b'))
  (ensures  (live h b /\ live h b' /\ Seq.slice (as_seq h b) (v i) (length b) == as_seq h b'
    /\ length b' = length b - v i
    /\ (forall (j:nat). {:pattern (get h b' j)} j < length b' ==> get h b' j == get h b (j + v i)) ))
  [SMTPat (Seq.slice (as_seq h b) (v i) (length b)); SMTPat (as_seq h b')]
let lemma_offset_quantifiers #a h b b' i =
  assert(forall (j:nat). j < length b - v i ==> Seq.index (Seq.slice (as_seq h b) (v i) (length b)) j
    == Seq.index (as_seq h b) (j + v i))
