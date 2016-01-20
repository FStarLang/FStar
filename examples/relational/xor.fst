(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Bytes.fst sample.fst
  --*)

module Xor
open FStar.Bytes
open FStar.Bijection

assume val blocksize : int
type block = b:bytes{length b = blocksize}
assume val xor : block -> block -> Tot block

assume Xor_sym : (forall a b.{:pattern (xor a b)} xor a b = xor b a)
assume Xor_inv : (forall a b.{:pattern (xor a b)}xor (xor a b) a = b)
assume Xor_ass : (forall a b c.{:pattern (xor (xor a b) c); (xor a (xor b c))} xor (xor a b) c = xor a (xor b c))

opaque val xor_inj : a:block -> b:block -> c:block
              -> Lemma
              (requires (xor a b = xor a c))
              (ensures (b = c))
              [SMTPat (xor a b = xor a c)]
let xor_inj a b c = cut (b2t (xor (xor a b) a = xor (xor a c) a))
