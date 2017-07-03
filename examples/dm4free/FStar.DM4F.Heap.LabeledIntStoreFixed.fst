module FStar.DM4F.Heap.LabeledIntStoreFixed

open FStar.Seq
open Label

let store_size = 10

abstract type id : eqtype = i:nat{store_size > i}
abstract type heap : eqtype = h:seq (int * label) {store_size > length h}

let to_id (n:nat{store_size > n}) : id = n

let index (h:heap) (i:id) : Tot (int * label) = index h i
let sel = index
let upd (h:heap) (i:id) (x:(int * label)) : Tot heap = let h1 = upd h i x in assert (length h1 = store_size) ; h1

let create (x:(int*label)) : Tot heap = create #(int * label) store_size x

abstract val lemma_index_upd1: s:heap -> n:id -> v:(int * label) -> Lemma
  (requires True)
  (ensures (index (upd s n v) n == v))
  [SMTPat (index (upd s n v) n)]
let lemma_index_upd1 s n v = lemma_index_upd1 #(int * label) s n v

abstract val lemma_index_upd2: s:heap -> n:id -> v:(int * label) -> i:id{i<>n} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i == index s i))
  [SMTPat (index (upd s n v) i)]
let lemma_index_upd2 s n v i = lemma_index_upd2 #(int * label) s n v i


abstract val lemma_index_create: v:(int * label) -> i:id -> Lemma
  (requires True)
  (ensures (index (create v) i == v))
  [SMTPat (index (create v) i)]
let lemma_index_create v i = lemma_index_create #(int * label) store_size v i
