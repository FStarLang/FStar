module FStar.DM4F.Heap.IntStoreFixed

open FStar.Seq

let store_size = 10

abstract type id : eqtype = i:nat{i < store_size}
abstract type heap : eqtype = h:seq int{length h < store_size}

let to_id (n:nat{n < store_size}) : id = n

let index (h:heap) (i:id) : Tot int = index h i
let sel = index
let upd (h:heap) (i:id) (x:int) : Tot heap = let h1 = upd h i x in assert (length h1 = store_size) ; h1

let create (x:int) : Tot heap = create #int store_size x
