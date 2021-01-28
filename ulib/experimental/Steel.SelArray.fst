module Steel.SelArray

let array t = ref (Seq.seq t)

let is_array r = ptr r
let array_sel r = ptr_sel r

let alloc x n =
  let s = Seq.create (U32.v n) x in
  alloc s

let index r i =
  let s = read r in
  Seq.index s (U32.v i)

let upd r i x =
  let s = read r in
  let s' = Seq.upd s (U32.v i) x in
  write r s'

let free r = free r
