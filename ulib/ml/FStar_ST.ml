(* https://www.lexifi.com/blog/references-physical-equality *)

open FStar_CommonST

type ('a, 'b) mref = 'a FStar_Heap.ref
   
type 'a ref = 'a FStar_Heap.ref

let read = read

let op_Bang = op_Bang

let write = write

let op_Colon_Equals = op_Colon_Equals

let alloc = alloc

let recall = recall
let get = get
