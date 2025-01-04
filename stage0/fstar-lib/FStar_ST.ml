(* https://www.lexifi.com/blog/references-physical-equality *)

open FStar_CommonST

type ('a, 'b) mref = ('a, 'b) FStar_Monotonic_Heap.mref
   
type 'a ref = 'a FStar_Monotonic_Heap.ref

let ref_to_yojson _ _ = `Null
let ref_of_yojson _ _ = failwith "cannot readback"

let read = read

let op_Bang = op_Bang

let write = write

let op_Colon_Equals = op_Colon_Equals

let alloc = alloc

let recall = recall
let get = get

type 'a witnessed = 'a FStar_CommonST.witnessed

let gst_witness = gst_witness
let gst_recall = gst_recall
