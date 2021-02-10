#light "off"
module FStar_ST

open FStar_CommonST

type 'a mref = 'a FStar_Monotonic_Heap.mref
type 'a ref = 'a FStar_Monotonic_Heap.ref

let read = read
let op_Bang = op_Bang

let write = write
let op_Colon_Equals = op_Colon_Equals

let alloc x = alloc

let recall = recall
let get = get

type 'a witnessed = 'a FStar_CommonST.witnessed

let gst_Witness = gst_witness
let gst_recall = gst_recall