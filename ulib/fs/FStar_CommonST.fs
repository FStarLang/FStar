module FStar_CommonST

open FStar_Monotonic_Heap

let read x = x.contents

let op_Bang x = read x

let write x y = x.contents <- y

let op_Colon_Equals x y = write x y

let uid = ref 0

let alloc contents =
  let id = incr uid; !uid in
  let r = { id = id; contents = contents } in
  r

let recall = (fun r -> ())
let get () = ()

type 'a witnessed = | C

let gst_witness = (fun r -> ())
let gst_recall = (fun r -> ())
