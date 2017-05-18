open FStar_CommonST

open FStar_HyperHeap
open FStar_HyperStack

let push_frame () = ()
let pop_frame () = ()

let def_rid = root

let salloc (contents:'a) :('a reference) =
  let r = alloc contents in
  MkRef (root, r)

let salloc_mm (contents:'a) :('a reference) =
  let r = alloc contents in
  MkRef (root, r)

let sfree r = ()

let new_region = (fun r0 -> def_rid)
let new_colored_region = (fun r0 c -> def_rid)

let ralloc i (contents:'a) :('a reference) =
  let r = alloc contents in
  MkRef (i, r)  

let ralloc_mm i (contents:'a) :('a reference) =
  let r = alloc contents in
  MkRef (i, r)  

let rfree r = ()

let op_Colon_Equals r v = match r with
  | MkRef (_, r) -> op_Colon_Equals r v

let op_Bang r = match r with
  | MkRef (_, r) -> op_Bang r

let get () = HS (FStar_Map.const FStar_Heap.emp, def_rid)

let recall = (fun r -> ())

let recall_region = (fun r -> ())
