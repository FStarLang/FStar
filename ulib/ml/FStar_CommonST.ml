open FStar_Monotonic_Heap

let read x = !x

let op_Bang x = read x

let write x y = x := y

let op_Colon_Equals x y = write x y

let alloc contents = ref contents

let recall = (fun r -> ())
let get () = ()

type 'a witnessed = | C

let gst_witness = (fun r -> ())
let gst_recall = (fun r -> ())
