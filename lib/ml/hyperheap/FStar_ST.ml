type 'a __ref = 'a ref
type 'a ref = 'a __ref
let read x = !x
let op_Colon_Equals = (fun i r v -> r := v)
let op_Bang = (fun i r -> !r)
let alloc = (fun x -> ref x)
let new_region = (fun r0 -> ())
let ralloc = (fun i x -> ref x)
let recall = (fun i r -> ())
