type 'a __ref = 'a ref
type 'a ref = 'a __ref
let read x = !x
let op_Colon_Equals = (fun i r v -> r := v)
let alloc x = ref x

