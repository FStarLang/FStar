let op_Bang (r:'a ref) () () = !r
let op_Colon_Equals (r:'a ref) (v:'a) () = r := v
let alloc (v:'a) = ref v