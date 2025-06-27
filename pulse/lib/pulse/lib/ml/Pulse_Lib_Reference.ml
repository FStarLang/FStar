let op_Bang (r:'a ref) () () = !r
let op_Colon_Equals (r:'a ref) (v:'a) () = r := v
let alloc (v:'a) = ref v

let __null = alloc 0
let null : 'a ref = Obj.magic __null
let is_null (r:'a ref) : bool = r == __null
