type 'a ref' = 'a ref[@@deriving yojson,show]
type 'a ref = 'a ref'[@@deriving yojson,show]

let op_Bang (r:'a ref) = !r
let op_Colon_Equals x y = x := y
let alloc x = ref x
let raise = raise
let exit i = exit (Z.to_int i)
exception Failure = Failure
let failwith x = raise (Failure x)
