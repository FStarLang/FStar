type 'a ref = 'a Stdlib.ref
let alloc x = Stdlib.ref x
let op_Bang x = Stdlib.(!) x
let op_Colon_Equals x v = Stdlib.(:=) x v
exception Failure = Failure
let failwith x = raise (Failure x)
let exit i = exit (Z.to_int i)
let try_with f g = try f () with e -> g e
