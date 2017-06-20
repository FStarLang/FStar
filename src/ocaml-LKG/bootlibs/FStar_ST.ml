type nonrec 'a ref = 'a ref
let read x = !x
let op_Colon_Equals x y = x := y
let write x y = x := y
let alloc x = ref x
let get () = ()
