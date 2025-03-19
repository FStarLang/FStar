exception Failure = Failure
let failwith x = raise (Failure x)
let exit i = exit (Z.to_int i)
