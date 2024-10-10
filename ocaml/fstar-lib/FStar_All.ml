exception Failure = Failure
let failwith x = raise (Failure x)
let exit i = exit (Z.to_int i)
let try_with f1 f2 = try f1 () with | e -> f2 e
