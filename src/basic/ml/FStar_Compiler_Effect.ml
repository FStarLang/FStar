let pipe_right (x : 'a) (f : ('a -> 'b)) : 'b = f x
let pipe_left  (f : ('a -> 'b)) (x : 'a) : 'b = f x

type 'a ref' = 'a ref
type 'a ref = 'a ref'

let op_Bang (r:'a ref) = !r
let op_ColonEquals x y = x := y
let alloc x = ref x
let raise = raise
let exit i = exit (Z.to_int i)
let try_with f1 f2 = try f1 () with | e -> f2 e
exception Failure = Failure
let failwith x = raise (Failure x)
