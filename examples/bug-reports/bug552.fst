module Bug552

type mapping = int -> Tot int

let f : mapping = fun x -> x

let g:h:mapping{forall x. h x = x} = fun x -> x
