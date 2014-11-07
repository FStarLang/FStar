module Sub

val foo : 'a -> int -> x:int{x>0}
let foo _ n = n

(* Shouldn't pring b2t, should print op_GreaterThan nicer
Error typing-error.fst(4,0-10,0): The following problems were found:
	Subtyping check failed; expected type
[Before:x:int{(b2t (op_GreaterThan x 0))}]
[After:x:int{(b2t (op_GreaterThan x 0))}];
got type
[Before:((fun 'a:Type => int) 'a)]
[After:int] 
(typing-error.fst(4,14-4,15))
*)
