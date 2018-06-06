module Bug293

val test : (a:int & b:int{a=b}) ->(unit*unit) -> Tot unit
let test (|a, b|) ((),()) =  assert(a = b)

(* This term in elaborated form is
let test x y =
  match x, t with
  | (|a, b|) ((),()) -> assert(a = b)


The equality in the body introduces two flex-flex subtyping constraints

   ?u_a   <: ?t
   ?u_b a <: ?t

If we solve these constraints in isolation, e.g., when closing the match,
then we set (?u_b a = ?u_a) rather than ?u_b a = fun a -> b:int{a=b}

And the program fails to verify
*)
