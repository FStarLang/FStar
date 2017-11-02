module Bug026b

assume val factorial : n:nat -> Tot nat

(* This fails, when it shouldn't *)
assume val bar:n:int{n > 1} -> Tot (y:int{y=factorial n})

(* This fails, and rightly so
assume val foo: n:int -> Tot (y:int{y=factorial n})
*)
