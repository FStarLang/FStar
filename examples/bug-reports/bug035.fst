module Bug035

assume val factorial : n:nat -> Tot nat
assume val foo: n:int -> Tot (y:int{y=factorial n})
