module Bug26

assume val factorial : n:nat -> Tot nat
assume val bar:n:int{n > 1} -> Tot (y:int{y==factorial n})
