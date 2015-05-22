module Bug35
open Prims.PURE

assume val factorial : n:nat -> Tot nat
assume val foo: n:int -> Tot (y:int{y=factorial n})
