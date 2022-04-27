//SNIPPET_START: t$
module UInt32

val t : eqtype
//SNIPPET_END: t$

//SNIPPET_START: bounds$
let n = 32
let min : nat = 0
let max : nat = pow2 n - 1
let u32_nat = n:nat{ n <= max }
//SNIPPET_END: bounds$

//SNIPPET_START: vu$
val v (x:t) : u32_nat
val u (x:u32_nat) : t

val uv_inv (x : t) : Lemma (u (v x) == x)
val vu_inv (x : u32_nat) : Lemma (v (u x) == x)
//SNIPPET_END: vu$
  
//SNIPPET_START: add_mod$
(** Addition modulo [2^n]

    Machine integers can always be added, but the postcondition is now
    in terms of addition modulo [2^n] on mathematical integers *)
val add_mod (a:t) (b:t) 
  : y:t { v y = (v a + v b) % pow2 n } 
//SNIPPET_END: add_mod$  

//SNIPPET_START: sub_mod$
(** Subtraction modulo [2^n]

    Machine integers can always be added, but the postcondition is now
    in terms of subtraction modulo [2^n] on mathematical integers *)
val sub_mod (a:t) (b:t) 
  : y:t { v y = (v a - v b) % pow2 n } 
//SNIPPET_END: sub_mod$

//SNIPPET_START: fits$
let fits (op: int -> int -> int)
         (x y : t)
  = min <= op (v x) (v y) /\
    op (v x) (v y) <= max
//SNIPPET_END: fits$

//SNIPPET_START: add$
(** Bounds-respecting addition

    The precondition enforces that the sum does not overflow,
    expressing the bound as an addition on mathematical integers *)
val add (a:t) (b:t { fits (+) a b }) 
  : y:t{ v y == v a + v b }
//SNIPPET_END: add$

//SNIPPET_START: sub$
(** Bounds-respecting subtraction

    The precondition enforces that the sum does not overflow,
    expressing the bound as an subtraction on mathematical integers *)
val sub (a:t) (b:t { fits (fun x y -> x - y) a b }) 
  : y:t{ v y == v a - v b }
//SNIPPET_END: sub$

//SNIPPET_START: lt$
(** Less than *)
val lt (a:t) (b:t) 
  : r:bool { r <==> v a < v b }
//SNIPPET_END: lt$
