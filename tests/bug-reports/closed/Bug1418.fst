module Bug1418

open FStar.Ghost

noeq
type vector (a:Type) : nat -> Type =
    | Nil : vector a 0
    | Cons: #l:erased nat
            -> hd:a
            -> tl:vector a (reveal l)
            -> vector a (reveal l + 1)

let v1 : vector unit 1 = Cons () Nil

val fold(#a #state:Type)(#l:erased nat):
    (state -> a -> state)
    -> state
    -> vector a (reveal l)
    -> Tot state (decreases (reveal l))
let rec fold #_ #_ #_ f s = function
    | Cons hd tl -> 
        fold f (f s hd) tl
    | Nil -> s
