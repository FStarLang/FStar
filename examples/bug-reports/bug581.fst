module Bug581

open FStar.All

//#set-options "--log_types --print_effect_args"

assume new type p: int -> Type0

assume val f: n:int{p n} -> int

//The three declarations below are equivalent and with all of them g fails to typecheck
//val g: unit -> int
//val g: unit -> ML int
//val g: unit -> ALL int (fun post _ -> forall a h. post a h)

//Inferred type and effect when no declaration is given; with it g typechecks
val g: unit -> ALL int (fun post _ -> p 0 /\ (forall a h. post a h))

let g () = f 0
