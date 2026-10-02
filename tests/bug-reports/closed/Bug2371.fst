module Bug2371

// A Pure postcondition must be usable as a refinement on the return type
// when passing the function itself, without eta-expanding it.
assume val f : unit -> Pure int (requires True) (ensures fun x -> x >= 0)
assume val g (f:unit -> nat) : unit
let test () : unit = g f

// Check the converse direction and a weaker postcondition as well.
assume val refined : unit -> nat
let as_pure : unit -> Pure int (requires True) (ensures fun x -> x >= 0) = refined
let weakened : unit -> Pure int (requires True) (ensures fun x -> x >= -1) = refined
