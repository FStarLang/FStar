module Bug1065c

assume val t : Type

assume val proof : squash t

#set-options "--no_smt"

val ref : _:unit{t}
let ref  = proof

let id1 (x : (_:unit{t})) : squash t = x

let id2 (x : squash t) : (_:unit{t}) = x
