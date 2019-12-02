module Bug1867

let u (a:Type) = unit

val return_u : (a:Type) -> a -> u a
let return_u a x = ()

val bind_u : (a:Type) -> (b:Type) -> (f:u a) -> (g: a -> u b) -> u b
let bind_u a b f g = ()

[@expect_failure]
total reifiable reflectable new_effect {
  U : (a:Type) -> Effect
  with repr = u
     ; bind = bind_u
     ; return = return_u
  }
