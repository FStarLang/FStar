module Bug1370b

effect Ouch (a:Type) = False

(* This should fail *)
let x () : Ouch unit = ()
