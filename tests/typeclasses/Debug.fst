module Debug

class c (t:Type) = { dummy:unit }

instance c_int () : c int = { dummy=() }

let _ : c int = Tactics.Typeclasses.solve_debug
