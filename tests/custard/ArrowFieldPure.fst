module ArrowFieldPure
noeq type rec_t = { fld: bool -> bool -> bool }
let mk () : rec_t = { fld = (fun a b -> a && b) }
let call_it (t: rec_t) (x: bool) : bool = t.fld x x
let main () : bool = call_it (mk ()) true
