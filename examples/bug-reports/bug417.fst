module Bug417

assume val f: unit -> GTot bool

assume val coerce: $g:(unit -> GTot unit) -> unit -> Tot unit

let ok =
  let g : unit -> GTot unit = fun _ -> let _ = f () in () in
  coerce g

//this used to fail, because the inferred type is not **equal** to (unit -> GTot unit), although it can be subsumed to that type
//Until the change described in https://github.com/FStarLang/FStar/wiki/Minimizing-verification-conditions-by-omitting-redundant-equality-hypotheses
//infers it to have (unit -> GTot unit)
let no_longer_fails =
  coerce (fun _ -> let _ = f () in ())
