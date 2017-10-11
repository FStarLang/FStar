module Bug417

assume val f: unit -> GTot bool

assume val coerce: $g:(unit -> GTot unit) -> unit -> Tot unit

let ok =
  let g : unit -> GTot unit = fun _ -> let _ = f () in () in
  coerce g


let fails =
  coerce (fun _ -> let _ = f () in ())  //rightfully, because the inferred type is not **equal** to (unit -> GTot unit), although it can be subsumed to that type
