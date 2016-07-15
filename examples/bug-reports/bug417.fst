module Bug417

assume val f: unit -> GTot bool

assume val coerce: $g:(unit -> GTot unit) -> unit -> Tot unit

let odd = coerce (fun _ -> let _ = f () in ())
