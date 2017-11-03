module Bug405

val f: f:(unit -> Tot unit){True}
let f () = ()

val g: f:(unit -> Tot unit){True} -> Tot (u:unit{f () = ()})
let g f = ()

val v: u:unit{f () = ()}
let v = g f
