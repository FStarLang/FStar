module Bug284

val foo : f:(unit -> Tot bool){f () = true}
          -> Tot (r:bool {r = f () /\ r = true})
let foo f = f ()

val bar : unit -> Pure bool (requires True) (ensures (fun _ -> False))
let bar () = foo (fun x -> false)
