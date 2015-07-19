module Bug252

(* Adding spurious parenthesis around `True` makes this work *)
assume val foo : unit -> Pure unit (requires True) (ensures (fun _ -> False))
