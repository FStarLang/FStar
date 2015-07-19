module Bug252

(* Adding spurious type declaration also makes this work ... wtf? *)
(* type unused = int *)

(* Adding spurious parenthesis around `True` makes this work *)
assume val foo : unit -> Pure unit (requires True) (ensures (fun _ -> False))
