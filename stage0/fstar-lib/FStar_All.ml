exception Failure = Failure (* NB: reusing OCaml's native Failure. *)
let exit i = exit (Z.to_int i)
(* Not used: handled specially by extraction. If used,
   you will get all sorts of weird failures (e.g. an incomplete match
   on f2!). *)
(* let try_with f1 f2 = try f1 () with | e -> f2 e *)
(* let failwith x = raise (Failure x) *)
