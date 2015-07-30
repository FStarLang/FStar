module Bug289

val foo : unit -> ST unit 
                     (requires (fun _ -> True))
                     (ensures  (fun _ r _  -> True)) 
let foo  () = ()

val test : unit -> unit
let test () = ()

(* val bar : unit -> unit *)
let bar () = let u = foo () in assert(False) //; test ()
