module Bug389

open FStar.ST

let a = alloc 0

val compose_self: #wp:(unit -> Tot (st_wp unit))
                -> $c:(x:unit -> STATE unit (wp x))
                -> St unit
let compose_self #wp c = ()

val f: unit -> STATE unit (fun 'p h -> 'p () (Heap.upd h a 0))
let f () = a := 0

val test': unit -> St unit
let test' () = a := 0;
              a := 0;
              f ();
              a := 0;
              a := 0;
              f ();
              a := 0;
              a := 0;
              f ();
              a := 0;
              a := 0

(* Adding some checkpoints to inference works *)
val test2': unit -> St unit
let test2' () = compose_self test'

val test: unit -> St unit
let test () = a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0;
              a := 0

val test2 : unit -> St unit
let test2 () = compose_self test
