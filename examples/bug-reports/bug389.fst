(*--build-config
    options:--admit_fsi FStar.Set --log_types;
    other-files:set.fsi heap.fst st.fst all.fst
  --*)

module Bug389OutOfMem

let a = alloc 0

val compose_self : #wp:(unit -> STWP unit) ->
                   #wlp:(unit -> STWP unit)
                -> =c:(x:unit -> STATE unit (wp x) (wlp x))
                -> St unit
let compose_self _ = ()


val f : unit -> State unit (fun 'p h -> 'p () (Heap.upd h a 0))
let f () = a := 0

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
val test2' : unit -> St unit
let test2' () = compose_self test'

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
              a := 0

(* Works when setting --eager_inference in build-config options *)
(* This set-options apparently has no effect though *)
#set-options "--eager_inference"

val test2 : unit -> St unit
let test2 () = compose_self test
