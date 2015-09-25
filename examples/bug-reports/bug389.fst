(*--build-config
    options:--admit_fsi FStar.Set --log_types;
    other-files:set.fsi heap.fst st.fst all.fst
  --*)

module Bug389OutOfMem

let a = alloc 0

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

val compose_self : #wp:(unit -> STWP unit) ->
                   #wlp:(unit -> STWP unit)
                -> =c:(x:unit -> STATE unit (wp x) (wlp x))
                -> St unit
let compose_self _ = ()

val test2 : unit -> St unit
let test2 () = compose_self test
