module Bug

type foo = unit -> St unit

val fail1 : (unit * foo) -> unit
let fail1 p = assert (fst p = fst p)

val fail2 : (unit * foo) -> unit
let fail2 p = let x = fst p in 
              let y = fst p in 
              assert (y = x)

val works : (unit * foo) -> unit
let works p = let x = match p with
                      | a,b -> a in 
              let y = match p with
                      | a,b -> a in 
              assert (y = x)
            
