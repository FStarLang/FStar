module State

open FStar.Tactics

let x : int = synth (fun () -> lset "myint" 1;
                               let y : int = lget "myint" in
                               exact (quote y))

let _ = assert (x == 1)

// Can't type 1 as a bool
[@Pervasives.fail]
let y : int = synth (fun () -> lset "myint" 1;
                               let y : bool = lget "myint" in
                               exact (quote y))
