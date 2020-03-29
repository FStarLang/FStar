module GhostImplicits
module G = FStar.Ghost

//We have a simple indexed type
type t (n:nat) = m:nat{m == n}

//And a function that takes the index as an implicit argument
//returning a non-informative type, e.g., unit, Type, G.erased ...
let f (#x:nat) (y:t x) : unit = ()

//Now, if you call f with an explicit argument, it's fine
let test (x:G.erased nat) (y:t (G.reveal x)) : unit = f #(Ghost.reveal x) y

//But, leave it implicit and although F* infers the same elaboration
//as the term above it rejects it
let test2 (x:G.erased nat) (y:t (G.reveal x)) : unit = f y

//But, if you have a function that is not computationally irrelevant,
//then instantiating its implicits to ghost terms should fail
let g (#x:nat) (y:t x) : nat = 0

//But, leave it implicit and although F* infers the same elaboration
//as the term above it rejects it
[@(expect_failure [34])]
let test3 (x:G.erased nat) (y:t (G.reveal x)) : nat = g y



//But, if you have a function that is not computationally irrelevant,
//then instantiating its implicits to ghost terms should fail
let h (#x:G.erased nat) (y:t (G.reveal x)) : nat = 0

//But, leave it implicit and although F* infers the same elaboration
//as the term above it rejects it
let test4 (x:G.erased nat) (y:t (G.reveal x)) : nat = h y
