//SNIPPET_START: sample
module Sample

let incr (x:int) : int = x + 1
//SNIPPET_END: sample

//SNIPPET_START: ex1.1
let incr1 (x:int) : y:int{y > x} = x + 1
//SNIPPET_END: ex1.1

//the expect_failure attribute tells F* to check that "Error 19" is
//raised on the next definition, to suppress an error report, and
//proceed with the rest of the file.
[@@expect_failure [19]]
//SNIPPET_START: ex1.2
let incr2 (x:int) : nat = x + 1
//SNIPPET_END: ex1.2

//SNIPPET_START: ex1.3
let incr3 (x:nat) : nat = x + 1
//SNIPPET_END: ex1.3
