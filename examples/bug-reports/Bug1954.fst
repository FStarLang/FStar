module Bug1954

(* disable warning about needless let rec *)
#set-options "--warn_error -328"

%Fail [178]
let blah = match None with | (None : option int) -> ()

let         addp ((x, y) : int & int) : int = x + y
let rec rec_addp ((x, y) : int & int) : int = x + y

let         addp' = fun ((x,y) : int & int) -> x + y <: int
let rec rec_addp' = fun ((x,y) : int & int) -> x + y <: int

type box a = | Box of a

let unbox (Box x) : int = x

let unbox' (Box x : box int) : int = x

let unbox'' (Box (x : int) : box int) : int = x

%Fail [178]
let g b =
    match b with
    | (Box x : box int) -> x
