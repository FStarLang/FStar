module ID2

(* The old file was an identity layered effect indexed by pure WPs.  It is now
   the plain identity monad with the same small computations written using
   explicit monadic bind. *)

type id (a:Type u#a) : Type u#a = a

let return #a (x:a) : id a = x
let bind #a #b (x:id a) (f:a -> id b) : id b = f x
let (let!) #a #b (x:id a) (f:a -> id b) : id b = bind x f

let rec count (n:nat) : id int =
  if n = 0 then return 0 else count (n-1)

let test_f () : id int = return 5

let test_2 () : id int = return 5

let l () : int = test_f ()

let rec sum (l : list int) : id int =
  match l with
  | [] -> return 0
  | x::xs ->
    let! s = sum xs in
    return (x + s)
