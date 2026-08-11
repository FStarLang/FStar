module ID3

(* The WP-indexed identity effect has been simplified to its underlying
   identity monad. *)

type id (a:Type u#a) : Type u#a = a

let return #a (x:a) : id a = x
let bind #a #b (x:id a) (f:a -> id b) : id b = f x
let (let!) #a #b (x:id a) (f:a -> id b) : id b = bind x f

let test_f () : id int = return 3

let l () : int = test_f ()

let rec sum (l : list int) : id int =
  match l with
  | [] -> return 0
  | x::xs ->
    assert (xs << l);
    let! s = sum xs in
    return (x + s)
