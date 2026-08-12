module ID4

(* This example used to package monotonicity evidence for an identity effect.
   After removing WP indices, the surviving computation model is just the
   identity monad. *)

type id (a:Type u#a) : Type u#a = a

let return #a (x:a) : id a = x
let bind #a #b (x:id a) (f:a -> id b) : id b = f x
let (let!) #a #b (x:id a) (f:a -> id b) : id b = bind x f

let test_f () : id int = return 3

let l () : int = test_f ()

let br (n:nat) : id bool =
 if n = 0 then return true else return false
  
let add1 (x:int) : Pure (id int) (requires (x > 0)) (ensures (fun r -> r == x+1)) = return (x + 1)

let rec count (n:nat) : id int
 = if n = 0 then return 0 else count (n-1)

let rec fib (i:nat) : id nat =
  if i = 0 || i = 1
  then return 1
  else let! x = fib (i-1) in
       let! y = fib (i-2) in
       return (x+y)

let rec idiv (a b : nat{b > 0}) : id int
  =
  if a < b
  then return 0
  else begin
   assert (a-b << a);
   let! r = idiv (a-b) b in
   return (1 + r)
  end

let rec sum (l : list int) : id int
 = match l with
   | [] -> return 0
   | x::xs -> sum xs
