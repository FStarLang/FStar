module ID5

(* This file used to test the identity effect with a weakest-precondition
   index.  The WP index and layered-effect declaration are gone; what remains
   is the ordinary identity monad, used explicitly with let!. *)

type id (a:Type u#a) : Type u#a = a

let return #a (x:a) : id a = x
let bind #a #b (x:id a) (f:a -> id b) : id b = f x
let (let!) #a #b (x:id a) (f:a -> id b) : id b = bind x f

let test_f () : id int = return 3

let l () : int = test_f ()

open FStar.List.Tot

let rec pmap #a #b (f : a -> id b) (l : list a) : id (list b)
  = match l with
    | [] -> return []
    | x::xs ->
      let! y = f x in
      let! ys = pmap f xs in
      return (y :: ys)

let even x = x % 2 == 0

let fmap (x:nat) : id nat =
  let r = x / 2 in
  return r

let callmap () : id (list nat) =
 let lmap : list nat = [2;4;6;8] in
 pmap fmap lmap

let rec count (n:nat) : id int
 = if n = 0 then return 0 else count (n-1)
 
let rec pow2 (n:nat) : id int
 = if n = 0 then return 1 else
   let! x = pow2 (n-1) in
   let! y = pow2 (n-1) in
   return (x + y)
 
let rec fibl (i:nat) : id nat =
  if i = 0 || i = 1
  then return 1
  else fibl (i-1)
  
let rec fibr (i:nat) : id nat =
  if i = 0 || i = 1
  then return 1
  else fibr (i-2)

let rec fib (i:nat) : id nat =
  if i < 2
  then return 1
  else let! x = fib (i-1) in
       let! y = fib (i-2) in
       return (x+y)

let rec idiv (a b : nat{b > 0}) : id int
  =
  if a < b
  then return 0
  else let! r = idiv (a-b) b in
       return (1 + r)
  
#push-options "--admit_smt_queries true"
let rec ack (m n : nat) : id nat =
  match m, n with
  | 0, n -> return (n+1)
  | m, 0 -> ack (m-1) 1
  | m, n -> let! r = ack m (n-1) in ack (m-1) r
#pop-options

let add1 (x:int) : Pure (id int) (requires (x > 0)) (ensures (fun r -> r == x+1)) = return (x + 1)

let tot_i #a (f : unit -> Tot a) : id a =
  return (f ())

let i_tot #a (f : unit -> id a) : Tot a =
  f ()

let rec sum (l : list int) : id int
 = match l with
   | [] -> return 0
   | x::xs -> sum xs
