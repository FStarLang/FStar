module Bug379

val test1 : nat -> nat -> Tot nat
let rec test1 x y = if x = 0 then y else test1 0 y

val test2 : nat -> Tot (nat -> Tot nat)
let rec test2 x y = if x = 0 then y else test2 0 y

val test3 : nat -> Tot ( nat -> Dv nat)
let rec test3 x y = if x = 0 then y else test3 0 y

val test4 : nat -> Tot (nat -> Tot nat)
let rec test4 x = let f y = if x = 0 then y else test4 0 y in f

val test5 : nat -> Tot (nat -> Dv nat)
let rec test5 x =
  let f : _ -> Dv _ =
   (* ^ Needs an annotation to infer proper wp *)
    fun y -> if x = 0 then y else test5 0 y
  in
  if x = 0
  then f
  else
    let f' = test5 (x-1) in
    (fun y -> f' (f x))
