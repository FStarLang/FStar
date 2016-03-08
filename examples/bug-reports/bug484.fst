module Bug484


(* With "Tot", works fine *)
val ok : #a:Type
         -> p:(a -> GTot bool)
         -> f:(d:a -> Tot (r:a{p d ==> p r}))
         -> l:list a
         -> acc:a
         -> Tot a
let rec ok p f l a =
    match l with
        | [] -> a
        | x::xs -> f (ok p f xs a)


(* Doesn't work if I replace "Tot" by "ML" (or any other effect) *)
val bug : #a:Type
         -> p:(a -> GTot bool)
         -> f:(d:a -> ML (r:a{p d ==> p r}))
         -> l:list a
         -> acc:a
         -> ML a
let rec bug p f l a =
    match l with
        | [] -> a
        | x::xs -> f (bug p f xs a)

