module Bug484

open FStar.All

(* With "Tot", works fine *)
val ok : #a:Type
         -> p:(a -> GTot bool)
         -> f:(d:a -> Tot (r:a{p d ==> p r}))
         -> l:list a
         -> acc:a
         -> Tot a
let rec ok #a p f l acc =
    match l with
        | [] -> acc
        | _::xs -> f (ok #a p f xs acc)


(* Changing the effect to ML works when binding the result of the recursive call *)
(* VD: This example now fails with "Bound term variable not found (after unmangling)" *)
val also_ok : #a:Type
         -> p:(a -> GTot bool)
         -> f:(d:a -> Tot (r:a{p d ==> p r}))
         -> l:list a
         -> acc:a
         -> ML a
let rec also_ok #a p f l acc =
    match l with
        | [] -> acc
        | _::xs -> let u = also_ok #a p f xs acc in f u


(* But it doesn't work otherwise *)
val bug : #a:Type
         -> p:(a -> GTot bool)
         -> f:(d:a -> Tot (r:a{p d ==> p r}))
         -> l:list a
         -> acc:a
         -> ML a
let rec bug #a p f l acc =
    match l with
        | [] -> acc
        | _::xs -> f (bug #a p f xs acc)
