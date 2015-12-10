module DList
open FStar.List

type dList1 't =
    | Nil : dList1 't
    | Unit : 't -> dList1 't
    | Join : dList1 't -> dList1 't -> nat -> dList1 't

val isCorrectJoined : l : dList1 't -> Tot bool
let rec isCorrectJoined l =
    match l with
    | Nil -> true
    | Unit x -> true
    | Join Nil _ _ -> false
    | Join x y l -> isCorrectJoined x && isCorrectJoined y

//unverifieble
type dList 't = l:(dList1 't){isCorrectJoined l}

//verifieble
//type dList 't = l:dList1 't

val ld: l:dList 't -> Tot (v:pos)
let rec ld t =
    match t with
    | Nil -> 1
    | Unit x -> 1
    | Join x y _ -> 1 + ld x + ld y

val lt: l:list(dList 't) -> Tot (v:pos)
let rec lt l = 
    match l with 
    | [] -> 1
    | hd :: tl -> 1 + ld hd + lt tl

#reset-options

val finish : rights : list (dList 't) -> xs : 'a -> f : ('a -> 't -> Tot 'a) 
-> Tot 'a  (decreases %[lt rights; 1])
val walk : rights : list (dList 't)  -> l : dList 't -> xs : 'a -> f : ('a -> 't -> Tot 'a) 
-> Tot 'a (decreases %[ld l + lt rights; 0])
let rec walk rights l xs f =
    match l with
    | Nil         -> finish rights xs f
    | Unit x      -> finish rights (f xs x) f
    | Join x y _  -> walk (y::rights) x xs f
and finish rights xs f =
    match rights with
    | []     -> xs
    | hd::tl -> walk tl hd xs f

(* val fold : f : ('a -> 't -> Tot 'a) -> st : 'a -> l : dList 't -> Tot (v : 'a) *)
(* let fold f state l = walk [] l state f *)
