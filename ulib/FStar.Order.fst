module FStar.Order

type order = | Lt | Eq | Gt

// NOTE: the following six functions are not defined using `=` and `<>`
// intentionally, as those operators have limited reduction semantics
// (which we should add!). Thus we implement them by pattern matching,
// which does reduce well. This is essential to call from within a
// tactic.

// Some derived checks
val ge : order -> bool
let ge o =
    match o with
    | Lt -> false
    | _ -> true

val le : order -> bool
let le o =
    match o with
    | Gt -> false
    | _ -> true

val ne : order -> bool
let ne o =
    match o with
    | Eq -> false
    | _ -> true

// Just for completeness and consistency...
val gt : order -> bool
let gt o =
    match o with
    | Gt -> true
    | _ -> false

val lt : order -> bool
let lt o =
    match o with
    | Lt -> true
    | _ -> false

val eq : order -> bool
let eq o =
    match o with
    | Eq -> true
    | _ -> false

// Lexicographical combination, thunked to be lazy
val lex : order -> (unit -> order) -> order
let lex o1 o2 =
    match o1, o2 with
    | Lt, _ -> Lt
    | Eq, _ -> o2 ()
    | Gt, _ -> Gt

val order_from_int : int -> order
let order_from_int i =
    if i < 0 then Lt
    else if i = 0 then Eq
    else Gt

val compare_int : int -> int -> order
let compare_int i j = order_from_int (i - j)

val compare_list : ('a -> 'a -> order) -> list 'a -> list 'a -> order
let rec compare_list f l1 l2 =
    match l1, l2 with
    | [], [] -> Eq
    | [], _ -> Lt
    | _, [] -> Gt
    | x::xs, y::ys -> lex (f x y) (fun () -> compare_list f xs ys)
