#light "off"

module FStar.Order

type order = | Lt | Eq | Gt

// Some derived checks
let ge (o : order) : bool = o <> Lt
let le (o : order) : bool = o <> Gt
let ne (o : order) : bool = o <> Eq

// Just for completeness and consistency...
let gt (o : order) : bool = o = Gt
let lt (o : order) : bool = o = Lt
let eq (o : order) : bool = o = Eq

// Lexicographical combination, thunked to be lazy
let lex (o1 : order) (o2 : unit -> order) : order =
    match o1, o2 with
    | Lt, _ -> Lt
    | Eq, _ -> o2 ()
    | Gt, _ -> Gt

let order_from_int (i : int) : order =
    if i < 0 then Lt
    else if i = 0 then Eq
    else Gt

let compare_int (i : int) (j : int) : order = order_from_int (i - j)

let rec compare_list (f : 'a -> 'a -> order) (l1 : list<'a>) (l2 : list<'a>) : order =
    match l1, l2 with
    | [], [] -> Eq
    | [], _ -> Lt
    | _, [] -> Gt
    | x::xs, y::ys -> lex (f x y) (fun () -> compare_list f xs ys)
