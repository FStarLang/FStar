module FStar.Order

type order = | Lt | Eq | Gt

// Some derived checks
val ge : order -> bool
let ge o = o <> Lt

val le : order -> bool
let le o = o <> Gt

val ne : order -> bool
let ne o = o <> Eq

// Just for completeness and consistency...
val gt : order -> bool
let gt o = o = Gt

val lt : order -> bool
let lt o = o = Lt

val eq : order -> bool
let eq o = o = Eq

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

type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
  (forall a. f a a) (* reflexive *)
  /\ (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2)  (* anti-symmetry *)
  /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)   (* transitivity  *)
  /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                 (* totality      *)

type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}
