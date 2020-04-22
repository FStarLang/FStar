module Bug1097

let m (f : int -> int) : Tot int =
    match f with
    | x -> 0

// 114: type of pattern does not match scrutinee
// this used to succeed via SMT at some point
[@(expect_failure [114])]
let m2 (a:Type) (_ : a == int) (x : a) =
    match x with
    | 0 -> 0
    | _ -> 1

// but we can manually coerce
let coerce (#a:Type) (#b:Type{a==b}) (x:a) : b = x

let m2' (a:Type) (_ : a == int) (x : a) =
    match coerce x with
    | 0 -> 0
    | _ -> 1

let f (x:int) = x

(* incomplete patterns *)
[@(expect_failure [19])]
let m3 =
    match f with

let m4 =
    match f with
    | ff -> ff

let m5 =
    match (fun x -> x) with
    | ff -> ff
