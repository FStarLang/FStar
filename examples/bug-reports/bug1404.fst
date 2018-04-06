module Bug1404

(* This should fail with :
 * bug1404.fst(9,6-10,17): (Error 297) Patterns in this match are incoherent, variable y is bound in some but not all patterns.
 *)
let f o =
    match o with
    | (Some x, _)
    | (x, Some y) -> y
    | _ -> false
