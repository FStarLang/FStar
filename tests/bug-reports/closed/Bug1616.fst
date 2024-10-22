module Bug1616

let rec f x =
    match x with
    | _ -> (fun y -> y)
