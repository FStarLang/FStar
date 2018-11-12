module Bug1389b

effect MyTot (a:Type) = PURE a (fun p -> forall x. p x)
assume val or_else : (#a:Type) -> (f : (unit -> MyTot a)) -> (g : (unit -> MyTot a)) -> MyTot a
assume val fail : (#a:Type) -> string -> MyTot a

let rec first #a (ts : list (unit -> MyTot a)) : MyTot a =
    match ts with
    | [] -> fail "no tactics to try"
    | t::ts -> or_else #a t (first #(unit -> MyTot a) ts)

let first2 #a (ts : list (unit -> MyTot a)) : MyTot a =
    match ts with
    | [] -> fail "no tactics to try"
    | t::ts -> or_else #a t (first #(unit -> MyTot a) ts)

// fails appropriately
(*
let rec first_int (ts : list (unit -> MyTot int)) : MyTot int =
    match ts with
    | [] -> fail "no tactics to try"
    | t::ts -> or_else #int t (first_int ts)
*)
