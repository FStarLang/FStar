module Bug1389a

assume val or_else : (#a:Type) -> (f : (unit -> Ex a)) -> (g : (unit -> Ex a)) -> Ex a
assume val fail : (#a:Type) -> string -> Ex a

let rec first #a (ts : list (unit -> Ex a)) : Ex a =
    match ts with
    | [] -> fail "no tactics to try"
    | t::ts -> or_else #a t (first #(unit -> Ex a) ts)

let first2 #a (ts : list (unit -> Ex a)) : Ex a =
    match ts with
    | [] -> fail "no tactics to try"
    | t::ts -> or_else #a t (first #(unit -> Ex a) ts)

// fails appropriately
(*
let rec first_int (ts : list (unit -> Ex int)) : Ex int =
    match ts with
    | [] -> fail "no tactics to try"
    | t::ts -> or_else #int t (first_int ts)
*)
