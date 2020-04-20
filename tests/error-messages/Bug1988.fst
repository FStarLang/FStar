module Bug1988

[@(expect_failure [189])]
let x : int = "string literal"

assume type ident
assume val text_of_id  : ident -> string

noeq
type t = { tm : ident * int }

[@(expect_failure [54])]
let f1 e : bool =
    match e.tm with
    | (id, _) when text_of_id = "blah" -> false (* forgot to apply to id *)
    | _ -> true

[@(expect_failure [54])]
let f2 (e:t) : bool =
    match e.tm with
    | (id, _) when text_of_id = "blah" -> false (* forgot to apply to id *)
    | _ -> true
