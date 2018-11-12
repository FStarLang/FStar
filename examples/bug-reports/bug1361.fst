module Bug1361

open FStar.List.Tot

let rec f (is:list int)
: Tot(list int)
           (decreases %[List.length is])
  =
match is with
| [] -> []
| i::is -> []

let f1 (is:list int) = f is

let f2 (is:list int) =
  let rec localf (is:list int)
    : Tot(list int)
           (decreases %[List.length is])
      =
    match is with
    | [] -> []
    | i::is -> []
  in
    localf is
