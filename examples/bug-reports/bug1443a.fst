module Bug1443a

[@(expect_failure [66])]
let rec test ps = match ps with
  | [] -> 0
  | a::q ->
    let rec blah i = match i with
      | [] -> 0
      | b::r -> blah r
    in
    if a = 0 then 0
    else test q
