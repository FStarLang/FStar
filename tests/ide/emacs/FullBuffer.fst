module FullBuffer
let f x = match x with | Some x -> true | None -> false
let test y = if Some? y then f y else true
