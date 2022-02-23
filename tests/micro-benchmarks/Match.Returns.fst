module Match.Returns

let test1 (n:int) =
  match n + 1 as x returns (n:int{n > x}) with
  | 0 -> 1
  | _ -> n+2

open FStar.ST

// With returns annotation, the scrutinee must be pure/ghost

[@@ expect_failure]
let test2 (r:ref int) : St int =
  match !r as x returns St (n:int{n > x}) with
  | 0 -> 1
  | _ -> !r+2

let test2 (r:ref int) : St int =
  let n = !r in
  match n returns St (m:int{m > n}) with
  | 0 -> 1
  | _ -> n+2

