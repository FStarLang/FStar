module DivLoop

/// `Div` computations are not required to terminate, but their pre/post are
/// still checked.  Because a `Div` result cannot be substituted back into the
/// specification, the checker must introduce a *logical-only* binder for it
/// (no term-level let is inserted).

assume val step : x:int -> Div int (requires (x >= 0)) (ensures (fun r -> r >= 0))

let rec loop (x:int) : Div int (requires (x >= 0)) (ensures (fun r -> r >= 0)) =
  if x = 0 then 0
  else loop (step x)

/// Two Div calls in sequence: the postcondition of the first must discharge the
/// precondition of the second.
let twice (x:int) : Div int (requires (x >= 0)) (ensures (fun r -> r >= 0)) =
  let a = step x in
  step a

/// Pure lifts into Div.
assume val pure_thing : x:int -> Pure int (requires True) (ensures (fun r -> r >= 0))

let lifted (x:int) : Div int (requires True) (ensures (fun r -> r >= 0)) =
  step (pure_thing x)
