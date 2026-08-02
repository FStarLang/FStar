module IfJoin

/// Branch joining: the two branches of an `if` may have different effects and
/// different specifications.  The result must sit at the *join* of the two
/// effects in the lattice, with the branch conditions guarding each branch's
/// pre- and postcondition.

assume val pos : x:int -> Pure int (requires (x > 0)) (ensures (fun r -> r > 0))
assume val neg : x:int -> Div   int (requires (x < 0)) (ensures (fun r -> r < 0))

/// Pure `then`, Div `else` ==> the whole thing is Div.
let joined (x:int) : Div int (requires (x =!= 0)) (ensures (fun r -> r =!= 0)) =
  if x > 0 then pos x else neg x

/// Both branches Pure ==> the whole thing stays Pure.
let both_pure (x:int) : Pure int (requires (x > 0)) (ensures (fun r -> r > 0)) =
  if x > 1 then pos x else pos (x + 1)

/// The branch condition must be assumed when checking the branch's
/// precondition: neither `pos` nor `neg` is applicable without it.
let needs_guard (x:int) : Div int (requires True) (ensures (fun _ -> True)) =
  if x > 0 then pos x
  else if x < 0 then neg x
  else 0

/// Same for `match`.
let matched (b:bool) (x:int) : Pure int (requires (x > 0)) (ensures (fun r -> r > 0)) =
  match b with
  | true -> pos x
  | false -> x
