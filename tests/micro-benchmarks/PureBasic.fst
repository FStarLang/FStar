module PureBasic

/// The precondition of a `Pure` call must be pushed into the VC at the call
/// site, exactly like a refinement-typed argument, and the postcondition must
/// be usable by the continuation.

assume
val div : x:int -> y:int -> Pure int (requires (y =!= 0)) (ensures (fun r -> r * y == x))

let ok (x:int) : Pure int (requires True) (ensures (fun r -> r * 2 == x)) =
  div x 2

/// The postcondition of the inner call is available when checking the outer one.
let chained (x:int) : Pure int (requires True) (ensures (fun r -> True)) =
  let a = div x 2 in
  let b = div a 3 in
  b

/// A `Pure` computation with a trivial specification is just `Tot`.
let tot_is_pure (x:int) : Tot int = x + 1
