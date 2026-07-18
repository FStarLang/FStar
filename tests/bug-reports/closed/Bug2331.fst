module Bug2331

let ubool = Type

let fstar_bug () : Lemma (True) =
  let q1:(int -> GTot ubool) = fun (_:int) -> True in
  let q2:(int -> GTot ubool) = fun (_:int) -> True in
  assert (q1 == q2)
