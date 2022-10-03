module ExtractMutRecTypesAndTerms

let rec f (x:nat) : Type =
  if x = 0 then unit
  else y:int { y == g (x - 1) } & f (x - 1)

and g (x:nat) : nat = 
  x
