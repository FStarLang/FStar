module Test

type T = 
  | MkT : int -> T

let g (MkT i) (MkT j) = i - j  
