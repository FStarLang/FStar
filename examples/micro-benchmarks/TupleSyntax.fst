module TupleSyntax
open FStar.Mul

(* non-dependent tuples: (t & t') *)
let f1 (x: int & int) : int = fst x
let f2 (x: int & (int & int)) : int = fst x
let f3 (x: int & (int & int)) : int & int = snd x
let f4 (x: int & int & int) : int = let fst, snd, third = x in fst * snd * third
let f5 (x: (int & int) & int) : int = fst (fst x) * snd (fst x) * snd x

(* dependent tuples: (x:t & t') *)
let g1 (x: (x:int & int)) : int = dfst x
let g2 (x: (x:int & (int & int))) : int = dfst x
let g3 (x: (x:int & (y:int & int))) : (y:int & int) = dsnd x
let g4 (x: (x:int & y:int & int)) : int = let (|fst, snd, third|) = x in fst * snd * third
let g5 (x: (x:(int & int) & int)) : int = fst (dfst x) + snd (dfst x) + dsnd x

(* mixed, resolved as dependent tuple *)
let h4 (x: (int & y:int & int)) : int = let (|fst, snd, third|) = x in fst * snd * third
