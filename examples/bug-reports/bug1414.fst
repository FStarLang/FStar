module Bug1414

open FStar.Tactics

let constant (t:term) : Tac unit = exact (norm_term [primops; delta; iota; zeta] t)

let f (x:option int) : int = if Some? x then Some?.v x else 0
let c1 : int = (synth (fun()-> constant (`( f (Some 42) ))))
// c1 = 42
let _ = assert_by_tactic (c1 == 42) trefl

let f' (x:list int) : int = if Cons? x then Cons?.hd x else 0
let c1' : int = (synth (fun()-> constant (`( f' (Cons 42 Nil) ))))
// c1' = if Cons? [42] then Cons?.hd [42] else 0 -- old result
let _ = assert_by_tactic (c1' == 42) trefl // this used to fail

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

let f'' (x:list int) : int = if Cons? x then Cons?.hd x else 0
let c1'' : int = (synth (fun()-> constant (`( f'' (Cons 42 Nil) ))))
// c1'' = 42
let _ = assert_by_tactic (c1'' == 42) trefl
