module Bug397

(* removing index also makes this work *)
type t (i:int) =
  | C : int -> t i

(* this works *)
let dummy2 (i:int) (s:t i)  =
  match s with
  | C _ -> 42

(* this fails *)
let dummy (i:int) (s:t i)  =
  match s, i with
  | C _, _ -> 42
