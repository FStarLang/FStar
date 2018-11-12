module Bug181

(* This works *)
type t1 (t:Type) = t

(* This doesn't work -- now it does *)
type t2' (a:Type) (p:a->Type) = a
