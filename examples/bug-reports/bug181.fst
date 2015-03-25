module Bug181

(* These work *)
type t1 (t:Type) = t
type t2 (a:Type) ('p:a->Type) = a

(* This doesn't work *)
type t2' (a:Type) (p:a->Type) = a
