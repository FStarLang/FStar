module Bug279

(* type t = *)
(*   | T : ts -> t *)
(* and ts = list t *)

let rec f (x:t) = match x with
  | T ts -> g ts
and g (y:ts) = ()

(* this works, i.e., removing the annotation on x *)
(*let rec f x = match x with
  | T ts -> g ts
and g (y:ts) = ()*)
