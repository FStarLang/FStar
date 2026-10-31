module Phase2CoreLetRecTail

(* The expected type of a local [let rec] is related to the type of its body,
   rather than to the whole term, which the SMT encoding treats opaquely. *)

type t = | A of nat | B of t

let wrap (x:t) : y:t{B? y} =
  let rec go (x:t) : t =
    match x with
    | A n -> A (n + 1)
    | B x -> go x
  in
  let r = go x in
  B r
