module CherryLiftMatch
module U32 = FStar.UInt32

(* A local function whose type is a match, as in bug-reports/closed/Bug1714:
   [t true] is [arrow int p], which the local's type does not show, so it is
   not lambda-lifted, which would take the result type from the type. *)
let arrow (a b:Type) = a -> b

type p = | Print : string -> p

let rec t (b:bool) : Type0 =
  match b with
  | false -> p
  | true -> arrow int p

let run (f:t true) : p = (f <: arrow int p) 3

let main () : U32.t =
  let f : t true = fun src -> Print (if src = 3 then "mov" else "bad") in
  match run f with
  | Print x -> if x = "mov" then 0ul else 1ul
