module Phase2CoreReturnsAtPattern

(* As in TcTerm, each branch of a match with a returns annotation is expected
   to have the annotation at its pattern, rather than at the scrutinee: here
   [as_type (A n)], which reduces, without fuel, to [nat]. *)

noeq type t =
  | A : nat -> t
  | P : i:Type0 -> (i -> t) -> t

let rec as_type (x:t) : Type0 =
  match x with
  | A _ -> nat
  | P i k -> (y:i & as_type (k y))

noeq type box (a:Type0) = | Box : (unit -> a) -> box a

#push-options "--fuel 0"
let default (x:t) : Tot (box (as_type x)) =
  match x returns Tot (box (as_type x)) with
  | A n -> Box (fun _ -> n)
  | P i k -> Box (fun _ -> admit ())
#pop-options
