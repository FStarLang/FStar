module SuccessfulProjectorSharing

open FStar.Tactics.V2

(* Successful projections must select constructor argument closures directly.
   Closing the projectee constructor first loses the argument environments and
   memo cells, making this record-update chain quadratic. *)

type state = {
  f00: int; f01: int; f02: int; f03: int;
  f04: int; f05: int; f06: int; f07: int;
  f08: int; f09: int;
}

let initial = {
  f00 = 0; f01 = 1; f02 = 2; f03 = 3;
  f04 = 4; f05 = 5; f06 = 6; f07 = 7;
  f08 = 8; f09 = 9;
}

let step (s: state) : state =
  { s with f00 = s.f00 + s.f01 }

let rec iterate (n: nat) (s: state) : Tot state (decreases n) =
  if n = 0 then s else iterate (n - 1) (step s)

let normalize () =
  norm [primops; iota; delta; zeta; weak];
  trefl ()

[@@postprocess_with normalize]
let result = iterate 1000 initial
