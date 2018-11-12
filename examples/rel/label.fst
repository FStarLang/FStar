module Label


(* CH: Everything specialized to 2-point lattice *)
type label =
| Low
| High

val op_Less : label -> label -> Tot bool
let op_Less l1 l2 =
  match l1, l2 with
  | Low,High -> true
  | _, _ -> false

val op_Less_Equals : label -> label -> Tot bool
let op_Less_Equals l1 l2 =
  match l1, l2 with
  | High,Low -> false
  | _, _ -> true

val join : label -> label -> Tot label
let join l1 l2 =
  match l1, l2 with
  | Low,Low -> Low
  | _, _ -> High

val meet : label -> label -> Tot label
let meet l1 l2 =
  match l1, l2 with
  | High, High -> High
  | _, _ -> Low

let universal_property_meet l l1 l2
  : Lemma (requires (l <= l1 /\ l <= l2)) (ensures (l <= meet l1 l2))
= ()
