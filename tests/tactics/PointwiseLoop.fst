module PointwiseLoop

open FStar.List
open FStar.Tactics

(* This tactic can unfold recursive functions inside of [match] statements and others... *)
let rec_norm direction (steps : list norm_step) : Tac unit =
  let normalize () = norm steps; trefl () in
  t_pointwise direction normalize

let opt_id_nat (x : nat) : option nat = Some x

(* The function we want to unfold *)
val list_sum : list nat -> nat
let rec list_sum (l:list nat) =
  match l with
  | [] -> 0
  | n :: l' ->
    (* We use [opt_id_nat] so that this match won't get reduced *)
    match opt_id_nat n with
    | None -> 0
    | Some n' ->
      n + (list_sum l')

let eqs = [`%list_sum]

let norm_steps = [iota; zeta; delta_only eqs]

(* This used to loop before e608a222413896ccf9def35a091971ff7cdb2f16 *)
let list_sum_lem () =
  assert(list_sum [1;2;3;4;5] = 15)
    by (rec_norm TopDown norm_steps)
