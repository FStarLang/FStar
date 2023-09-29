module Pulse.Lib.Stick

open Pulse.Lib.Core
friend Pulse.Lib.Core
open Steel.ST.Util

[@@"__reduce__"; "__steel_reduce__"]
let stick #is = implies_ #is

(* Using this indirection as Steel tactic relies on 'star' instead of ** *)
val __elim_stick
  (#opened : inames)
  (#is: inames{opened /! is})
  (hyp concl: vprop)
: stt_ghost unit opened
    ((stick #is hyp concl) `star` hyp)
    (fun _ -> concl)

let __elim_stick #opened #is hyp concl =
  fun _ -> elim_implies #opened #is hyp concl

let elim_stick #opened #is = __elim_stick #opened #is

(* Using this indirection as Steel tactic relies on 'star' instead of ** *)
val __intro_stick
  (#opens: inames)
  (#is : inames)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: (
    (opens': inames{opens' /! is}) ->
    stt_ghost unit opens'
    (v `star` hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit opens
    v
    (fun _ -> (@==>) #is hyp concl)

let __intro_stick #opens #is hyp concl v f_elim =
  fun _ -> intro_implies #opens #is hyp concl v
               (fun opens' -> f_elim opens' ())

let intro_stick #opened #is = __intro_stick #opened #is
