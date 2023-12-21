(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.Stick

open Pulse.Lib.Core
friend Pulse.Lib.Core
open Steel.ST.Util

[@@"__reduce__"; "__steel_reduce__"]
let stick #is = implies_ #is

(* Using this indirection as Steel tactic relies on 'star' instead of ** *)
val __elim_stick
  (#is: inames)
  (hyp concl: vprop)
: stt_ghost unit is
    ((stick #is hyp concl) `star` hyp)
    (fun _ -> concl)

let __elim_stick #is hyp concl =
  fun #opened () -> elim_implies_gen #opened #is hyp concl

let elim_stick #is = __elim_stick #is

(* Using this indirection as Steel tactic relies on 'star' instead of ** *)
val __intro_stick
  (#is : inames)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: unit -> (
    stt_ghost unit is
    (v `star` hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit emp_inames
    v
    (fun _ -> (@==>) #is hyp concl)

let __intro_stick #is hyp concl v f_elim =
  fun #opened () ->
     intro_implies_gen #opened #is hyp concl v
               (fun _ -> f_elim () ())

let intro_stick #is = __intro_stick #is

let stick_sub_inv
  (#os1 : inames)
  (#os2 : inames{inames_subset os1 os2})
  (hyp concl: vprop)
: stt_ghost unit emp_inames
    (stick #os1 hyp concl)
    (fun _ -> stick #os2 hyp concl)
=  intro_stick #os2 hyp concl (stick #os1 hyp concl) (fun () -> elim_stick #os1 hyp concl)

let op_forall_Star (#a:Type) (p:a -> vprop) : vprop = forall_ #a p

let elim_forall #a = admit()
let intro_forall #a = admit()