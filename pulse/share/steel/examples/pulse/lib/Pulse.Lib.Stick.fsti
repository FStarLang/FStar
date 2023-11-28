module Pulse.Lib.Stick

open Pulse.Lib.Core
module T = FStar.Tactics

val stick  :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop

let ( @==> ) :
  (#[T.exact (`emp_inames)] is:inames) ->
  (hyp : vprop) ->
  (concl : vprop) ->
  vprop
  = fun #is -> stick #is

val elim_stick
  (#[T.exact (`emp_inames)] is: inames)
  (hyp concl: vprop)
: stt_ghost unit is
    ((stick #is hyp concl) ** hyp)
    (fun _ -> concl)

val intro_stick
  (#[T.exact (`emp_inames)] is : inames)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: unit -> (
    stt_ghost unit is
    (v ** hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit emp_inames
    v
    (fun _ -> stick #is hyp concl)

val stick_sub_inv
  (#os1 : inames)
  (#os2 : inames{inames_subset os1 os2})
  (hyp concl: vprop)
: stt_ghost unit emp_inames
    (stick #os1 hyp concl)
    (fun _ -> stick #os2 hyp concl)
