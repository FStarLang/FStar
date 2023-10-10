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
  (#opens: inames)
  (#[T.exact (`emp_inames)] is: inames { Set.disjoint opens is })
  (hyp concl: vprop)
: stt_ghost unit opens
    ((stick #is hyp concl) ** hyp)
    (fun _ -> concl)

val intro_stick
  (#opens: inames)
  (#[T.exact (`emp_inames)] is : inames)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: (
    (opens': inames{opens' /! is}) ->
    stt_ghost unit opens'
    (v ** hyp)
    (fun _ -> concl)
  ))
: stt_ghost unit opens
    v
    (fun _ -> stick #is hyp concl)
