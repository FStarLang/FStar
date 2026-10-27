module Pulse.Lib.LogicalAtomicity.Update
#lang-pulse

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks

val wand (before after:inames) (p q:slprop) : slprop

let fupd (before after:inames) (p:slprop) = wand before after emp p

ghost fn intro_wand (before after:inames) (p q extra:slprop)
  (k:unit -> M.gaction unit before after (extra ** p) (fun _ -> q))
  requires extra
  ensures wand before after p q

val elim_wand (before after:inames) (p q:slprop)
  : M.gaction unit before after (wand before after p q ** p) (fun _ -> q)

ghost fn return_update (mask:inames) (p:slprop)
  requires p
  ensures fupd mask mask p

val elim_update (before after:inames) (p:slprop)
  : M.gaction unit before after (fupd before after p) (fun _ -> p)

ghost fn compose (m1 m2 m3:inames) (p q r:slprop)
  requires wand m1 m2 p q ** wand m2 m3 q r
  ensures wand m1 m3 p r

ghost fn frame (m1 m2:inames) (p q r:slprop)
  requires wand m1 m2 p q
  ensures wand m1 m2 (p ** r) (q ** r)

ghost fn map (m1 m2:inames) (p q:slprop)
  (k:unit -> stt_ghost unit emp_inames p (fun _ -> q))
  requires fupd m1 m2 p
  ensures fupd m1 m2 q
