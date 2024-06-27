module Pulse.Lib.ConditionVarWithCodes
open Pulse.Lib.Pervasives
//open Pulse.Lib.Codeable

noeq
type code : Type u#4 = {
  t    : Type u#2;
  emp  : t;
  up   : t -> boxable;
  laws : squash ( up emp == Pulse.Lib.Pervasives.emp )
}

class codeable (code:code) (v:vprop) = {
  c : code.t;
  laws : squash (code.up c == v)
}

val cvar_t (c:code) : Type0

val inv_name #c (cv:cvar_t c) : iref

val send #c (cv:cvar_t c) (p:vprop) : vprop

val recv #c (cv:cvar_t c) (p:vprop) : vprop

val create #c (p:vprop) (pf: codeable c p)
: stt (cvar_t c) emp (fun b -> send b p ** recv b p)

val signal #c (cv:cvar_t c) (#p:vprop)
: stt unit (send cv p ** p) (fun _ -> emp)

val wait #c (cv:cvar_t c) (#p:vprop)
: stt unit (recv cv p) (fun _ -> p)

val split #c (cv:cvar_t c) (#p #q:vprop) (cq:codeable c p) (cr:codeable c q)
: stt_ghost unit (add_inv emp_inames (inv_name cv))
  (recv cv (p ** q)) (fun _ -> recv cv p ** recv cv q)



val cvinv #c (cv:cvar_t c) (p:vprop) : vprop

val dup_cvinv #c (cv:cvar_t c) (#p:vprop)
: stt_ghost unit emp_inames (cvinv cv p) (fun _ -> cvinv cv p ** cvinv cv p)

val send_core #c (cv:cvar_t c) : boxable

val decompose_send #c (cv:cvar_t c) (p:vprop)
: stt_ghost unit emp_inames (send cv p) (fun _ -> cvinv cv p ** send_core cv)

val recompose_send #c (cv:cvar_t c) (p:vprop)
: stt_ghost unit emp_inames (cvinv cv p ** send_core cv) (fun _ -> send cv p)

val recv_core #c (cv:cvar_t c) (q:vprop)
: boxable

val decompose_recv #c (cv:cvar_t c) (p:vprop)
: stt_ghost unit emp_inames 
  (recv cv p) (fun _ ->  (exists* q. cvinv cv q) ** recv_core cv p)
  
val recompose_recv #c (cv:cvar_t c) (p:vprop) (#q:_)
: stt_ghost unit emp_inames
  (cvinv cv q ** recv_core cv p) (fun _ -> recv cv p)