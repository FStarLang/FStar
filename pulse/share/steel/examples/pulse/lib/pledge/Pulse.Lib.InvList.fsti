module Pulse.Lib.InvList

open Pulse.Lib.Pervasives

let invlist0 = list (p:vprop & inv p)

let rec invlist_names (is : invlist0) : inames =
  match is with
  | [] -> emp_inames
  | i :: is -> add_iname (invlist_names is) (name_of_inv <| dsnd i)

let rec invlist_nodups (is : invlist0) : prop =
  match is with
  | [] -> True
  | i :: is -> not (mem_inv (invlist_names is) (dsnd i)) /\ invlist_nodups is

let invlist =
  i:invlist0{invlist_nodups i}

let rec invlist_v (is : invlist) : vprop =
  match is with
  | [] -> emp
  | i :: is -> dfst i ** invlist_v is

val shift_invlist_one
  (#a:Type0)
  (p : vprop)
  (i : inv p)
  (is : invlist{not (mem_inv (invlist_names is) i)})
  (#pre:vprop)
  (#post : a -> vprop)
  (f : unit -> stt_unobservable a emp_inames (invlist_v ((| p, i |) :: is) ** pre) (fun v -> invlist_v ((| p, i |) :: is) ** post v)) :
       unit -> stt_unobservable a emp_inames (invlist_v is ** (p ** pre)) (fun v -> invlist_v is ** (p ** post v))

val with_invlist (#a:Type0) (#pre : vprop) (#post : a -> vprop)
  (is : invlist)
  (f : unit -> stt_unobservable a emp_inames (invlist_v is ** pre) (fun v -> invlist_v is ** post v))
  : stt_unobservable a (invlist_names is) pre (fun v -> post v)
