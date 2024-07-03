(*
   Copyright 2024 Microsoft Research

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

module Pulse.Lib.InvList

open Pulse.Lib.Pervasives

let invlist_elem = vprop & iname
let invlist0 = list invlist_elem

let rec invlist_names (is : invlist0) : inames =
  match is with
  | [] -> emp_inames
  | i :: is -> add_inv (invlist_names is) (snd i)

let rec invlist_nodups (is : invlist0) : prop =
  match is with
  | [] -> True
  | i :: is -> not (mem_inv (invlist_names is) (snd i)) /\ invlist_nodups is

let invlist =
  i:invlist0{invlist_nodups i}

let invlist_empty : invlist = []

let add_one (h : invlist_elem) (t : invlist{not (mem_inv (invlist_names t) (snd h))}) : invlist =
  h :: t

let rec invlist_v (is : invlist) : vprop =
  match is with
  | [] -> emp
  | i :: is -> fst i ** invlist_v is

let rec invlist_inv (is:invlist) : vprop =
  match is with
  | [] -> emp
  | i :: is -> inv (snd i) (fst i) ** invlist_inv is

val dup_invlist_inv (is:invlist)
  : stt_ghost unit emp_inames
      (requires invlist_inv is)
      (ensures fun _ -> invlist_inv is ** invlist_inv is)

val shift_invlist_one
  (#a:Type0)
  (p : vprop)
  (i : iname)
  (is : invlist{not (mem_inv (invlist_names is) i)})
  (#pre:vprop)
  (#post : a -> vprop)
  (f : unit -> stt_ghost a emp_inames (invlist_v (( p, i ) :: is) ** pre) (fun v -> invlist_v (( p, i ) :: is) ** post v))
  
  : unit -> stt_ghost a emp_inames (invlist_v is ** (p ** pre)) (fun v -> invlist_v is ** (p ** post v))

val with_invlist (#a:Type0) (#pre : vprop) (#post : a -> vprop)
  (is : invlist)
  (f : unit -> stt_ghost a emp_inames (invlist_v is ** pre) (fun v -> invlist_v is ** post v))
  : stt_ghost a (invlist_names is) (invlist_inv is ** pre) (fun v -> invlist_inv is ** post v)

(* A helper for a ghost-unit function. *)
// val with_invlist_ghost (#pre : vprop) (#post : vprop)
//   (is : invlist)
//   (f : unit -> stt_ghost unit (invlist_v is ** pre) (fun _ -> invlist_v is ** post))
//   : stt_atomic unit #Unobservable (invlist_names is) pre (fun _ -> post)

// TODO: change to just subset so invlist_sub_split is implementable in Ghost.
// In unobservable, we should be able to prove that the names being a subset
// is enough for the invlists to be a sublist.
let invlist_sub (is1 is2 : invlist) : prop =
  inames_subset (invlist_names is1) (invlist_names is2)

(* FIXME: invlist should be made erasable. But, that would not allow us
to inspect in ghost. Maybe we can have a `uerased` type constructor to represent
values that can be revealed in unobservable, and which are also erased at runtime.
Currently, this here is an axiom, and we would be constructing these
lists at runtime. *)
val invlist_reveal (is : erased invlist) : (is':invlist{reveal is == is'})

val invlist_sub_split (is1 is2 : invlist) :
  stt_ghost unit emp_inames
    (pure (invlist_sub is1 is2) ** invlist_v is2)
    (fun _ -> invlist_v is1 ** Pulse.Lib.Priv.Trade0.stick (invlist_v is1) (invlist_v is2))

val invlist_sub_inv (is1 is2:invlist)
  : stt_ghost unit emp_inames
      (invlist_inv is2 ** pure (invlist_sub is1 is2))
      (fun _ -> invlist_inv is1 ** Pulse.Lib.Priv.Trade0.stick (invlist_inv is1) (invlist_inv is2))
