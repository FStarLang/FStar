(*
   Copyright 2020 Microsoft Research

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

module Steel.Extracted

module AS = Steel.PCM.ArrayStruct
module Mem = Steel.PCM.Memory
module SizeT = Steel.SizeT
module Map = FStar.Map


open FStar.FunctionalExtensionality
module PCM = Steel.PCM
module UPCM = Steel.PCM.Unitless
module UPCMBase = Steel.PCM.Unitless.Base

/// Abstraction boundary for Steel programs. Every function here gets a special treatment in Kremlin
/// and is extracted to a C primitive.


(*** Types stored in memory *)


(**** Type declaration *)

(** The memory cells only contain instances of [mem_typ] *)
val mem_typ : Type u#(a+1)

(**
   You can store any higher-universe type in the memory, but also need to provide a PCM to describe
   the rules for how it can be shared between threads.
*)
val to_mem_typ (a: Type u#a) (pcm: UPCM.unitless_pcm a) : mem_typ u#a

(** [ghost_mem_typ a pcm] will store [Ghost.erased a] into memory, it will not be extracted *)
val ghost_mem_typ (a: Type u#a)  (pcm: UPCM.unitless_pcm (Ghost.erased a)) : mem_typ u#a

(** If [t] is extracted to [tau] in C, then [mem_array t len] will be extracted to [*tau] *)
val mem_array (t: mem_typ u#a) (len: SizeT.t) : mem_typ u#a

(**
  Tactic that examines a type to check if it is an inductive type with one constructor and
  all the arguments that have the [mem_typ] type.
*)
let is_mem_typ_record (mem_record: Type u#a) : prop =
  admit()

(**
  Struct extraction uses F* inductive types. In [mem_struct mem_record], [mem_record] should be
  an inductive type with one constructor, all the arguments of which should have the [mem_typ] type.
*)
val mem_struct (mem_record: Type u#a{is_mem_typ_record mem_record}) : mem_typ u#a

(**** Views *)

(** The view of a [mem_typ] is the logical representation of values stored in a reference *)
val mem_typ_view (t: mem_typ u#a) : Type u#a

val base_view (a: Type u#a) (pcm: UPCM.unitless_pcm a)
    : Lemma (mem_typ_view (to_mem_typ a pcm) == a)
    [SMTPat (mem_typ_view (to_mem_typ a pcm))]

val base_view_ghost (a: Type u#a) (pcm: UPCM.unitless_pcm (Ghost.erased a))
    : Lemma (mem_typ_view (ghost_mem_typ a pcm) == Ghost.erased a)
    [SMTPat (mem_typ_view (ghost_mem_typ a pcm))]

val array_view (t: mem_typ u#a) (len: SizeT.t)
    : Lemma (mem_typ_view (mem_array t len) == Seq.lseq (mem_typ_view t) (SizeT.v len))
    [SMTPat (mem_typ_view (mem_array t len))]

(**
  To a [mem_record], we can associate another inductive type [view_record] which has the same
  constructor and number of arguments as [mem_record], but each of the arguments is [mem_typ_view]
  of the original argument. That [view_record] can be used to store the view of the struct.
*)
val is_view_record
  (mem_record: Type u#a{is_mem_typ_record mem_record})
  (view_record: Type u#a)
    : prop

(** Should be implemented by tactic? Not the right signature. *)
let to_view_record
  (mem_record: Type u#a{is_mem_typ_record mem_record})
     : (view_record:Type u#a{is_view_record mem_record view_record}) =
  admit()


val struct_view
  (mem_record: Type u#a{is_mem_typ_record mem_record})
  (view_record:Type u#a{is_view_record mem_record view_record})
    : Lemma (mem_typ_view (mem_struct mem_record) == view_record)
    [SMTPat (mem_typ_view (mem_struct mem_record)); SMTPat (view_record)]

(**** PCMs *)


(**
  To every [mem_typ], we associate an unitless PCM wich is the pointwise conjunction of all the
  PCMs at the leaves of the [mem_typ].
*)
val mem_typ_pcm (t: mem_typ u#a) : UPCM.unitless_pcm u#a (mem_typ_view t)

val base_pcm (a: Type u#a) (pcm: UPCM.unitless_pcm a)
    : Lemma (mem_typ_pcm (to_mem_typ a pcm) == pcm)
    [SMTPat (mem_typ_pcm (to_mem_typ a pcm))]

val base_pcm_ghost (a: Type u#a) (pcm: UPCM.unitless_pcm (Ghost.erased a))
    : Lemma (mem_typ_pcm (ghost_mem_typ a pcm) == pcm)
    [SMTPat (mem_typ_pcm (ghost_mem_typ a pcm))]

val array_pcm (t: mem_typ u#a) (len: SizeT.t)
    : Lemma (mem_typ_pcm (mem_array t len) ==
      AS.pointwise_array_pcm (mem_typ_view t) len (mem_typ_pcm t)
    )
    [SMTPat (mem_typ_pcm (mem_array t len))]

(**
  To a [mem_record], we can associate another inductive type [pcm_record] which has the same
  constructor and number of arguments as [mem_record], but each of the arguments is [mem_typ_pcm]
  of the original argument. That [pcm_record] can be used to store the PCM of the struct.
*)
val is_pcm_record
  (mem_record: Type u#a{is_mem_typ_record mem_record})
  (view_record:Type u#a{is_view_record mem_record view_record})
  (pcm_record: Type u#a)
    : prop

(** Should be implemented by tactic? Not the right signature. *)
let to_pcm_record
  (mem_record: Type u#a{is_mem_typ_record mem_record})
  (view_record:Type u#a{is_view_record mem_record view_record})
     : (pcm_record:Type u#a{is_pcm_record mem_record view_record pcm_record}) =
  admit()

(**
  Use a tactic to derive the PCM for a record by taking the pointwise composition of its fields
*)
let pointwise_struct_pcm
  (mem_record: Type u#a{is_mem_typ_record mem_record})
  (view_record:Type u#a{is_view_record mem_record view_record})
  (pcm_record:Type u#a{is_pcm_record mem_record view_record pcm_record})
    : UPCM.unitless_pcm view_record
  =
  admit()

val struct_pcm
  (mem_record: Type u#a{is_mem_typ_record mem_record})
  (view_record:Type u#a{is_view_record mem_record view_record})
  (pcm_record:Type u#a{is_pcm_record mem_record view_record pcm_record})
    : Lemma (
      struct_view mem_record view_record;
      mem_typ_pcm (mem_struct mem_record) ==
      pointwise_struct_pcm mem_record view_record pcm_record
    )
   [SMTPat (mem_typ_pcm (mem_struct mem_record)); SMTPat view_record; SMTPat pcm_record]

(*** Pointers *)

val reference (t: mem_typ u#a) : Type u#0
