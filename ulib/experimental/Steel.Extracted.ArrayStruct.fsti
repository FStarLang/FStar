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

module Steel.Extracted.ArrayStruct

module AS = Steel.PCM.ArrayStruct
module Mem = Steel.PCM.Memory
module SizeT = Steel.SizeT
module Map = FStar.Map


open FStar.FunctionalExtensionality
module PCM = Steel.PCM
module UPCM = Steel.PCM.Unitless
module UPCMBase = Steel.PCM.Unitless.Base

/// This module defines a mechanism for extracting arraystructs compatible with separation logic
/// into C arraystructs via Kremlin

(* foo is the view of what you're storing *)
type foo =
  | MkFoo : x: UInt32.t -> y: UInt32.t -> z: UInt64.t -> foo

(* low_foo is the low-level representation of [foo] *)
type low_foo = {
  xy: Seq.lseq UInt32.t 2;
  z: UInt64.t
}

val foo_to_low_foo : foo -> low_foo

val low_foo_to_foo : low_foo -> foo

(* The representation of the objects managed by [foo_pcm] in memory is low_foo *)
(* [@@repr [low_foo, foo_to_low_foo, low_foo_to_foo]] *)
val foo_pcm : PCM.pcm foo
(* Suppose the [foo_pcm] mandates that z >= x + y *)

class low_level_type (a: Type u#a) = {
  pcm: PCM.pcm a;
  low_a: Type u#a;
  a_to_low_a: a -> low_a;
  low_a_to_a: low_a -> a
}

instance low_level_foo : low_level_type foo = {
  pcm = foo_pcm;
  low_a = low_foo;
  a_to_low_a = foo_to_low_foo;
  low_a_to_a = low_foo_to_foo;
}

open FStar.Tactics.Typeclasses

(* Raise a GitHub issue for a typeclass syntax withing val signatures *)
val ref (a: Type u#a) (#[tcresolve ()] ca:low_level_type a) : Type u#0

val alloc
  (#a: Type u#a) (#[FStar.Tactics.Typeclasses.tcresolve ()] ca: low_level_type a)
  (v: a) (#[FStar.Tactics.exact (quote (ca.a_to_low_a v))] v_low: ca.low_a)
    : ref a #ca

let main () =
  alloc #foo (MkFoo 0ul 0ul 1UL)

(* You have to give update_z because you have to justify this with regards to [foo_pcm]

  [@@ update low_foo.z] (* What checks for this attribute ?
    - number of arguments: 2
    - first argument is ref to type that has low_level_type typeclass
    - [low_foo] is [low_a] for that typeclass
    - z is a field of low_foo (low_foo has to be a record)
    - postcondition implies that (a_to_low_a (sel h1 r))  == { a_to_low_a (sel h0 r) with z = new_val }
  *)
  val update_z (r: ref foo) (new_val: UInt64.t) : Steel unit (ref r) (fun _ -> ref r) (fun h0 ->
    new_val >= (sel h0 r).x + (sel h0 r).y
  ) (fun h0 _ h1 ->
    (sel h1 r) = MkFoo (sel h0 r).x (sel h0 r).y new_val
  )
*)

(* Language of attributes :
   [@@ update low_struct.field]
   [@@ update low_array.index] and paths thereof
   [@@ read low_struct.field]
   [@@ read low_array.index] and paths thereof
   [@@ address_of low_struct.field]
*)
