(*
   Copyright 2025 Microsoft Research

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

(** Read-only arrays with static storage duration, whose contents are known at
    compile time.

    A [static_array t] is a table baked into the program image rather than
    built at run time.  In C it is

      static const t name[n] = { ... };

    so it costs no startup code and the linker can put it in [.rodata]; in
    OCaml it is a [t array], and in Rust it is a [&[t]].

    Custard's whole-program extraction gives this a compile-time meaning: the
    element list handed to {!mk_static_array} has to reduce to a literal, and
    the elements become the C initializer directly.  Nothing about it survives
    to run time --- there is no allocation, no initialization pass and no
    [custard_init_globals] entry.

    Three properties are being axiomatized, and each one is doing work:

    - [static_array t] has no decidable equality --- it is [assume val] and so
      carries no [hasEq] --- which is what makes {!mk_static_array} safe as a
      *pure* function.  Two syntactically distinct calls may or may not be the
      same object in the image, and no F* program can ask.

    - {!array_of_static_array} yields only *fractional* permission, so the
      array can be read and never written.  That is what licenses the [const]
      in the emitted C, and it is the reason the pointer conversion Custard
      emits at this call is sound rather than a hole.

    - The conversion is [stt_atomic ... #Neutral], not a pure coercion,
      because in C it is the point at which a [const t *] becomes a [t *].
      Making it a computation keeps that step visible in the extracted code
      instead of letting it be duplicated or sunk into a spec.

    See section 71 of [doc/ref/custard.md]. *)
module Pulse.Lib.GlobalArray
#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module Seq = FStar.Seq

(** A run of [t]s fixed at compile time.

    [assume val] rather than [assume new type] because the type is
    parameterized, and deliberately without decidable equality: see the
    module comment. *)
assume val static_array ([@@@strictly_positive] t : Type0) : Type0

(** The contents.  Ghost: the whole point of the type is that the elements
    live in the program image and not in any F* value. *)
assume val static_array_elems (#t : Type0) (a : static_array t)
  : GTot (Seq.seq t)

(** Build one.  Pure, which is sound because {!static_array} has no equality,
    and total, because there is nothing to allocate.

    [l] has to reduce to a literal list for Custard to extract this; a
    [static_array] whose contents are not known at compile time is a
    contradiction in terms, and Custard reports one (error 393) rather than
    building the table at startup behind your back. *)
assume val mk_static_array (#t : Type0) (l : list t)
  : a : static_array t { static_array_elems a == Seq.seq_of_list l }

(** View it as an ordinary Pulse array.

    The post-condition gives an *existential fraction*, never full
    permission, so the result can be read and never written.  There is no
    matching release: the permission is on an object with static storage
    duration, which outlives every caller, so there is nothing to give
    back. *)
assume val array_of_static_array (#t : Type0) (a : static_array t)
  : stt_atomic (A.array t) #Neutral emp_inames
      emp
      (fun a' -> exists* (p : perm). pts_to a' #p (static_array_elems a))
