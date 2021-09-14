(*
   Copyright 2008-2021 Jay Lorch, Rustan Leino, Alex Summers, Dan
   Rosen, Microsoft Research, and contributors to the Dafny Project

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Includes material from the Dafny project
   (https://github.com/dafny-lang/dafny) which carries this license
   information:

     Created 9 February 2008 by Rustan Leino.
     Converted to Boogie 2 on 28 June 2008.
     Edited sequence axioms 20 October 2009 by Alex Summers.
     Modified 2014 by Dan Rosen.
     Copyright (c) 2008-2014, Microsoft.
     Copyright by the contributors to the Dafny Project
     SPDX-License-Identifier: MIT
*)

(**
This module declares a type and functions used for modeling
sequences as they're modeled in Dafny.

@summary Type and functions for modeling sequences
*)
module Util.Seq.Defs

open FStar.List.Tot

type seq (ty: Type) = list ty

/// We represent the Dafny function `Seq#Length` with `seq_length`:
///
/// function Seq#Length<T>(Seq T): int;

[@"opaque_to_smt"]
let seq_length = length

let reveal_seq_length (ty: Type) : Lemma (seq_length #ty == length #ty) =
  reveal_opaque #(#ty: Type -> seq ty -> int) (`%seq_length) seq_length

/// We represent the Dafny function `Seq#Empty` with `seq_empty`:
/// 
/// function Seq#Empty<T>(): Seq T;

[@"opaque_to_smt"]
let seq_empty (ty: Type) : seq ty = []

let reveal_seq_empty (ty: Type) : Lemma (seq_empty ty == []) =
  reveal_opaque #(ty: Type -> seq ty) (`%seq_empty) seq_empty

/// We represent the Dafny function `Seq#Singleton` with `seq_singleton`:
///
/// function Seq#Singleton<T>(T): Seq T;

let seq_singleton_hidden (#ty: Type) (v: ty) : seq ty =
  [v]

[@"opaque_to_smt"]
let seq_singleton = seq_singleton_hidden

let reveal_seq_singleton (ty: Type) : Lemma (seq_singleton #ty == seq_singleton_hidden #ty) =
  reveal_opaque #(#ty: Type -> ty -> seq ty) (`%seq_singleton) seq_singleton

/// We represent the Dafny function `Seq#Index` with `seq_index`:
///
/// function Seq#Index<T>(Seq T, int): T;

let seq_index_hidden (#ty: Type) (s: seq ty) (i: nat{i < seq_length s}) : ty =
  reveal_seq_length ty;
  index s i

[@"opaque_to_smt"]
let seq_index = seq_index_hidden

let reveal_seq_index (ty: Type) : Lemma (seq_index #ty == seq_index_hidden #ty) =
  reveal_opaque #(#ty: Type -> s: seq ty -> i: nat{i < seq_length s} -> ty) (`%seq_index) seq_index

/// We represent the Dafny function `Seq#Build` with `seq_build`:
/// 
/// function Seq#Build<T>(s: Seq T, val: T): Seq T;

let seq_build_hidden (#ty: Type) (s: seq ty) (v: ty) : seq ty =
  append s [v]

[@"opaque_to_smt"]
let seq_build = seq_build_hidden

let reveal_seq_build (ty: Type) : Lemma (seq_build #ty == seq_build_hidden #ty) =
  reveal_opaque #(#ty: Type -> seq ty -> ty -> seq ty) (`%seq_build) seq_build

/// We represent the Dafny function `Seq#Append` with `seq_append`:
///
/// function Seq#Append<T>(Seq T, Seq T): Seq T;

[@"opaque_to_smt"]
let seq_append = append

let reveal_seq_append (ty: Type) : Lemma (seq_append #ty == append #ty) =
  reveal_opaque #(#ty: Type -> seq ty -> seq ty -> seq ty) (`%seq_append) seq_append

/// We represent the Dafny function `Seq#Update` with `seq_update`:
///
/// function Seq#Update<T>(Seq T, int, T): Seq T;

let seq_update_fn (#ty: Type) (s: list ty) (i: nat{i < length s}) (v: ty) : list ty =
  let s1, _, s2 = split3 s i in
  append s1 (append [v] s2)

let seq_update_hidden (#ty: Type) (s: seq ty) (i: nat{i < seq_length s}) (v: ty) : list ty =
  reveal_seq_length ty;
  let s1, _, s2 = split3 s i in
  append s1 (append [v] s2)

[@"opaque_to_smt"]
let seq_update = seq_update_hidden

let reveal_seq_update (ty: Type) : Lemma (seq_update #ty == seq_update_hidden #ty) =
  reveal_opaque #(#ty: Type -> s: seq ty -> i: nat{i < seq_length s} -> ty -> seq ty) (`%seq_update) seq_update

/// We represent the Dafny function `Seq#Contains` with `seq_contains`:
///
/// function Seq#Contains<T>(Seq T, T): bool;

let seq_contains_hidden (#ty: Type) (s: seq ty) (v: ty) : Type0 =
  memP v s

[@"opaque_to_smt"]
let seq_contains = seq_contains_hidden

let reveal_seq_contains (ty: Type) : Lemma (seq_contains #ty == seq_contains_hidden #ty) =
  reveal_opaque #(#ty: Type -> seq ty -> ty -> Type0) (`%seq_contains) seq_contains

/// We represent the Dafny function `Seq#Take` with `seq_take`:
///
/// function Seq#Take<T>(s: Seq T, howMany: int): Seq T;

let seq_take_fn (#ty: Type) (s: list ty) (howMany: nat{howMany <= length s}) : seq ty =
  let result, _ = splitAt howMany s in
  result

let seq_take_hidden (#ty: Type) (s: seq ty) (howMany: nat{howMany <= seq_length s}) : seq ty =
  reveal_seq_length ty;
  seq_take_fn s howMany

[@"opaque_to_smt"]
let seq_take = seq_take_hidden

let reveal_seq_take (ty: Type) : Lemma (seq_take #ty == seq_take_hidden #ty) =
  reveal_opaque #(#ty: Type -> s: seq ty -> howMany: nat{howMany <= seq_length s} -> seq ty) (`%seq_take) seq_take

/// We represent the Dafny function `Seq#Drop` with `seq_drop`:
///
/// function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;

let seq_drop_fn (#ty: Type) (s: list ty) (howMany: nat{howMany <= length s}) : seq ty =
  let _, result = splitAt howMany s in
  result

let seq_drop_hidden (#ty: Type) (s: seq ty) (howMany: nat{howMany <= seq_length s}) : seq ty =
  reveal_seq_length ty;
  seq_drop_fn s howMany

[@"opaque_to_smt"]
let seq_drop = seq_drop_hidden

let reveal_seq_drop (ty: Type) : Lemma (seq_drop #ty == seq_drop_hidden #ty) =
  reveal_opaque #(#ty: Type -> s: seq ty -> howMany: nat{howMany <= seq_length s} -> seq ty) (`%seq_drop) seq_drop

/// We represent the Dafny function `Seq#Equal` with `seq_equal`.
///
/// function Seq#Equal<T>(Seq T, Seq T): bool;

let seq_equal_hidden (#ty: Type) (s0: seq ty) (s1: seq ty) : Type0 =
  seq_length s0 == seq_length s1 /\
    (forall j.{:pattern seq_index s0 j \/ seq_index s1 j}
      0 <= j && j < seq_length s0 ==> seq_index s0 j == seq_index s1 j)

[@"opaque_to_smt"]
let seq_equal = seq_equal_hidden

let reveal_seq_equal (ty: Type) : Lemma (seq_equal #ty == seq_equal_hidden #ty) =
  reveal_opaque #(#ty: Type -> seq ty -> seq ty -> Type0) (`%seq_equal) seq_equal

/// Instead of representing the Dafny function `Seq#SameUntil`, which
/// is only ever used in Dafny to represent prefix relations, we
/// instead use `seq_is_prefix`.
///
/// function Seq#SameUntil<T>(Seq T, Seq T, int): bool;

let seq_is_prefix_hidden (#ty: Type) (s0: seq ty) (s1: seq ty) : Type0 =
    seq_length s0 <= seq_length s1
  /\ (forall (j: nat).{:pattern seq_index s0 j \/ seq_index s1 j}
     j < seq_length s0 ==> seq_index s0 j == seq_index s1 j)

let seq_is_prefix = seq_is_prefix_hidden

let reveal_seq_is_prefix (ty: Type) : Lemma (seq_is_prefix #ty == seq_is_prefix_hidden #ty) =
  reveal_opaque #(#ty: Type -> seq ty -> seq ty -> Type0) (`%seq_is_prefix) seq_is_prefix

/// We represent the Dafny function `Seq#Rank` with `seq_rank`.
///
/// function Seq#Rank<T>(Seq T): int;

let seq_rank_hidden (#ty: Type) (v: ty) = v

[@"opaque_to_smt"]
let seq_rank = seq_rank_hidden

let reveal_seq_rank (ty: Type) : Lemma (seq_rank #ty == seq_rank_hidden #ty) =
  reveal_opaque #(#ty: Type -> ty -> ty) (`%seq_rank) seq_rank
