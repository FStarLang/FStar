(*
   Copyright 2008-2018 Microsoft Research

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
[@@"no_prelude"]
module FStar.Pervasives.Native

(* This is a file from the core library, dependencies must be explicit *)
open Prims
include FStar.Tuple2

/// This module is implicitly opened in the scope of all other modules.
///
/// It provides several basic types in F* that enjoy some special
/// status in extraction. For instance, the tuple type below is
/// compiled to OCaml's tuple type, rather than to a F*-defined
/// inductive type. See ulib/ml/FStar_Pervasives_Native.ml
///

(** [option a] represents either  [Some a]-value or a non-informative [None]. *)
type option (a: Type) =
  | None : option a
  | Some : v: a -> option a

(**** Tuples *)

/// Aside from special support in extraction, the tuple types have
/// special syntax in F*.
///
/// For instance, rather than [tupleN a1 ... aN],
/// we usually write [a1 & ... & aN] or [a1 * ... * aN].
///
/// The latter notation is more common for those coming to F* from
/// OCaml or F#. However, the [*] also clashes with the multiplication
/// operator on integers define in FStar.Mul. For this reason, we now
/// prefer to use the [&] notation, though there are still many uses
/// of [*] remaining.
///
/// Tuple values are introduced using as [a1, ..., an], rather than
/// [MktupleN a1 ... aN].
///
/// They are found in the modules FStar.TupleN and FStar.DTupleN, for
/// the relevant values of N. The only odd case is dtuple2 which is
/// defined in Prims, as it is needed for the definition of l_Exists.

let fst x = FStar.Tuple2.Mk?._1 x
let snd x = FStar.Tuple2.Mk?._2 x
