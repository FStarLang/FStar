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
module Pruning

(* Pollute our namespace *)
open FStar.Algebra.Monoid
open FStar.Array
open FStar.Axiomatic.Array
open FStar.BitVector
open FStar.Bytes
open FStar.Char
open FStar.Classical
open FStar.Constructive
open FStar.Crypto
open FStar.DependentMap
open FStar.ErasedLogic
open FStar.Fin
open FStar.Float
open FStar.FunctionalExtensionality
open FStar.Ghost
open FStar.Heap
open FStar.IndefiniteDescription
open FStar.Int
open FStar.Int128
open FStar.Int16
open FStar.Int32
open FStar.Int64
open FStar.Int8
open FStar.Int.Cast
open FStar.Integers
open FStar.IO
open FStar.List
open FStar.List.Tot
open FStar.List.Tot.Base
open FStar.List.Tot.Properties
open FStar.Map
open FStar.MarkovsPrinciple
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Matrix2
open FStar.MRef
open FStar.Mul
open FStar.Option
open FStar.Order
open FStar.OrdMap
open FStar.OrdMapProps
open FStar.OrdSet
open FStar.OrdSetProps
open FStar.PredicateExtensionality
open FStar.PropositionalExtensionality
open FStar.Reflection.V2
open FStar.Seq
open FStar.Seq.Base
open FStar.Seq.Properties
open FStar.Set
open FStar.Squash
open FStar.SquashProperties
open FStar.ST
open FStar.String
open FStar.StrongExcludedMiddle
open FStar.Tactics.V2
open FStar.Tcp
open FStar.TSet
open FStar.All
open FStar.IO
open FStar.Option
open FStar.ST
open FStar.UInt
open FStar.UInt128
open FStar.UInt16
open FStar.UInt32
open FStar.UInt64
open FStar.UInt8
open FStar.Universe
open FStar.Util
open FStar.WellFounded
open Prims

(* Clear most of it before SMT encoding *)
#reset-options "--using_facts_from FStar.Seq --using_facts_from Prims"

let lemma (#a:Type) (s_0:Seq.seq a) (s_1:Seq.seq a{Seq.length s_0 `Prims.op_LessThanOrEqual` Seq.length s_1})
    : Lemma (requires (Seq.equal s_0 (Seq.slice s_1 0 (Seq.length s_0))))
            (ensures  (Seq.equal s_1 (Seq.append s_0 (Seq.slice s_1 (Seq.length s_0) (Seq.length s_1)))))
    = ()
