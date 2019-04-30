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

open FStar.Algebra.Monoid
open FStar.Array
open FStar.Axiomatic.Array
open FStar.BaseTypes
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
open FStar.Int31
open FStar.Int32
open FStar.Int63
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
open FStar.Reader
open FStar.Reflection

open FStar.Tactics
open FStar.List

// This query will go the SMT, in the default proof namespace
let f (x:int) = assert (x + 1 == 1 + x)

// This one should be sent in a pruned context
let _ = assert_by_tactic (rev [1;2] == [2;1])
                         (fun () -> prune "";
                                    addns "FStar.List";
                                    addns "Prims")

// Both should go to the SMT, also in pruned context
let _ = assert_by_tactic (rev [1;2] == [2;1] /\ (forall x. x + 1 == 1 + x))
                         (fun () ->
                            prune "";
                            FStar.Tactics.split ();
                            (* rev [1;2] == [2;1] *)
                                addns "FStar.List";
                                addns "Prims";
                                smt ();
                            (* 1 == 1 *)
                                addns "Prims";
                                smt ())

let _ = assert_by_tactic (rev [1;2] == [2;1] /\ (forall x. x + 1 == 1 + x))
                         (fun () ->
                            FStar.Tactics.split ();
                            (* rev [1;2] == [2;1] *)
                                prune "";
                                addns "FStar.List";
                                addns "Prims";
                                smt ();
                            (* 1 == 1 *)
                                prune "";
                                addns "Prims";
                                smt ())

[@expect_failure]
let _ = assert_by_tactic (rev [1;2] == [2;1] /\ (forall x. x + 1 == 1 + x))
                         (fun () ->
                            prune "";
                            FStar.Tactics.split ();
                            (* rev [1;2] == [2;1] *)
                                addns "Prims";
                                smt ();
                            (* 1 == 1 *)
                                addns "Prims";
                                smt ())

[@expect_failure]
let _ = assert_by_tactic (rev [1;2] == [2;1] /\ (forall x. x + 1 == 1 + x))
                         (fun () ->
                            prune "";
                            FStar.Tactics.split ();
                            (* rev [1;2] == [2;1] *)
                                addns "FStar.List";
                                smt ();
                            (* 1 == 1 *)
                                addns "Prims";
                                smt ())

[@expect_failure]
let _ = assert_by_tactic (rev [1;2] == [2;1] /\ (forall x. x + 1 == 1 + x))
                         (fun () ->
                            prune "";
                            FStar.Tactics.split ();
                            (* rev [1;2] == [2;1] *)
                                addns "FStar.List";
                                addns "Prims";
                                smt ();
                            (* 1 == 1 *)
                                smt ())
