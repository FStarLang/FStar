(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR C  ONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Parser.Const.Tuples

open FStarC
open FStarC.Effect
open FStarC.Ident
open FStarC.Range

(* Non-dependent tuples *)

(* tycon *)
val mk_tuple_lid (arity : int) (r : range) : lid
(* datacon *)
val mk_tuple_data_lid (arity : int) (r : range) : lid

val get_tuple_datacon_arity (s:string) : option int
val get_tuple_tycon_arity (s:string) : option int

val is_tuple_constructor_lid (lid : lident) : bool
val is_tuple_data_lid (f : lident) (n : int) : bool
val is_tuple_datacon_lid (f : lident) : bool

(* Dependent tuples *)

(* tycon *)
val mk_dtuple_lid (arity : int) (r : range) : lid
(* datacon *)
val mk_dtuple_data_lid (arity : int) (r : range) : lid

val get_dtuple_datacon_arity (s:string) : option int
val get_dtuple_tycon_arity (s:string) : option int

val is_dtuple_constructor_lid (lid : lident) : bool
val is_dtuple_data_lid (f : lident) (n : int) : bool
val is_dtuple_datacon_lid (f : lident) : bool

(* Shortcuts *)
val lid_tuple2   : lident
val lid_tuple3   : lident
val lid_tuple4   : lident
val lid_tuple5   : lident
val lid_Mktuple2 : lident
val lid_Mktuple3 : lident
val lid_Mktuple4 : lident
val lid_Mktuple5 : lident
val lid_dtuple2  : lident
