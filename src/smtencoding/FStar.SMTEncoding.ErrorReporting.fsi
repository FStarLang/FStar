﻿(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"

module FStar.SMTEncoding.ErrorReporting
open FStar.ST
open FStar.All
open FStar
open FStar.BaseTypes
open FStar.Util
open FStar.SMTEncoding.Term
open FStar.SMTEncoding.Util
open FStar.SMTEncoding
open FStar.Range
module BU = FStar.Util

type label = error_label
type labels = list<label>

val label_goals : option<(unit -> string)> -> range -> q:term -> labels * term

val detail_errors :  bool //detail_hint_replay?
                  -> TypeChecker.Env.env
                  -> labels
                  -> (decls_t -> Z3.z3result)
                  -> unit
