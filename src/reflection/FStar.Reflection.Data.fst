(*
   Copyright 2008-2022 Microsoft Research

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
module FStar.Reflection.Data

(* NOTE: This file is exactly the same as its .fs/.fsi counterpart.
It is only here so the equally-named interface file in ulib/ is not
taken by the dependency analysis to be the interface of the .fs. We also
cannot ditch the .fs, since out bootstrapping process does not extract
any .ml file from an interface. Hence we keep both, exactly equal to
each other. *)
open FStar.Compiler.List
open FStar.Syntax.Syntax
module Ident = FStar.Ident
module Range = FStar.Compiler.Range
module Z     = FStar.BigInt
open FStar.Ident

(* These two functions are in ulib/FStar.Reflection.Data.fsti
   But, they are not extracted from there.

   Instead, these functions are extraction from this file. It is 
   not sufficient to place these functions in the interface
   src/reflection/FStar.Reflection.Data.fsti since this module, like the 
   rest of the compiler, is extracted in MLish mode. Which means that
   functions in the interface are not supported for extraction. So, 
   we include them in this module implementation file to force them
   to be extracted *)
let as_ppname (x:string) : Tot string = x

let notAscription (tv:term_view) : Tot bool =
  not (Tv_AscribedT? tv) && not (Tv_AscribedC? tv)
