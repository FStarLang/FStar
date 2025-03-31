(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy and Copilot
*)
module FStarC.Parser.AST.Diff

open FStarC.Effect
open FStarC.Parser.AST

(* Check if two decls are equal, ignoring range metadata.
   Used in FStarC.Interactive.Incremental *)
val eq_term (t1 t2:term) : bool
val eq_binder (b1 b2:binder) : bool
val eq_pattern (p1 p2:pattern) : bool
val eq_decl (d1 d2:decl) : bool
