(*
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
module FStar.ToSyntax.Interleave
open FStar.ST
open FStar.All
open FStar.Ident
open FStar.Parser.AST
open FStar.ToSyntax.Env
val initialize_interface:        lident -> list<decl> -> Env.withenv<unit>
val prefix_with_interface_decls: decl -> Env.withenv<(list<decl>)>
val interleave_module:           modul -> bool -> Env.withenv<modul>