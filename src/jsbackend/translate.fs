(*
   Copyright 2014 Antoine Delignat-Lavaud and Microsoft Research

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

module Microsoft.FStar.Backends.JS.Translate

open Microsoft.FStar.Backends.JS.Ast

open System
open System.Text

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Range
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util

open FSharp.Format

let js_of_fstar (m:modul) : source_t =
    JS_Statement(JSS_If(JSE_Bool(true),JSS_Debugger,Some(JSS_Empty)))

let js_of_fstars (fmods : list<modul>) : Ast.t =
    let fmods = List.map js_of_fstar fmods in fmods



