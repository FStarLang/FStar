(*
   Copyright 2008-2024 Nikhil Swamy and Microsoft Research

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

module FStar.TypeChecker.Quals

open FStar
open FStar.Compiler
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
  
(*
Checking qualifiers **and attributes**. This is split in two functions,
_pre and _post, as some qualifier/attributes must be checked before the function
is typechecked (or at least it's better/faster to do so) and some can only be checked
after the function is typechecked.

Currently, the only thing that must be checked after the function is typechecked
is the "erasable" attribute, which can only be checked when the body of the definition
is fully elaborated. See #3252.
*)

val check_sigelt_quals_pre  : env -> sigelt -> unit
val check_sigelt_quals_post : env -> sigelt -> unit
