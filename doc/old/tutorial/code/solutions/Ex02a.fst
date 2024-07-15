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
module Ex02a
//can-read-write-types

type filename = string

val canWrite : filename -> Tot bool
let canWrite (f:filename) =
  match f with 
    | "demo/tempfile" -> true
    | _ -> false

val canRead : filename -> Tot bool
let canRead (f:filename) =
  canWrite f               (* writeable files are also readable *)
  || f="demo/README"       (* and so is this file *)
