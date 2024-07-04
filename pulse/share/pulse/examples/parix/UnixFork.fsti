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
*)

module UnixFork

(* This module assumes an unstructured unix-style fork *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge

new
val thread : Type0

val joinable : thread -> slprop
val done     : thread -> slprop (* i.e. reapable/zombie *)

val fork 
  (#pre #post : slprop)
  (f : unit -> stt unit pre (fun () -> post))
  : stt thread pre (fun th -> joinable th ** pledge emp_inames (done th) post)

val join
  (th : thread)
  : stt unit (joinable th) (fun () -> done th)
