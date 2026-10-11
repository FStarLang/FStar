(*
   Copyright 2026 Microsoft Research

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
module FStarC.Target

open FStarC.Effect

(* Compilation targets, see doc/ref/targets.md.  A file [A.B-foo.fst] belongs
   to module [A.B] and target [foo].  A target name starts with a lowercase
   letter and contains only lowercase letters, digits and '_'. *)
val is_target_name : string -> ML bool

(* Split a file stem (a module name, possibly followed by [-target]) into the
   module name and the target. *)
val split_target : string -> ML (string & option string)
