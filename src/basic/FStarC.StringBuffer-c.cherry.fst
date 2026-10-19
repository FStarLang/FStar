(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.StringBuffer

(* The Cherry implementation: a reference to the contents.  [add] empties the
   reference before appending, so that the string is uniquely owned and
   Cherry's [^] extends it in place. *)

open FStarC.Effect

type t = ref string

let create _ = mk_ref ""

let add s t =
  let cur = !t in
  t := "";
  t := cur ^ s;
  t

let contents t = !t

let clear t = t := ""; t

let output_channel ch t = FStarC.Util.fprint ch "%s" [!t]
