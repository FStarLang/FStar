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
module FStar.Issue

(* The user-facing FStar.Issue module is realized by the compiler's own issue
   type, so that issues can be passed between metaprograms and the compiler
   without conversion. *)

module E = FStarC.Errors.Issue

(* FStar.Range.range is the compiler's range (src/basic/FStar.Range.fst), but
   abstract here. *)
let co_range (#a #b : Type0) (r:option a) : option b =
  FStar.Pervasives.coerce_eq (admit ()) r

type issue = E.issue

let message_of_issue i = i.issue_msg

let level_of_issue i =
  match i.issue_level with
  | E.EInfo -> "Info"
  | E.EWarning -> "Warning"
  | E.EError -> "Error"
  | E.ENotImplemented -> "Feature not yet implemented: "

let number_of_issue i = i.issue_number

let range_of_issue i = co_range i.issue_range

let context_of_issue i = i.issue_ctx

(* Rendering consults the compiler's state (e.g. to refind ranges), so it is
   in the ML effect in the compiler; it is nevertheless deterministic enough
   to be presented as a total function to metaprograms. *)
[@@custard_extern "(fun i -> FStarC_Errors.issue_to_doc' true i)"]
let issue_to_doc _ = admit ()

[@@custard_extern "FStarC_Errors.format_issue"]
let render_issue _ = admit ()

let mk_issue_doc i msg range number ctx =
  { E.issue_level = E.issue_level_of_string i;
    E.issue_msg = msg;
    E.issue_range = co_range range;
    E.issue_number = number;
    E.issue_ctx = ctx }
