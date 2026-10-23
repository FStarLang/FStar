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
module FStarC.Errors.Issue

(* The type of issues, included by FStarC.Errors.  It lives in its own module,
   below the typeclass/reflection layer, so that FStar.Issue (which the
   reflection stubs depend on) can be implemented by it without creating a
   dependency cycle. *)

type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError

type issue = {
    issue_msg: list FStar.Pprint.document;
    issue_level: issue_level;
    issue_range: option FStarC.Range.Type.range;
    issue_number: option int;
    issue_ctx: list string;
}

let string_of_issue_level (il : issue_level) : string =
  match il with
  | EInfo -> "Info"
  | EWarning -> "Warning"
  | EError -> "Error"
  | ENotImplemented -> "Feature not yet implemented: "

let issue_level_of_string (s : string) : issue_level =
  match s with
  | "Info" -> EInfo
  | "Warning" -> EWarning
  | "Error" -> EError
  | _ -> ENotImplemented
