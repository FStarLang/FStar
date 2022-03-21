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
module Bug601

type ok (t:Type0) =
    | Good: ok t

assume type tp (t:Type0) : Type0

(* Error: Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Name not found: StrangeTypePredicate.bad *)
type bad (t:Type0{tp t}) =
    | Bad: bad t

(* type pt = t:Type0{tp t} *)
(* type valid (t:pt) = *)
(*     | Valid: valid t *)
