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
module FStar.Stubs.Tactics.Result

// This file is never extracted. It's a copy of the one with the same name in
// the compiler.  It lives here so that one doesn't need to adjust their load
// path to use tactics from ulib.

open FStar.Stubs.Tactics.Types

noeq type __result a =
    | Success : v:a -> ps:proofstate -> __result a
    | Failed  : exn:exn         (* Error *)
              -> ps:proofstate  (* The proofstate at time of failure *)
              -> __result a
