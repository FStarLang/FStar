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
module FStar.Tactics.V2.Bare

include FStar.Stubs.Reflection.Types
include FStar.Reflection.V2
include FStar.Reflection.V2.Formula

include FStar.Stubs.Tactics.Types
include FStar.Tactics.Effect
include FStar.Stubs.Tactics.V2.Builtins
include FStar.Tactics.V2.Derived
include FStar.Tactics.V2.SyntaxHelpers
include FStar.Tactics.V2.Logic
include FStar.Tactics.V2.SyntaxCoercions
include FStar.Tactics.Util
include FStar.Tactics.Print
include FStar.Tactics.Visit
include FStar.Tactics.NamedView
include FStar.Tactics.SMT

include FStar.Reflection.TermEq.Simple
