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
module FStarC.Custard.PrintC

open FStarC.Effect
open FStarC.Custard.Syntax

(** The whole program as one self-contained C11 translation unit (section 6,
    M8): a header and a source, in that order.  The argument is the stem of
    the output file, which the source includes and the include guard is
    derived from.

    Only the [Root] declarations appear in the header; everything else is
    [static] (section 24). *)
val print_program : string -> program -> ML (string & string)
