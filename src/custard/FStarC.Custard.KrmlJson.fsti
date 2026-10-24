(*
   Copyright 2008-2025 Microsoft Research

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

(** The [.krml] file format: the JSON encoding that karamel's [InputAst]
    derives with [ppx_deriving_yojson].  karamel matches constructors by
    name, so the names written here are karamel's, which differ from
    {!FStarC.Custard.KrmlAst}'s in a few places (e.g. [ETypApp] is
    [ETApp]). *)
module FStarC.Custard.KrmlJson

open FStarC.Effect
module K = FStarC.Custard.KrmlAst

val write_file : string -> K.binary_format -> ML unit

(** [None] if the file is not JSON or does not decode as a [.krml]. *)
val read_file : string -> ML (option K.binary_format)
