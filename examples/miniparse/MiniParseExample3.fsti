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
module MiniParseExample3
open MiniParse.Tac.Spec
open MiniParse.Impl.Base

module U8 = FStar.UInt8

type color = U8.t // | Red | Blue | Green | Yellow
type palette = nlist 18 (color & U8.t)

noextract
val ps: package palette

val p: parser_impl (package_parser ps)

val s: serializer_impl (package_serializer ps)
