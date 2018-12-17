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
open MiniParse.Tac.Impl
open FStar.Tactics

let ps = _ by (gen_package Goal (`palette))

#set-options "--print_implicits --print_universes"

let p = _ by (gen_parser_impl Goal)

let s = _ by (gen_serializer_impl Goal)
