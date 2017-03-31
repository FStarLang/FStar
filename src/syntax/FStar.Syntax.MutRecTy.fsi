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
#light "off"
// (c) Microsoft Corporation. All rights reserved
module FStar.Syntax.MutRecTy
open FStar.All
open FStar.Syntax.Syntax
open FStar.Ident

val disentangle_abbrevs_from_bundle: list<sigelt> -> list<qualifier> -> list<lident> ->
                                     FStar.Range.range -> option<fsdoc> -> sigelt * list<sigelt>
