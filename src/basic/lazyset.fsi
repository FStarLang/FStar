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
module Microsoft.FStar.LazySet

type iset<'t> =                                         //invisible
  | Set of list<'t>
  | Delayed of (('t -> 't -> bool) -> list<set<'t>>)
and set<'t> = ref<iset<'t>>                             //abstract --- don't rely on rep


val set_of_thunk: (unit -> set<'a>) -> set<'a>
val set_of_list: list<'a> -> set<'a>
val list_of_set: ('a -> 'a -> bool) -> set<'a> -> list<'a>
val union: set<'a> -> set<'a> -> set<'a>
val intersection: set<'a> -> set<'a> -> set<'a>
val difference: set<'a> -> set<'a> -> set<'a>