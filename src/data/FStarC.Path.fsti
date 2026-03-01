(*
   Copyright 2008-2017 Microsoft Research

   Authors: Aseem Rastogi, Nikhil Swamy, Jonathan Protzenko

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
module FStarC.Path

open FStarC.Class.Deq

type path a = list a

type forest (a:Type) (qual:Type) =
  list (path a & qual) & qual

val is_under {| deq 'a |} (p1 p2 : path 'a) : bool

val search_forest #a #q {| deq a |} (p:path a) (f : forest a q) : q
