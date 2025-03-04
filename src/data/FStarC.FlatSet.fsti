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

module FStarC.FlatSet

open FStarC.Class.Ord
open FStarC.Class.Show
open FStarC.Class.Setlike
include FStarC.Class.Setlike

val flat_set (a:Type0) : Type0
type t = flat_set

instance
val showable_set (a:Type) (_ : ord a) (_ : showable a) : Tot (showable (flat_set a))

instance
val setlike_flat_set (a:Type0) (_ : ord a) : Tot (setlike a (flat_set a))
