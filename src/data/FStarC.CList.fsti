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

(* Catenable lists, based on Jaskelioff and Rivas' "Functional Pearl: A Smart View on Datatypes" *)
module FStarC.CList

open FStarC.Class.Deq
open FStarC.Class.Ord
open FStarC.Class.Show
open FStarC.Class.Monoid
open FStarC.Class.Listlike

new
val clist (a:Type0) : Type0

type t = clist

instance val listlike_clist (a:Type0) : Tot (listlike a (t a))
instance val monoid_clist (a:Type0) : Tot (monoid (t a))
instance val showable_clist (a:Type0) (_ : showable a) : Tot (showable (t a))
instance val eq_clist (a:Type0) (_ : deq a) : Tot (deq (t a))
instance val ord_clist (a:Type0) (_ : ord a) : Tot (ord (t a))

val map (#a #b : Type0) (f : a -> b) (l : clist a) : clist b

val existsb (#a : Type0) (p : a -> bool) (l : clist a) : bool

val for_all (#a : Type0) (p : a -> bool) (l : clist a) : bool

val partition (#a : Type0) (p : a -> bool) (l : clist a) : clist a * clist a

val collect : ('a -> clist 'b) -> clist 'a -> clist 'b
