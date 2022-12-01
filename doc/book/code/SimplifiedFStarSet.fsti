(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi,
                       Microsoft Research, University of Maryland

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

//SNIPPET_START: module$
module SimplifiedFStarSet
(** Computational sets (on eqtypes): membership is a boolean function *)
#set-options "--fuel 0 --ifuel 0"
//SNIPPET_END: module$

//SNIPPET_START: set$
val set (a:eqtype)
  : Type0
//SNIPPET_END: set$

//SNIPPET_START: destructor$
val mem (#a:eqtype) (x:a) (s:set a)
  : bool
//SNIPPET_END: destructor$

//SNIPPET_START: constructors$
val empty (#a:eqtype)
  : set a

val singleton (#a:eqtype) (x:a)
  : set a

val union (#a:eqtype) (s0 s1: set a)
  : set a
  
val intersect (#a:eqtype) (s0 s1: set a)
  : set a
  
val complement (#a:eqtype) (s0:set a)
  : set a
//SNIPPET_END: constructors$

//SNIPPET_START: equal$
val equal (#a:eqtype) (s0 s1:set a)
  : prop
//SNIPPET_END: equal$

//SNIPPET_START: core_properties$
val mem_empty (#a:eqtype) (x:a)
  : Lemma
    (ensures (not (mem x empty)))
    [SMTPat (mem x empty)]

val mem_singleton (#a:eqtype) (x y:a)
  : Lemma
    (ensures (mem y (singleton x) == (x=y)))
    [SMTPat (mem y (singleton x))]

val mem_union (#a:eqtype) (x:a) (s1 s2:set a)
  : Lemma
    (ensures (mem x (union s1 s2) == (mem x s1 || mem x s2)))
    [SMTPat (mem x (union s1 s2))]

val mem_intersect (#a:eqtype) (x:a) (s1:set a) (s2:set a)
  : Lemma
    (ensures (mem x (intersect s1 s2) == (mem x s1 && mem x s2)))
    [SMTPat (mem x (intersect s1 s2))]

val mem_complement (#a:eqtype) (x:a) (s:set a)
  : Lemma
    (ensures (mem x (complement s) == not (mem x s)))
    [SMTPat (mem x (complement s))]
//SNIPPET_END: core_properties$


//SNIPPET_START: equal_intro_elim$
val equal_intro (#a:eqtype) (s1 s2: set a)
  : Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (equal s1 s2))
    [SMTPat (equal s1 s2)]

val equal_elim (#a:eqtype) (s1 s2:set a)
  : Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPat (equal s1 s2)]
//SNIPPET_END: equal_intro_elim$
