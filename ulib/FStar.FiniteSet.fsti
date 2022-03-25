(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: John Li, N. Swamy
*)
module FStar.FiniteSet

val set (a:eqtype)
  : Type0

val set_as_list (#a:eqtype) (s: set a)
  : GTot (list a)

val mem (#a:eqtype) (x:a) (s:set a)
  : bool

val emptyset (#a:eqtype)
  : set a

val insert (#a:eqtype) (x:a) (s: set a)
  : set a

val remove (#a:eqtype) (x:a) (s: set a)
  : set a

val insert_remove (#a:eqtype) (x:a) (s: set a)
  : Lemma
    (requires mem x s)
    (ensures insert x (remove x s) == s)
    [SMTPat (insert x (remove x s))]

val remove_insert (#a:eqtype) (x:a) (s: set a)
  : Lemma
    (requires mem x s == false)
    (ensures remove x (insert x s) == s)
    [SMTPat (remove x (insert x s))]

let notin (#a:eqtype) (x:a) (s: set a)
  : bool
  = not (mem x s)
