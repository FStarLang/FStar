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
*)

module FStar.Classical.Sugar
/// This module provides a few combinators that are targeted
/// by the desugaring phase of the F* front end


(*** Combinators used by syntactic sugar ***)

val forall_elim
       (#a:Type)
       (#p:a -> Type)
       (v:a)
       (f:squash (forall (x:a). p x))
  : Tot (squash (p v))

val bind_squash_exists
     (#t:Type)
     (#p:t -> Type)
     (#q:Type)
     ($s_ex_p: squash (exists (x:t). p x))
     (f: (x:t -> squash (p x) -> Tot (squash q)))
  : Tot (squash q)

let implies_elim
        (p:Type)
        (q:Type)
        (_:squash (p ==> q))
        (_:squash p)
  : squash q
  = ()

val or_elim
        (p:Type)
        (q:Type)
        (r:Type)
        (_:squash (p \/ q))
        (f:squash p -> Tot (squash r))
        (g:squash q -> Tot (squash r))
  : Tot (squash r)

val and_elim
        (p:Type)
        (q:Type)
        (r:Type)
        (_:squash (p /\ q))
        (f:squash p -> squash q -> Tot (squash r))
  : Tot (squash r)

val forall_intro
      (a:Type)
      (p:a -> Type)
      (f: (x:a -> Tot (squash (p x))))
  : Tot (squash (forall x. p x))

val exists_intro
        (a:Type)
        (p:a -> Type)
        (v:a)
        (x: squash (p v))
  : Tot (squash (exists x. p x))

val implies_intro
        (p:Type)
        (q:Type)
        (f:squash p -> Tot (squash q))
  : Tot (squash (p ==> q))

val or_intro_left
        (p:Type)
        (q:Type)
        (f:squash p)
  : Tot (squash (p \/ q))

val or_intro_right
        (p:Type)
        (q:Type)
        (f:squash q)
  : Tot (squash (p \/ q))

val and_intro
        (p:Type)
        (q:Type)
        (f:squash p)
        (g:squash q)
  : Tot (squash (p /\ q))
