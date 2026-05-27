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

let forall_elim
       (#a:Type)
       (#p:a -> prop)
       (v:a)
       (f:squash (forall (x:a). p x))
  : Tot (squash (p v))
  = ()

let exists_elim #t #p #q s_ex_p f =
  Classical.exists_elim q s_ex_p fun x -> f x ()

let or_elim_simple
        (p:prop)
        (q:prop)
        (r:prop)
        (x:squash (p \/ q))
        (f:squash p -> Tot (squash r))
        (g:squash q -> Tot (squash r))
  : Tot (squash r)
  = Classical.or_elim #p #q #(fun _ -> r) (fun _ -> f ()) (fun _ -> g ())

let or_elim
        (p:prop)
        (q:squash (~p) -> prop)
        (r:prop)
        (p_or:squash (p \/ q()))
        (left:squash p -> Tot (squash r))
        (right:squash (~p) -> squash (q()) -> Tot (squash r))
  : Tot (squash r)
  = or_elim_simple p (~p) r ()
            (fun (s:squash p) -> left s)
            (fun (np:squash (~p)) ->
              or_elim_simple p (q ()) r p_or
                (fun (pf_p:squash p) -> left pf_p)
                (fun (pf_q:squash (q())) -> right np pf_q))

let and_elim (p:prop)
             (q:squash p -> prop)
             (r:prop)
             (x:squash (p /\ q()))
             (f:squash p -> squash (q()) -> Tot (squash r))
  : Tot (squash r)
  = f () ()

let forall_intro
      (a:Type)
      (p:a -> prop)
      (f: (x:a -> Tot (squash (p x))))
  : Tot (squash (forall x. p x))
  = let f (x: a) : Lemma (p x) = f x in
  Classical.forall_intro #a #p f

let exists_intro_simple
        (a:Type)
        (p:a -> prop)
        (v:a)
        (f: squash (p v))
  : Tot (squash (exists x. p x))
  = ()

let exists_intro
        (a:Type)
        (p:a -> prop)
        (v:a)
        (f: unit -> Tot (squash (p v)))
  : Tot (squash (exists x. p x))
  = exists_intro_simple a p v (f())


let implies_intro
        (p:prop)
        (q:squash p -> prop)
        (f:(squash p -> Tot (squash (q()))))
  : Tot (squash (p ==> q()))
  = Classical.impl_intro_gen #p #q fun _ -> f ()

let or_intro_left
        (p:prop)
        (q:squash (~p) -> prop)
        (f:unit -> Tot (squash p))
  : Tot (squash (p \/ q()))
  = f()

let or_intro_right
        (p:prop)
        (q:squash (~p) -> prop)
        (f:squash (~p) -> Tot (squash (q())))
  : Tot (squash (p \/ q()))
  = or_elim_simple p (~p)
                  (p \/ q())
                  ()
                  (fun s_p -> or_intro_left p q (fun _ -> s_p))
                  (fun s_np -> f s_np)

let and_intro
        (p:prop)
        (q:squash p -> prop)
        (f:unit -> Tot (squash p))
        (g:squash p -> Tot (squash (q())))
  : Tot (squash (p /\ q()))
  = let _ = f() in g()
