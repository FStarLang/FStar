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
       (f:(forall (x:a). p x))
  : Tot (p v)
  = ()

let exists_elim #t #p #q s_ex_p f =
  Classical.exists_elim q s_ex_p fun x -> f x ()

let or_elim_simple
        (p:prop)
        (q:prop)
        (r:prop)
        (x:(p \/ q))
        (f:p -> Tot r)
        (g:q -> Tot r)
  : Tot r
  = Classical.or_elim #p #q #(fun _ -> r) (fun _ -> f ()) (fun _ -> g ())

let or_elim
        (p:prop)
        (q:(~p) -> prop)
        (r:prop)
        (p_or:(p \/ q()))
        (left:p -> Tot r)
        (right:(~p) -> q() -> Tot r)
  : Tot r
  = or_elim_simple p (~p) r ()
            (fun (s:p) -> left s)
            (fun (np:(~p)) ->
              or_elim_simple p (q ()) r p_or
                (fun (pf_p:p) -> left pf_p)
                (fun (pf_q:q()) -> right np pf_q))

let and_elim (p:prop)
             (q:p -> prop)
             (r:prop)
             (x:(p /\ q()))
             (f:p -> q() -> Tot r)
  : Tot r
  = f () ()

let forall_intro
      (a:Type)
      (p:a -> prop)
      (f: (x:a -> Tot (p x)))
  : Tot (forall x. p x)
  = let f (x: a) : Lemma (p x) = f x in
  Classical.forall_intro #a #p f

let exists_intro_simple
        (a:Type)
        (p:a -> prop)
        (v:a)
        (f:p v)
  : Tot (exists x. p x)
  = ()

let exists_intro
        (a:Type)
        (p:a -> prop)
        (v:a)
        (f: unit -> Tot (p v))
  : Tot (exists x. p x)
  = exists_intro_simple a p v (f())


let implies_intro
        (p:prop)
        (q:p -> prop)
        (f:(p -> Tot (q())))
  : Tot (p ==> q())
  = Classical.impl_intro_gen #p #q fun _ -> f ()

let or_intro_left
        (p:prop)
        (q:(~p) -> prop)
        (f:unit -> Tot p)
  : Tot (p \/ q())
  = f()

let or_intro_right
        (p:prop)
        (q:(~p) -> prop)
        (f:(~p) -> Tot (q()))
  : Tot (p \/ q())
  = or_elim_simple p (~p)
                  (p \/ q())
                  ()
                  (fun s_p -> or_intro_left p q (fun _ -> s_p))
                  (fun s_np -> f s_np)

let and_intro
        (p:prop)
        (q:p -> prop)
        (f:unit -> Tot p)
        (g:p -> Tot (q()))
  : Tot (p /\ q())
  = let _ = f() in g()
