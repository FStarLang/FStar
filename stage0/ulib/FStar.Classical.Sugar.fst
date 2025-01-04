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
       (#p:a -> Type)
       (v:a)
       (f:squash (forall (x:a). p x))
  : Tot (squash (p v))
  = ()

let exists_elim #t #p #q s_ex_p f
  = let open FStar.Squash in
    bind_squash s_ex_p (fun ex_p ->
    bind_squash ex_p (fun (sig_p: (x:t & p x)) ->
    let (| x, px |) = sig_p in
    f x (return_squash px)))

let or_elim_simple
        (p:Type)
        (q:Type)
        (r:Type)
        (x:squash (p \/ q))
        (f:squash p -> Tot (squash r))
        (g:squash q -> Tot (squash r))
  : Tot (squash r)
  = let open FStar.Squash in
    bind_squash x (fun p_or_q ->
    bind_squash p_or_q (fun p_cor_q ->
    match p_cor_q with
    | Prims.Left p ->
      f (return_squash p)
    | Prims.Right q ->
      g (return_squash q)))

let or_elim
        (p:Type)
        (q:squash (~p) -> Type)
        (r:Type)
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

let and_elim (p:Type)
             (q:squash p -> Type)
             (r:Type)
             (x:squash (p /\ q()))
             (f:squash p -> squash (q()) -> Tot (squash r))
  : Tot (squash r)
  = let open FStar.Squash in
    bind_squash x (fun p_and_q ->
    bind_squash p_and_q (fun (Prims.Pair p q) ->
    f (return_squash p) (return_squash q)))

let forall_intro
      (a:Type)
      (p:a -> Type)
      (f: (x:a -> Tot (squash (p x))))
  : Tot (squash (forall x. p x))
  = let open FStar.Squash in
    let f' (x:a)
      : GTot (squash (p x))
      = f x
    in
    return_squash (squash_double_arrow (return_squash f'))

let exists_intro_simple
        (a:Type)
        (p:a -> Type)
        (v:a)
        (f: squash (p v))
  : Tot (squash (exists x. p x))
  = let open FStar.Squash in
    let p = (| v, f |) in
    squash_double_sum (return_squash p)

let exists_intro
        (a:Type)
        (p:a -> Type)
        (v:a)
        (f: unit -> Tot (squash (p v)))
  : Tot (squash (exists x. p x))
  = exists_intro_simple a p v (f())


let implies_intro
        (p:Type)
        (q:squash p -> Type)
        (f:(squash p -> Tot (squash (q()))))
  : Tot (squash (p ==> q()))
  = let open FStar.Squash in
    let f' (x:p)
      : GTot (squash (q ()))
      = f (return_squash x)
    in
    return_squash (squash_double_arrow (return_squash f'))

let or_intro_left
        (p:Type)
        (q:squash (~p) -> Type)
        (f:unit -> Tot (squash p))
  : Tot (squash (p \/ q()))
  = f()

let or_intro_right
        (p:Type)
        (q:squash (~p) -> Type)
        (f:squash (~p) -> Tot (squash (q())))
  : Tot (squash (p \/ q()))
  = or_elim_simple p (~p)
                  (p \/ q())
                  ()
                  (fun s_p -> or_intro_left p q (fun _ -> s_p))
                  (fun s_np -> f s_np)

let and_intro
        (p:Type)
        (q:squash p -> Type)
        (f:unit -> Tot (squash p))
        (g:squash p -> Tot (squash (q())))
  : Tot (squash (p /\ q()))
  = let _ = f() in g()
