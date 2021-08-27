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

(** Sugar *)


let forall_elim
       (#a:Type)
       (#p:a -> Type)
       (v:a)
       (f:squash (forall (x:a). p x))
  : Tot (squash (p v))
  = ()

let bind_squash_exists #t #p #q s_ex_p f
  = let open FStar.Squash in
    bind_squash s_ex_p (fun ex_p ->
    bind_squash ex_p (fun (sig_p: (x:t & p x)) ->
    let (| x, px |) = sig_p in
    f x (return_squash px)))

let or_elim
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
    | Left p ->
      f (return_squash p)
    | Right q ->
      g (return_squash q)))

let and_elim
        (p:Type)
        (q:Type)
        (r:Type)
        (x:squash (p /\ q))
        (f:squash p -> squash q -> Tot (squash r))
  : Tot (squash r)
  = let open FStar.Squash in
    bind_squash x (fun p_and_q ->
    bind_squash p_and_q (fun (And p q) ->
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

let exists_intro
        (a:Type)
        (p:a -> Type)
        (v:a)
        (x: squash (p v))
  : Tot (squash (exists x. p x))
  = let open FStar.Squash in
    let p : (v:a & squash (p v)) = (| v, x |) in
    squash_double_sum (return_squash p)

let implies_intro
        (p:Type)
        (q:Type)
        (f:squash p -> Tot (squash q))
  : Tot (squash (p ==> q))
  = let open FStar.Squash in
    let f' (x:p)
      : GTot (squash q)
      = f (return_squash x)
    in
    return_squash (squash_double_arrow (return_squash f'))

let or_intro_left
        (p:Type)
        (q:Type)
        (f:squash p)
  : Tot (squash (p \/ q))
  = ()

let or_intro_right
        (p:Type)
        (q:Type)
        (f:squash q)
  : Tot (squash (p \/ q))
  = ()

let and_intro
        (p:Type)
        (q:Type)
        (f:squash p)
        (g:squash q)
  : Tot (squash (p /\ q))
  = ()
