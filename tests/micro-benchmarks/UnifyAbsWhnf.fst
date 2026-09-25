(*
   Copyright 2008-2026 Microsoft Research

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
module UnifyAbsWhnf

(* Rel decides an equation it cannot solve syntactically by reducing both
   sides to weak head normal form and recursing on the arguments.  Weak head
   reduction stops at a lambda, so an argument that is a lambda has to be
   opened before its body can be compared; otherwise the beta-redex that
   substituting [vws] leaves in [sum_ait]'s body is never reduced, and the
   equation below falls through to the SMT solver, which cannot prove it. *)

noeq type rcd = { len : nat; ait : Type0 }

let natlt (n:nat) = i:nat{i < n}

assume val ok (n:pos) (vws : natlt n -> rcd) : prop

type sum_ait (n:pos) (vws : natlt n -> rcd) = (i : natlt n & (vws i).ait)

let sum (n:pos) (vws : natlt n -> rcd) (#_ : squash (ok n vws)) : rcd =
  { len = 0; ait = sum_ait n vws }

assume val container (st:Type) (a:Type) : Type

noeq type view (st : Type0) = { inner : rcd; ctn : container st inner.ait }

let sum_view
      (#st : Type0)
      (n : pos)
      (vws : natlt n -> view st)
      (#_ : squash (ok n (fun i -> (vws i).inner)))
      (c : container st (x: natlt n & (vws x).inner.ait))
  : view st
  = { inner = sum n (fun i -> (vws i).inner);
      ctn   = c }
