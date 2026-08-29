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
module FStar.Real.Dedekind.Sup

/// Completeness of the Dedekind reals.
///
/// The least upper bound of a nonempty, bounded-above family of cuts is simply
/// its *union*. That this union is again a cut is what makes the construction
/// worth the trouble, and it is the single property that separates the reals
/// from the rationals --- and hence the property that gives us square roots.

module Q = FStar.Rational
module B = FStar.Real.Dedekind.Base

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

let cset = B.cut -> prop

let cupper (s:cset) (b:B.cut) : prop = forall (x:B.cut). s x ==> B.cle x b
let cbounded (s:cset) : prop = exists (b:B.cut). cupper s b
let cnonempty (s:cset) : prop = exists (x:B.cut). s x

let unionp (s:cset) (q:Q.rat) : prop = exists (x:B.cut). s x /\ x q

let union_ne (s:cset)
  : Lemma (requires cnonempty s) (ensures exists (q:Q.rat). unionp s q)
  = eliminate exists (x:B.cut). s x
    with begin
      let a = B.cut_mem x in
      introduce exists (x2:B.cut). s x2 /\ x2 a with x and ();
      introduce exists (q:Q.rat). unionp s q with a and ()
    end

let union_nf (s:cset)
  : Lemma (requires cbounded s) (ensures exists (q:Q.rat). ~(unionp s q))
  = eliminate exists (b:B.cut). cupper s b
    with begin
      let t = B.cut_nonmem b in
      introduce unionp s t ==> False
      with eliminate exists (x:B.cut). s x /\ x t with ();
      introduce exists (q:Q.rat). ~(unionp s q) with t and ()
    end

let union_dc (s:cset)
  : Lemma (forall (u v:Q.rat). (unionp s v /\ Q.lt u v) ==> unionp s u)
  = introduce forall (u v:Q.rat). (unionp s v /\ Q.lt u v) ==> unionp s u
    with introduce _ ==> _ with
      eliminate exists (x:B.cut). s x /\ x v
      with begin
        B.cut_down x u v;
        introduce exists (x2:B.cut). s x2 /\ x2 u with x and ()
      end

let union_op (s:cset)
  : Lemma (forall (u:Q.rat). unionp s u ==>
                        (exists (v:Q.rat). unionp s v /\ Q.lt u v))
  = introduce forall (u:Q.rat). unionp s u ==>
                           (exists (v:Q.rat). unionp s v /\ Q.lt u v)
    with introduce _ ==> _ with
      eliminate exists (x:B.cut). s x /\ x u
      with begin
        let v = B.cut_above x u in
        introduce exists (x2:B.cut). s x2 /\ x2 v with x and ();
        introduce exists (v2:Q.rat). unionp s v2 /\ Q.lt u v2 with v and ()
      end

#push-options "--z3rlimit 200"
let csup (s:cset)
  : Pure B.cut
      (requires cnonempty s /\ cbounded s)
      (ensures fun c -> forall (q:Q.rat). c q <==> unionp s q)
  = union_ne s; union_nf s; union_dc s; union_op s;
    B.mk_cut (unionp s)
#pop-options

/// [csup s] is an upper bound ...
let csup_upper (s:cset)
  : Lemma (requires cnonempty s /\ cbounded s) (ensures cupper s (csup s))
  = introduce forall (x:B.cut). s x ==> B.cle x (csup s)
    with introduce _ ==> _ with
      introduce forall (q:Q.rat). x q ==> csup s q
      with introduce _ ==> _ with
        introduce exists (x2:B.cut). s x2 /\ x2 q with x and ()

/// ... and it is the least one.
let csup_least (s:cset) (c:B.cut)
  : Lemma (requires cnonempty s /\ cbounded s /\ cupper s c)
          (ensures B.cle (csup s) c)
  = introduce forall (q:Q.rat). csup s q ==> c q
    with introduce _ ==> _ with
      eliminate exists (x:B.cut). s x /\ x q with ()
