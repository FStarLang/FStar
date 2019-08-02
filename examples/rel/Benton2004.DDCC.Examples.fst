(*
   Copyright 2008-2018 Microsoft Research

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
module Benton2004.DDCC.Examples
open Benton2004.DDCC

#reset-options "--z3rlimit 128"

let op_abs_singl
  (#from #to: Type0)
  (op: (from -> from -> Tot to))
  (c1 c2: from)
: Lemma
  (op_abs op (ns_singl c1) (ns_singl c2) (ns_singl (op c1 c2)))
= ()

let d_op_singl
  (#from #to: Type0)
  (op: (from -> from -> Tot to))
  (c1 c2: from)
  (e1 e1' e2 e2': exp from)
  (phi: sttype)
: Lemma
  (requires (
    eval_equiv phi (ns_singl c1) e1 e1' /\
    eval_equiv phi (ns_singl c2) e2 e2'
  ))
  (ensures (eval_equiv phi (ns_singl (op c1 c2)) (eop op e1 e2) (eop op e1' e2')))
  [SMTPat  (eval_equiv phi (ns_singl (op c1 c2)) (eop op e1 e2) (eop op e1' e2'))]
= op_abs_singl op c1 c2 ;
  d_op op e1 e1' e2 e2' (ns_singl c1) (ns_singl c2) (ns_singl (op c1 c2)) phi

let fig3_d1
  (x: var)
  (phi: sttype)
: Lemma
  (requires (
    x `st_fresh_in` phi
  ))
  (ensures (
    x `st_fresh_in` phi /\
    exec_equiv
      (st_cons phi x (ns_singl 3))
      (st_cons phi x (ns_singl 7))
      (ifthenelse (eop op_Equality (evar x) (const 3)) (assign x (const 7)) skip)
      (assign x (const 7))
  ))
= d_op_singl (op_Equality #int) 3 3 (evar x) (evar x) (const 3) (const 3) (st_cons phi x (ns_singl 3))
  // the rest is automatically inferred through patterns

let fig3_d2
  (x: var)
  (phi: sttype)
  (z: var)
: Lemma
  (requires (
    x `st_fresh_in` phi /\
    z `st_fresh_in` phi /\
    x <> z
  ))
  (ensures (
    x `st_fresh_in` phi /\
    z `st_fresh_in` phi /\
    x <> z /\
    exec_equiv
      (st_cons (st_cons phi x (ns_singl 7)) z ns_t)
      (st_cons (st_cons phi x ns_t) z (ns_singl 8))
      (assign z (eop op_Addition (evar x) (const 1)))
      (assign z (const 8))
  ))
= d_op_singl op_Addition 7 1 (evar x) (evar x) (const 1) (const 1) (st_cons phi x (ns_singl 7));
  assert (
    exec_equiv
      (st_cons (st_cons phi x (ns_singl 7)) z ns_t)
      (st_cons (st_cons phi x (ns_singl 7)) z (ns_singl 8))
      (assign z (eop op_Addition (evar x) (const 1)))
      (assign z (const 8))  
  )

let fig3_d3
  (x: var)
  (phi: sttype)
  (z: var)
: Lemma
  (requires (
    x `st_fresh_in` phi /\
    z `st_fresh_in` phi /\
    x <> z
  ))
  (ensures (
    x `st_fresh_in` phi /\
    z `st_fresh_in` phi /\
    x <> z /\
    exec_equiv
      (st_cons (st_cons phi x (ns_singl 3)) z ns_t)
      (st_cons (st_cons phi x ns_t) z (ns_singl 8))
      (seq (assign x (const 7)) (assign z (const 8)))
      (assign z (const 8))
  ))
= let c = assign x (const 7) in
  let c' = assign z (const 8) in
  let c'' = c' in
  let phi_ = st_cons (st_cons phi x (ns_singl 3)) z ns_t in
  let phi' = st_cons (st_cons phi x ns_t) z ns_t in
  let phi'' = st_cons (st_cons phi x ns_t) z (ns_singl 8) in
  d_das x (const 7) (st_cons phi z ns_t) (ns_singl 3);
  d_assign (st_cons phi x ns_t) z ns_t (ns_singl 8) (const 8) (const 8);
  d_su1' c c' c'' phi_ phi' phi'' // FIXME: WHY WHY WHY does the pattern on d_su1'' NOT trigger?

let fig3
  (x: var)
  (phi: sttype)
  (z: var)
: Lemma
  (requires (
    x `st_fresh_in` phi /\
    z `st_fresh_in` phi /\
    x <> z
  ))
  (ensures (
    x `st_fresh_in` phi /\
    z `st_fresh_in` phi /\
    x <> z /\
    exec_equiv
      (st_cons (st_cons phi x (ns_singl 3)) z ns_t)
      (st_cons (st_cons phi x ns_t) z (ns_singl 8))
      (seq (ifthenelse (eop op_Equality (evar x) (const 3)) (assign x (const 7)) skip) (assign z (eop op_Addition (evar x) (const 1))))
      (assign z (const 8))
  ))
= fig3_d1 x (st_cons phi z ns_t);
  d_csub // this step is IMPLICIT, BENTON DID NOT MENTION IT IN THE PROOF TREE
    (st_cons (st_cons phi z ns_t) x (ns_singl 3))
    (st_cons (st_cons phi z ns_t) x (ns_singl 7))
    (st_cons (st_cons phi x (ns_singl 3)) z ns_t)
    (st_cons (st_cons phi x (ns_singl 7)) z ns_t)
    (ifthenelse (eop op_Equality (evar x) (const 3)) (assign x (const 7)) skip)
    (assign x (const 7));
  fig3_d2 x phi z;
  fig3_d3 x phi z
