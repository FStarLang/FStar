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
module Benton2004.RHL.Examples
open Benton2004.RHL

(* Section 4.2 *)

let sec42_ex1
  (x y z: var)
: Lemma
  (ensures (
    exec_equiv
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gvar x Right)))
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gvar z Left) (gvar z Right)))
      (assign z (eop op_Addition (evar y) (const 1)))
      (assign z (evar x))
  ))
= r_ass
    z
    z
    (eop op_Addition (evar y) (const 1))
    (evar x)
    (gand (geq (gvar x Left) (gvar x Right)) (geq (gvar z Left) (gvar z Right)))

let sec42_ex2
  (x y: var)
: Lemma
  (requires (x <> y)) // MISSING from the paper!
  (ensures (
    exec_equiv
      (gand (geq (gop op_Addition (gvar y Left) (gconst 1)) (gop op_Addition (gvar y Right) (gconst 1))) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gop op_Addition (gvar y Right) (gconst 1))))
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gvar x Right)))
      (assign x (eop op_Addition (evar y) (const 1)))
      (assign x (eop op_Addition (evar y) (const 1)))
  ))
= r_ass
    x
    x
    (eop op_Addition (evar y) (const 1))
    (eop op_Addition (evar y) (const 1))
    (gand (geq (gvar x Left) (gvar x Right)) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gvar x Right)))

let sec42_ex3
  (y: var)
: Lemma
  (ensures (
    included
      (geq (gvar y Left) (gvar y Right))
      (gand (geq (gop op_Addition (gvar y Left) (gconst 1)) (gop op_Addition (gvar y Right) (gconst 1))) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gop op_Addition (gvar y Right) (gconst 1))))
  ))
= ()

let sec42_ex4
  (x y: var)
: Lemma
  (requires (x <> y))
  (ensures (
    exec_equiv
      (geq (gvar y Left) (gvar y Right))
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gop op_Addition (gvar y Left) (gconst 1)) (gvar x Right)))
      (assign x (eop op_Addition (evar y) (const 1)))
      (assign x (eop op_Addition (evar y) (const 1)))    
  ))
= sec42_ex2 x y;
  sec42_ex3 y
  // r_sub automatically applied

let sec42_ex5
  (x y z: var)
: Lemma
  (requires (x <> y))
  (ensures (
    exec_equiv
      (geq (gvar y Left) (gvar y Right))
      (gand (geq (gvar x Left) (gvar x Right)) (geq (gvar z Left) (gvar z Right)))
      (seq (assign x (eop op_Addition (evar y) (const 1))) (assign z (eop op_Addition (evar y) (const 1))))
      (seq (assign x (eop op_Addition (evar y) (const 1))) (assign z (evar x)))
  ))
= sec42_ex1 x y z;
  sec42_ex4 x y
  // r_seq automatically applied

let sec43_phi
  (i n x y: var)
: GTot (gexp bool)
= gand
    (geq (gvar i Left) (gvar i Right))
    (gand
      (geq (gvar n Left) (gvar n Right))
      (geq (gvar y Left) (gvar y Right))
    )

let sec43_left
  (i n x y: var)
: Tot computation
= while (eop op_LessThan (evar i) (evar n)) (seq
    (assign x (eop op_Addition (evar y) (const 1)))
    (assign i (eop op_Addition (evar i) (evar x)))
  )

let sec43_right
  (i n x y: var)
: Tot computation
= seq
  (assign x (eop op_Addition (evar y) (const 1)))
  (while (eop op_LessThan (evar i) (evar n))
    (assign i (eop op_Addition (evar i) (evar x)))
  )

(* Proof becomes really intractable. Thus let's design some more convenient derived rules. *)

let r_ass
  (x y: var)
  (e e' : exp int)
  (p p': gexp bool)
: Lemma
  (requires (
    included
      p
      (gsubst (gsubst p' x Left (exp_to_gexp e Left)) y Right (exp_to_gexp e' Right))
  ))
  (ensures (exec_equiv
    p
    p'
    (assign x e)
    (assign y e')
  ))
= Benton2004.RHL.r_ass x y e e' p'

let r_dassl
  (x: var)
  (e: exp int)
  (phi phi': gexp bool)
: Lemma
  (requires (
    included phi (gsubst phi' x Left (exp_to_gexp e Left))
  ))
  (ensures (exec_equiv phi phi' (assign x e) skip))
= Benton2004.RHL.r_dassl x e phi'

let flip_flip
  (phi: gexp bool)
: Lemma
  (forall h1 h2. (flip (flip phi)) h1 h2 == phi h1 h2)
  [SMTPat (flip (flip phi))]
= ()

let r_dassr
  (x: var)
  (e: exp int)
  (phi phi' : gexp bool)
: Lemma
  (requires (
    included phi (gsubst phi' x Right (exp_to_gexp e Right))
  ))
  (ensures (exec_equiv phi phi' skip (assign x e)))
= r_dassl x e (flip phi) (flip phi')

let d_su1'_flip
  (c'' c c' : computation)
  (phi phi' phi'' : gexp bool)
: Lemma
  (requires (
    exec_equiv phi phi' skip c /\
    exec_equiv phi' phi'' c'' c' 
  ))
  (ensures (exec_equiv phi phi'' c'' (seq c c')))
  [SMTPatOr [
    [SMTPat (exec_equiv phi phi'' c'' (seq c c')); SMTPat (exec_equiv phi phi' skip c)];
    [SMTPat (exec_equiv phi phi'' c'' (seq c c')); SMTPat (exec_equiv phi' phi'' c'' c')];
    [SMTPat (exec_equiv phi phi' skip c); SMTPat (exec_equiv phi' phi'' c'' c')];
  ]]
= d_su1' c c' c'' (flip phi) (flip phi') (flip phi'')

#set-options "--z3rlimit 40"
let sec43
  (i n x y: var)
  (diffs: squash (List.Tot.noRepeats [i; n; x; y] == true))
: Lemma
  (ensures (
    exec_equiv
      (sec43_phi i n x y)
      (sec43_phi i n x y)
      (sec43_left i n x y)
      (sec43_right i n x y)
  ))
= let phi = sec43_phi i n x y in
  let l = sec43_left i n x y in
  let r = sec43_right i n x y in
  let cond = eop op_LessThan (evar i) (evar n) in
  let asx_e = eop op_Addition (evar y) (const 1) in
  let asx = assign x asx_e in
  let asi_e = eop op_Addition (evar i) (evar x) in
  let asi = assign i asi_e in
  let lbody = seq asx asi in
  let rloop = while cond asi in
  let phi1 = gand phi (geq (gvar x Right) (gop op_Addition (gvar y Right) (gconst 1))) in
  let phi2 = gand phi1 (geq (gvar x Left) (gvar x Right)) in
  assert (x <> i /\ x <> n /\ x <> y); // for the substitutions in phi, phi1
  r_dassr x asx_e phi phi1;
  r_dassl x asx_e phi1 phi2;
  assert (i <> x /\ i <> n /\ i <> y); // for the substitutions in phi2
  r_ass i i asi_e asi_e phi2 phi2;
  d_su1' asx asi asi phi1 phi2 phi2;
  r_while cond cond lbody asi phi1;
  assert (exec_equiv phi1 phi l rloop); // by d_sub
  d_su1'_flip l asx rloop phi phi1 phi
#reset-options

(* Sophisticated dead code *)

let sec43'_postcond
  (x y: var)
: GTot (gexp bool)
= gand
    (gop op_GreaterThan (gvar y Left) (gconst 2))
    (gop op_GreaterThan (gvar y Right) (gconst 2))

let sec43'_precond
  (x y: var)
: GTot (gexp bool)
= gand (geq (gvar x Left) (gvar x Right)) (sec43'_postcond x y)

let sec43'
  (x y: var)
: Lemma
  (ensures (
    exec_equiv
      (sec43'_precond x y)
      (sec43'_postcond x y)
      (ifthenelse
        (eop op_GreaterThan (evar x) (const 3))
        (assign y (evar x))
        (assign y (const 7))
      )
      skip
  ))
= let ast_e = evar x in
  let ast = assign y ast_e in
  let asf_e = const 7 in
  let asf = assign y asf_e in
  let cond = eop op_GreaterThan (evar x) (const 3) in
  let l = ifthenelse cond ast asf in
  let phi = sec43'_precond x y in
  let phi' = sec43'_postcond x y in
  let gcond = exp_to_gexp cond Left in
  r_dassl y ast_e (gand phi gcond) phi';
  r_dassl y asf_e (gand phi (gnot gcond)) phi';
  r_cbl cond ast asf skip phi phi'
