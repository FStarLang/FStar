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
module Benton2004.RHL.Examples2
include Benton2004.RHL.Derived

assume val i: var
assume val n: var
assume val x: var
assume val y: var
assume val hyp : squash (List.Tot.noRepeats [i; n; x; y] == true)

let cond = eop op_LessThan (evar i) (evar n)
let asx_e = eop op_Addition (evar y) (const 1)
let asi_e = eop op_Addition (evar i) (evar x)
let l = while cond (seq (assign x asx_e) (assign i asi_e))
let r = seq (assign x asx_e) (while cond (assign i asi_e))

let phi () : GTot (gexp bool) = gand (geq (gvar i Left) (gvar i Right)) (gand (geq (gvar n Left) (gvar n Right)) (geq (gvar y Left) (gvar y Right)))

#set-options "--z3rlimit 100"

let proof () : Lemma
  (related l r (phi ()) (phi ()))
= 
  let phi = phi () in
  let phi1 = gand phi (geq (gvar x Right) (gop op_Addition (gvar y Right) (gconst 1))) in
  let phi2 = gand phi1 (geq (gvar x Left) (gvar x Right)) in
  hyp;
  assert (related (assign x asx_e) skip phi1 phi2); // by r_dassl
  assert (related (assign i asi_e) (assign i asi_e) phi2 phi2); // by r_ass
  d_su1' (assign x asx_e) (assign i asi_e) (assign i asi_e) phi1 phi2 phi2;
  r_while cond cond (seq (assign x asx_e) (assign i asi_e)) (assign i asi_e) phi1;
  assert (related skip (assign x asx_e) phi phi1); // by r_dassr
  assert (related l (while cond (assign i asi_e)) phi1 phi); // by d_sub
  d_su1'_flip l (assign x asx_e) (while cond (assign i asi_e)) phi phi1 phi
