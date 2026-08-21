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

(* Section 19.14.  A refinement is a proposition, and no question Custard asks
   about a declaration's type depends on one.

   [q40] is a proposition that costs 2^40 reduction steps to normalize and
   says [True].  It appears only in [table]'s refinement.  Deciding whether
   [table] is a type declaration or a value declaration used to normalize the
   whole of [x: U32.t{q40}] and then throw the proposition away, so this file
   could not be extracted under any budget at all; stripping first, it costs
   nothing.

   The Makefile runs this with a deliberately small --custard_norm_budget, so
   the test is that it extracts rather than that it extracts quickly.  This is
   EverParse's CDDL [env9] in miniature, whose refinement is a well-formedness
   condition on a machine-generated environment and which exhausted 10^9
   steps. *)
module RefStrip

module U32 = FStar.UInt32
module I32 = FStar.Int32

let q0 : prop = True
let q1 : prop = q0 /\ q0
let q2 : prop = q1 /\ q1
let q3 : prop = q2 /\ q2
let q4 : prop = q3 /\ q3
let q5 : prop = q4 /\ q4
let q6 : prop = q5 /\ q5
let q7 : prop = q6 /\ q6
let q8 : prop = q7 /\ q7
let q9 : prop = q8 /\ q8
let q10 : prop = q9 /\ q9
let q11 : prop = q10 /\ q10
let q12 : prop = q11 /\ q11
let q13 : prop = q12 /\ q12
let q14 : prop = q13 /\ q13
let q15 : prop = q14 /\ q14
let q16 : prop = q15 /\ q15
let q17 : prop = q16 /\ q16
let q18 : prop = q17 /\ q17
let q19 : prop = q18 /\ q18
let q20 : prop = q19 /\ q19
let q21 : prop = q20 /\ q20
let q22 : prop = q21 /\ q21
let q23 : prop = q22 /\ q22
let q24 : prop = q23 /\ q23
let q25 : prop = q24 /\ q24
let q26 : prop = q25 /\ q25
let q27 : prop = q26 /\ q26
let q28 : prop = q27 /\ q27
let q29 : prop = q28 /\ q28
let q30 : prop = q29 /\ q29
let q31 : prop = q30 /\ q30
let q32 : prop = q31 /\ q31
let q33 : prop = q32 /\ q32
let q34 : prop = q33 /\ q33
let q35 : prop = q34 /\ q34
let q36 : prop = q35 /\ q35
let q37 : prop = q36 /\ q36
let q38 : prop = q37 /\ q37
let q39 : prop = q38 /\ q38
let q40 : prop = q39 /\ q39

(* Assumed rather than proved: the point is the size of the term, and asking
   the SMT solver to unfold it would be the same problem one layer down. *)
assume val q40_holds : squash q40

let table : (x:U32.t{q40}) = q40_holds; 7ul

let main () : FStar.All.ML I32.t =
  if U32.eq table 7ul then 0l else 1l
