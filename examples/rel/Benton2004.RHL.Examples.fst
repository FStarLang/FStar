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

(* Proof becomes really intractable. Thus let's design a better rule for assignment. *)

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
  (flip (flip phi) == phi)
  [SMTPat (flip (flip phi))]
= gfeq2 (flip (flip phi)) phi

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

#set-options "--z3rlimit 64"

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
  let phi_per : squash (is_per phi) = () in
  let phi_interp : squash (interpolable phi) = () in
  let cond = eop op_LessThan (evar i) (evar n) in
  let lbody_phi = gand phi (gand (exp_to_gexp cond Left) (exp_to_gexp cond Right)) in
  let lbody_phi' = gand phi (geq (exp_to_gexp cond Left) (exp_to_gexp cond Right)) in
  let asx_e = eop op_Addition (evar y) (const 1) in
  let asx = assign x asx_e in
  let lbody_phi12 = gand lbody_phi' (geq (gvar x Left) (gvar x Right)) in
  let asi_e = eop op_Addition (evar i) (evar x) in
  let asi = assign i asi_e in
  let lbody = seq asx asi in
  let rloop = while cond asi in
  let _ : squash (exec_equiv phi phi l (seq skip l)) =
    r_ass x x asx_e asx_e lbody_phi lbody_phi12;
    r_ass i i asi_e asi_e lbody_phi12 lbody_phi';
    r_while cond cond lbody lbody phi;
    d_su1 l phi phi;
    phi_per;
    phi_interp;
    assert (exec_equiv phi phi l (seq skip l))
  in
  let _ : squash (exec_equiv phi phi (seq skip l) r) =
    let gi () : Lemma (x <> i /\ x <> n /\ x <> y) =
      diffs;
      ()
    in
    gi ();
    r_dassr x asx_e phi phi;
    assume (exec_equiv phi phi l rloop);
    r_seq phi phi phi skip asx l rloop
  in
  phi_per;
  phi_interp;
  ()
