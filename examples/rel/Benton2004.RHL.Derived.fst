module Benton2004.RHL.Derived
include Benton2004.RHL

(* Derived rules and patterns *)

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
  [SMTPat (exec_equiv p p' (assign x e) (assign y e'))]
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
  [SMTPat (exec_equiv phi phi' (assign x e) skip)]
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
  [SMTPat (exec_equiv phi phi' skip (assign x e))]
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

unfold
let related c c' phi phi' = exec_equiv phi phi' c c'
