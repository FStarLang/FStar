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
module Benton2004.RHL
include Benton2004

(* Relational Hoare Logic (Section 4) *)

type gexp (t: Type0) = heap -> heap -> GTot t

let gconst (#t: Type0) (n: t) : gexp t =
  let g _ _ : GTot t = n in
  g

type pos =
  | Left
  | Right

let gvar (x: var) (side: pos) : GTot (gexp int) =
  let g s1 s2 : GTot int = sel (match side with Left -> s1 | Right -> s2) x in
  g

let gop (#from #to: Type0) (op: (from -> from -> GTot to)) (e1 e2: gexp from) : GTot (gexp to) =
  let g s1 s2 : GTot to = op (e1 s1 s2) (e2 s1 s2) in
  g

let gnot (e: gexp bool) : GTot (gexp bool) =
  let g s1 s2 = not (e s1 s2) in
  g

(* Substitution: Lemma 3 al. 1, 2 *)

let gsubst (#t: Type0) (ge: gexp t) (x: var) (side: pos) (ge': gexp int) : gexp t =
  let g s1 s2 : GTot t =
    let v' = ge' s1 s2 in
    match side with
    | Left -> ge (upd s1 x v') s2
    | Right -> ge s1 (upd s2 x v')
  in
  g

val gsubst_gconst (#t: Type0) (n: t) (x: var) (side: pos) (ge' : gexp int): Lemma
  (forall h1 h2. (gsubst (gconst n) x side ge') h1 h2 == (gconst n) h1 h2)
  [SMTPat (gsubst (gconst n) x side ge')]

val gsubst_gvar_same (x: var) (side: pos) (ge': gexp int) : Lemma
  (forall h1 h2. (gsubst (gvar x side) x side ge') h1 h2 == ge' h1 h2)
  [SMTPat (gsubst (gvar x side) x side ge')]

val gsubst_gvar_other (x x': var) (side side': pos) (ge': gexp int) : Lemma
  (requires (x <> x' \/ side <> side'))
  (ensures  (forall h1 h2. (gsubst (gvar x side) x' side' ge') h1 h2 == (gvar x side) h1 h2))
  [SMTPat (gsubst (gvar x side) x' side' ge')]

val gsubst_gop (#from #to: Type0) (op: (from -> from -> GTot to)) (ge1 ge2: gexp from) (x: var) (side: pos) (ge': gexp int) : Lemma
  (forall h1 h2. (gsubst (gop op ge1 ge2) x side ge') h1 h2 ==
            (gop op (gsubst ge1 x side ge') (gsubst ge2 x side ge')) h1 h2)
  [SMTPat (gsubst (gop op ge1 ge2) x side ge')]

(* 4.1.3 Inference rules *)

let interp (ge: gexp bool) : GTot sttype =
  let g s1 s2 : GTot Type0 = ge s1 s2 == true in
  g

val holds_interp
  (ge: gexp bool)
  (s1 s2: heap)
: Lemma
  (holds (interp ge) s1 s2 <==> ge s1 s2 == true)
  [SMTPat (holds (interp ge) s1 s2)]

val exec_equiv
  (p p' : gexp bool)
  (f f' : computation)
: GTot Type0

val exec_equiv_elim
  (p p' : gexp bool)
  (f f' : computation)
: Lemma
  (requires (exec_equiv p p' f f'))
  (ensures (Benton2004.exec_equiv (interp p) (interp p') f f'))

val r_skip
  (p: gexp bool)
: Lemma
  (exec_equiv p p skip skip)
  [SMTPat (exec_equiv p p skip skip)]

let exp_to_gexp
  (#t: Type0)
  (e: exp t)
  (side: pos)
: GTot (gexp t)
= let g s1 s2 : GTot t =
    fst (reify_exp e (match side with | Left -> s1 | Right -> s2))
  in
  g

val exp_to_gexp_const
  (#t: Type0)
  (c: t)
  (side: pos)
: Lemma
  (forall h1 h2. (exp_to_gexp (const c) side) h1 h2 == (gconst c) h1 h2)
  [SMTPat (exp_to_gexp (const c) side)]

val exp_to_gexp_evar
  (x: var)
  (side: pos)
: Lemma
  (forall h1 h2. (exp_to_gexp (evar x) side) h1 h2 == (gvar x side) h1 h2)
  [SMTPat (exp_to_gexp (evar x) side)]

val exp_to_gexp_eop
  (#from #to: Type0)
  (op: (from -> from -> Tot to))
  (e1 e2: exp from)
  (side: pos)
: Lemma
  (forall h1 h2. (exp_to_gexp (eop op e1 e2) side) h1 h2 == (gop op (exp_to_gexp e1 side) (exp_to_gexp e2 side)) h1 h2)
  [SMTPat (exp_to_gexp (eop op e1 e2) side)]

let gand (b1 b2 : gexp bool) : GTot (gexp bool) =
  gop op_AmpAmp b1 b2

val holds_gand (b1 b2 : gexp bool) : Lemma
  (forall s1 s2 . holds (interp (gand b1 b2)) s1 s2 <==> holds (interp b1) s1 s2 /\ holds (interp b2) s1 s2)
  [SMTPat (holds (interp (gand b1 b2)))]

val gsubst_gand (b1 b2: gexp bool) (x:_) (side:_) (e:_) : Lemma
  (forall h1 h2. (gsubst (gand b1 b2) x side e) h1 h2 == (gand (gsubst b1 x side e) (gsubst b2 x side e)) h1 h2)
  [SMTPat (gsubst (gand b1 b2) x side e)]

let gor (b1 b2 : gexp bool) : GTot (gexp bool) =
  gop op_BarBar b1 b2

val holds_gor (b1 b2 : gexp bool) : Lemma
  (forall s1 s2 . holds (interp (gor b1 b2)) s1 s2 <==> holds (interp b1) s1 s2 \/ holds (interp b2) s1 s2)
  [SMTPat (holds (interp (gor b1 b2)))]

val gsubst_gor (b1 b2: gexp bool) (x:_) (side:_) (e:_) : Lemma
  (forall h1 h2. (gsubst (gor b1 b2) x side e) h1 h2 == (gor (gsubst b1 x side e) (gsubst b2 x side e)) h1 h2)
  [SMTPat (gsubst (gor b1 b2) x side e)]

val holds_gnot (b: gexp bool) : Lemma
  (forall s1 s2 . holds (interp (gnot b)) s1 s2 <==> ~ (holds (interp b) s1 s2))
  [SMTPat (holds (interp (gnot b)))]

let geq
  (#t: eqtype)
  (e1 e2 : gexp t)
: GTot (gexp bool)
= gop op_Equality e1 e2

val holds_geq (#t: eqtype) (e1 e2 : gexp t) : Lemma
  (forall s1 s2 . holds (interp (geq e1 e2)) s1 s2 <==> e1 s1 s2 == e2 s1 s2)
  [SMTPat (holds (interp (geq e1 e2)))]

val gsubst_geq (#t: eqtype) (b1 b2: gexp t) (x:_) (side:_) (e:_) : Lemma
  (forall h1 h2. (gsubst (geq b1 b2) x side e) h1 h2 == (geq (gsubst b1 x side e) (gsubst b2 x side e)) h1 h2)
  [SMTPat (gsubst (geq b1 b2) x side e)]

val holds_exp_to_gexp_left
  (e: exp bool)
: Lemma
  (forall s1 s2 . holds (interp (exp_to_gexp e Left)) s1 s2 <==> fst (reify_exp e s1) == true)
  [SMTPat (holds (interp (exp_to_gexp e Left)))]

val holds_exp_to_gexp_right
  (e: exp bool)
: Lemma
  (forall s1 s2 . holds (interp (exp_to_gexp e Right)) s1 s2 <==> fst (reify_exp e s2) == true)
  [SMTPat (holds (interp (exp_to_gexp e Right)))]

let r_if_precond_true
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: GTot (gexp bool)
= gand p (gand (exp_to_gexp b Left) (exp_to_gexp b' Right))

val holds_r_if_precond_true
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: Lemma
  (forall s1 s2 .
    holds (interp (r_if_precond_true b b' c c' d d' p p')) s1 s2 <==> (
    holds (interp p) s1 s2 /\
    fst (reify_exp b s1) == true /\
    fst (reify_exp b' s2) == true
  ))

let r_if_precond_false
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: GTot (gexp bool)
= gand p (gnot (gor (exp_to_gexp b Left) (exp_to_gexp b' Right)))

val holds_r_if_precond_false
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: Lemma
  (forall s1 s2 .
  holds (interp (r_if_precond_false b b' c c' d d' p p')) s1 s2 <==> (
    holds (interp p) s1 s2 /\
    ( ~ (fst (reify_exp b s1) == true \/ fst (reify_exp b' s2) == true))   
  ))

let r_if_precond
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: GTot (gexp bool)
= gand p (geq (exp_to_gexp b Left) (exp_to_gexp b' Right))

val holds_r_if_precond
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: Lemma
  (forall s1 s2 .
  holds (interp (r_if_precond b b' c c' d d' p p')) s1 s2 <==> (
    holds (interp p) s1 s2 /\
    fst (reify_exp b s1) == fst (reify_exp b' s2)
  ))

val r_if
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: Lemma
  (requires (
    exec_equiv
      (r_if_precond_true b b' c c' d d' p p')
      p'
      c
      c' /\
    exec_equiv
      (r_if_precond_false b b' c c' d d' p p')
      p'
      d
      d'
  ))
  (ensures (
    exec_equiv
      (r_if_precond b b' c c' d d' p p')
      p'
      (ifthenelse b c d)
      (ifthenelse b' c' d')
  ))

val r_seq
  (p0 p1 p2 : gexp bool)
  (c01 c01' c12 c12' : computation)
: Lemma
  (requires (
    exec_equiv p0 p1 c01 c01' /\
    exec_equiv p1 p2 c12 c12'
  ))
  (ensures (
    exec_equiv p0 p2 (seq c01 c12) (seq c01' c12')
  ))
  [SMTPatOr [
    [SMTPat (exec_equiv p0 p2 (seq c01 c12) (seq c01' c12')); SMTPat (exec_equiv p0 p1 c01 c01')];
    [SMTPat (exec_equiv p0 p2 (seq c01 c12) (seq c01' c12')); SMTPat (exec_equiv p1 p2 c12 c12')];
    [SMTPat (exec_equiv p0 p1 c01 c01'); SMTPat (exec_equiv p1 p2 c12 c12')];
  ]]

val r_ass
  (x y: var)
  (e e' : exp int)
  (p: gexp bool)
: Lemma
  (exec_equiv
    (gsubst (gsubst p x Left (exp_to_gexp e Left)) y Right (exp_to_gexp e' Right))
    p
    (assign x e)
    (assign y e')
  )

let included (p1 p2: gexp bool) : GTot Type0 =
  Benton2004.included (interp p1) (interp p2)

val included_alt (p1 p2 : gexp bool) : Lemma
  (included p1 p2 <==> (forall s1 s2 . p1 s1 s2 == true ==> p2 s1 s2 == true))
  [SMTPat (included p1 p2)]

val r_sub
  (p1 p2 p1' p2' : gexp bool)
  (f f' : computation)
: Lemma
  (requires (
    exec_equiv p1 p2 f f' /\
    included p1' p1 /\
    included p2 p2'
  ))
  (ensures (exec_equiv p1' p2' f f'))
  [SMTPat (exec_equiv p1' p2' f f'); SMTPat (exec_equiv p1 p2 f f')]

val r_while_terminates'
  (b b' : exp bool)
  (c c' : computation)
  (phi phi_c phi_c': gexp bool)
  (s0 s0' : heap)
  (fuel: nat)
: Lemma
  (requires (
    included phi (geq (exp_to_gexp b Left) (exp_to_gexp b' Right)) /\
    included (gand phi (gand (exp_to_gexp b Left) (exp_to_gexp b' Right))) phi_c /\
    included phi_c' phi /\
    exec_equiv phi_c phi_c' c c' /\
    holds (interp phi) s0 s0' /\
    fst (reify_computation (while b c) fuel s0) == true
  ))
  (ensures (
    terminates_on (reify_computation (while b' c')) s0'
  ))
  (decreases fuel)

let flip (phi: gexp bool) : Tot (gexp bool) =
  let g s1 s2 = phi s2 s1 in
  g

val holds_interp_flip (phi: gexp bool) : Lemma
  (forall s1 s2 . holds (interp (flip phi)) s1 s2 <==> holds (Benton2004.flip (interp phi)) s1 s2)
  [SMTPat (holds (interp (flip phi)))]

val exec_equiv_flip
  (p p': gexp bool)
  (f f' : computation)
: Lemma
  (exec_equiv (flip p) (flip p') f f' <==> exec_equiv p p' f' f)
  [SMTPat (exec_equiv (flip p) (flip p') f f')]

val r_while_terminates
  (b b' : exp bool)
  (c c' : computation)
  (p: gexp bool)
  (s0 s0' : heap)
: Lemma
  (requires (
    exec_equiv (gand p (gand (exp_to_gexp b Left) (exp_to_gexp b' Right))) (gand p (geq (exp_to_gexp b Left) (exp_to_gexp b' Right))) c c' /\
    holds (interp (gand p (geq (exp_to_gexp b Left) (exp_to_gexp b' Right)))) s0 s0'
  ))
  (ensures (
    terminates_on (reify_computation (while b c)) s0 <==>
    terminates_on (reify_computation (while b' c')) s0'
  ))

val r_while_correct
  (b b' : exp bool)
  (c c' : computation)
  (p: gexp bool)
  (s0 s0' : heap)
  (fuel: nat)
: Lemma
  (requires (
    exec_equiv (gand p (gand (exp_to_gexp b Left) (exp_to_gexp b' Right))) (gand p (geq (exp_to_gexp b Left) (exp_to_gexp b' Right))) c c' /\
    holds (interp (gand p (geq (exp_to_gexp b Left) (exp_to_gexp b' Right)))) s0 s0' /\
    fst (reify_computation (while b c) fuel s0) == true /\
    fst (reify_computation (while b' c') fuel s0') == true
  ))
  (ensures (
    holds (interp (gand p (gnot (gor (exp_to_gexp b Left) (exp_to_gexp b' Right))))) (snd (reify_computation (while b c) fuel s0)) (snd (reify_computation (while b' c') fuel s0'))
  ))
  (decreases fuel)

val r_while
  (b b' : exp bool)
  (c c' : computation)
  (p: gexp bool)
: Lemma
  (requires (
    exec_equiv (gand p (gand (exp_to_gexp b Left) (exp_to_gexp b' Right))) (gand p (geq (exp_to_gexp b Left) (exp_to_gexp b' Right))) c c'
  ))
  (ensures (
    exec_equiv (gand p (geq (exp_to_gexp b Left) (exp_to_gexp b' Right))) (gand p (gnot (gor (exp_to_gexp b Left) (exp_to_gexp b' Right)))) (while b c) (while b' c')
  ))

let is_per (p: gexp bool) = Benton2004.is_per (interp p)

(* Aparte: 4.4 How to prove is_per *)

val is_per_geq_exp_to_gexp
  (#t: eqtype)
  (e: exp t)
: Lemma
  (is_per (geq (exp_to_gexp e Left) (exp_to_gexp e Right)))

val is_per_gand_exp_to_gexp
  (b: exp bool)
: Lemma
  (is_per (gand (exp_to_gexp b Left) (exp_to_gexp b Right)))

val is_per_gand
  (e1 e2 : gexp bool)
: Lemma
  (requires (is_per e1 /\ is_per e2))
  (ensures (is_per (gand e1 e2)))

(* FIXME: holds but not replayable
let is_per_gor
  (e1 e2 : gexp bool)
: Lemma
  (requires (is_per e1 /\ is_per e2 /\ (forall s1 s2 . ~ (holds (interp e1) s1 s2 /\ holds (interp e2) s1 s2))))
  (ensures (is_per (gor e1 e2)))
= assert (forall s1 s2 . holds (interp (gor e1 e2)) s1 s2 <==> holds (interp e1) s1 s2 \/ holds (interp e2) s1 s2)
*)

val r_sym
  (p p': gexp bool)
  (f f' : computation)
: Lemma
  (requires (is_per p /\ is_per p'))
  (ensures (exec_equiv p p' f f' <==> exec_equiv p p' f' f))
  [SMTPat (exec_equiv p p' f f'); SMTPat (is_per p); SMTPat (is_per p')]

let interpolable (p: gexp bool) = Benton2004.interpolable (interp p)

(* Aparte: 4.4 How to prove interpolable *)

val interpolable_geq_exp_to_gexp
  (#t: eqtype)
  (e: exp t)
: Lemma
  (interpolable (geq (exp_to_gexp e Left) (exp_to_gexp e Right)))

val interpolable_gand_exp_to_gexp
  (b: exp bool)
: Lemma
  (interpolable (gand (exp_to_gexp b Left) (exp_to_gexp b Right)))

(* FIXME: holds but not replayable
let interpolable_gand
  (e1 e2 : gexp bool)
: Lemma
  (requires (is_per e1 /\ is_per e2 /\ interpolable e1 /\ interpolable e2))
  (ensures (interpolable (gand e1 e2)))
= assert (forall s1 s2 . holds (interp (gand e1 e2)) s1 s2 <==> holds (interp e1) s1 s2 /\ holds (interp e2) s1 s2)

let interpolable_gor
  (e1 e2 : gexp bool)
: Lemma
  (requires (is_per e1 /\ is_per e2 /\ interpolable e1 /\ interpolable e2))
  (ensures (interpolable (gor e1 e2)))
= assert (forall s1 s2 . holds (interp (gor e1 e2)) s1 s2 <==> holds (interp e1) s1 s2 \/ holds (interp e2) s1 s2)
*)

val r_trans
  (p p' : gexp bool)
  (c1 c2 c3 : computation)
: Lemma
  (requires (
    is_per p' /\
    interpolable p /\
    exec_equiv p p' c1 c2 /\
    exec_equiv p p' c2 c3
  ))
  (ensures (exec_equiv p p' c1 c3))
  [SMTPatOr [
    [SMTPat (exec_equiv p p' c1 c2); SMTPat (exec_equiv p p' c2 c3); SMTPat (is_per p'); SMTPat (interpolable p)];
    [SMTPat (exec_equiv p p' c1 c2); SMTPat (exec_equiv p p' c1 c3); SMTPat (is_per p'); SMTPat (interpolable p)];
    [SMTPat (exec_equiv p p' c1 c3); SMTPat (exec_equiv p p' c2 c3); SMTPat (is_per p'); SMTPat (interpolable p)];
  ]]

(* 4.2.1 Basic equations *)

val d_su1
  (c: computation)
  (phi phi' : gexp bool)
: Lemma
  (requires (exec_equiv phi phi' c c))
  (ensures (exec_equiv phi phi' (seq skip c) c))
  [SMTPat (exec_equiv phi phi' (seq skip c) c)]

val d_su1'
  (c c' c'' : computation)
  (phi phi' phi'' : gexp bool)
: Lemma
  (requires (
    exec_equiv phi phi' c skip /\
    exec_equiv phi' phi'' c' c''
  ))
  (ensures (exec_equiv phi phi'' (seq c c') c''))
  [SMTPatOr [
    [SMTPat (exec_equiv phi phi'' (seq c c') c''); SMTPat (exec_equiv phi phi' c skip)];
    [SMTPat (exec_equiv phi phi'' (seq c c') c''); SMTPat (exec_equiv phi' phi'' c' c'')];
    [SMTPat (exec_equiv phi' phi'' c' c''); SMTPat (exec_equiv phi phi' c skip)];
  ]]

val d_su2
  (c: computation)
  (phi phi' : gexp bool)
: Lemma
  (requires (exec_equiv phi phi' c c))
  (ensures (exec_equiv phi phi' (seq c skip) c))
  [SMTPat (exec_equiv phi phi' (seq c skip) c)]

val d_assoc
  (c1 c2 c3: computation)
  (phi phi' : gexp bool)
: Lemma
  (requires (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq (seq c1 c2) c3)))
  (ensures (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq c1 (seq c2 c3))))
  [SMTPat (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq c1 (seq c2 c3)))]

val d_cc
  (b: exp bool)
  (c1 c2 c3: computation)
  (phi phi' phi'' : gexp bool)
: Lemma
  (requires (
    exec_equiv phi phi' (ifthenelse b c1 c2) (ifthenelse b c1 c2) /\
    exec_equiv phi' phi'' c3 c3
  ))
  (ensures (
    exec_equiv phi phi'' (seq (ifthenelse b c1 c2) c3) (ifthenelse b (seq c1 c3) (seq c2 c3))
  ))
  [SMTPatOr [
    [SMTPat (exec_equiv phi phi'' (seq (ifthenelse b c1 c2) c3) (ifthenelse b (seq c1 c3) (seq c2 c3))); SMTPat (exec_equiv phi phi' (ifthenelse b c1 c2) (ifthenelse b c1 c2))];
    [SMTPat (exec_equiv phi phi'' (seq (ifthenelse b c1 c2) c3) (ifthenelse b (seq c1 c3) (seq c2 c3))); SMTPat (exec_equiv phi' phi'' c3 c3)];
    [SMTPat (exec_equiv phi phi' (ifthenelse b c1 c2) (ifthenelse b c1 c2)); SMTPat (exec_equiv phi' phi'' c3 c3)];
  ]]

val d_lu1
  (b: exp bool)
  (c: computation)
  (phi phi' : gexp bool)
: Lemma
  (requires (exec_equiv phi phi' (while b c) (while b c)))
  (ensures (exec_equiv phi phi' (while b c) (ifthenelse b (seq c (while b c)) skip)))

val d_lu2
  (b: exp bool)
  (c: computation)
  (phi phi' : gexp bool)
: Lemma
  (requires (exec_equiv phi phi' (while b c) (while b c)))
  (ensures (exec_equiv phi phi' (while b c) (while b (seq c (ifthenelse b c skip)))))

(* 4.2.2 Optimizing Transformations *)

(* Falsity *)

val r_f
  (c c' : computation)
  (phi: gexp bool)
: Lemma
  (ensures (
    exec_equiv
      (gconst false)
      phi
      c
      c'
  ))

(* Dead assignment *)

val r_dassl
  (x: var)
  (e: exp int)
  (phi: gexp bool)
: Lemma
  (ensures (
    exec_equiv
      (gsubst phi x Left (exp_to_gexp e Left))
      phi
      (assign x e)
      skip
  ))

(* Common branch *)

val r_cbl
  (b: exp bool)
  (c c' d : computation)
  (phi phi' : gexp bool)
: Lemma
  (requires (
    exec_equiv
      (gand phi (exp_to_gexp b Left))
      phi'
      c
      d /\
    exec_equiv
      (gand phi (gnot (exp_to_gexp b Left)))
      phi'
      c'
      d
  ))
  (ensures (
    exec_equiv
      phi
      phi'
      (ifthenelse b c c')
      d
  ))

(* Dead while *)

val r_dwhll
  (b: exp bool)
  (c: computation)
  (phi: gexp bool)
: Lemma
  (ensures (
    exec_equiv
      (gand phi (gnot (exp_to_gexp b Left)))
      (gand phi (gnot (exp_to_gexp b Left)))
      (while b c)
      skip
  ))
