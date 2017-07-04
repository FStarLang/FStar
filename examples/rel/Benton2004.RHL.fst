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

let gfeq2 (#a: Type) (#b: Type) (#c: Type) (f1 f2: (a -> b -> GTot c)) : Lemma
  (requires (forall x y . f1 x y == f2 x y))
  (ensures (f1 == f2))
= assert (forall x . FunctionalExtensionality.gfeq (f1 x) (f2 x));
  assert (FunctionalExtensionality.feq f1 f2)

let gsubst_gconst (#t: Type0) (n: t) (x: var) (side: pos) (ge' : gexp int): Lemma
  (gsubst (gconst n) x side ge' == gconst n)
  [SMTPat (gsubst (gconst n) x side ge')]
= gfeq2 (gsubst (gconst n) x side ge') (gconst n)

let gsubst_gvar_same (x: var) (side: pos) (ge': gexp int) : Lemma
  (gsubst (gvar x side) x side ge' == ge')
  [SMTPat (gsubst (gvar x side) x side ge')]
= gfeq2 (gsubst (gvar x side) x side ge') ge'

let gsubst_gvar_other (x x': var) (side side': pos) (ge': gexp int) : Lemma
  (requires (x <> x' \/ side <> side'))
  (ensures (gsubst (gvar x side) x' side' ge' == gvar x side))
  [SMTPat (gsubst (gvar x side) x' side' ge')]
= gfeq2 (gsubst (gvar x side) x' side' ge') (gvar x side)

let gsubst_gop (#from #to: Type0) (op: (from -> from -> GTot to)) (ge1 ge2: gexp from) (x: var) (side: pos) (ge': gexp int) : Lemma
  (gsubst (gop op ge1 ge2) x side ge' == gop op (gsubst ge1 x side ge') (gsubst ge2 x side ge'))
  [SMTPat (gsubst (gop op ge1 ge2) x side ge')]
= gfeq2 (gsubst (gop op ge1 ge2) x side ge') (gop op (gsubst ge1 x side ge') (gsubst ge2 x side ge'))

(* 4.1.3 Inference rules *)

let interp (ge: gexp bool) : GTot sttype =
  let g s1 s2 : GTot Type0 = ge s1 s2 == true in
  g

let holds_interp
  (ge: gexp bool)
  (s1 s2: heap)
: Lemma
  (holds (interp ge) s1 s2 <==> ge s1 s2 == true)
  [SMTPat (holds (interp ge) s1 s2)]
= holds_equiv (interp ge) s1 s2

abstract
let exec_equiv
  (p p' : gexp bool)
  (f f' : computation)
: GTot Type0
= Benton2004.exec_equiv (interp p) (interp p') f f'

let exec_equiv_elim
  (p p' : gexp bool)
  (f f' : computation)
: Lemma
  (requires (exec_equiv p p' f f'))
  (ensures (Benton2004.exec_equiv (interp p) (interp p') f f'))
= ()

let r_skip
  (p: gexp bool)
: Lemma
  (exec_equiv p p skip skip)
  [SMTPat (exec_equiv p p skip skip)]
= d_skip (interp p)

let exp_to_gexp
  (#t: Type0)
  (e: exp t)
  (side: pos)
: GTot (gexp t)
= let g s1 s2 : GTot t =
    fst (reify_exp e (match side with | Left -> s1 | Right -> s2))
  in
  g

let exp_to_gexp_const
  (#t: Type0)
  (c: t)
  (side: pos)
: Lemma
  (exp_to_gexp (const c) side == gconst c)
  [SMTPat (exp_to_gexp (const c) side)]
= gfeq2 (exp_to_gexp (const c) side) (gconst c)

let exp_to_gexp_evar
  (#t: Type0)
  (x: var)
  (side: pos)
: Lemma
  (exp_to_gexp (evar x) side == gvar x side)
  [SMTPat (exp_to_gexp (evar x) side)]
= gfeq2 (exp_to_gexp (evar x) side) (gvar x side)

let exp_to_gexp_eop
  (#from #to: Type0)
  (op: (from -> from -> Tot to))
  (e1 e2: exp from)
  (side: pos)
: Lemma
  (exp_to_gexp (eop op e1 e2) side == gop op (exp_to_gexp e1 side) (exp_to_gexp e2 side))
  [SMTPat (exp_to_gexp (eop op e1 e2) side)]
= gfeq2 (exp_to_gexp (eop op e1 e2) side) (gop op (exp_to_gexp e1 side) (exp_to_gexp e2 side))

#set-options "--z3rlimit 2048 --max_fuel 8 --max_ifuel 8"

let gand (b1 b2 : gexp bool) : GTot (gexp bool) =
  gop op_AmpAmp b1 b2

let holds_gand (b1 b2 : gexp bool) : Lemma
  (forall s1 s2 . holds (interp (gand b1 b2)) s1 s2 <==> holds (interp b1) s1 s2 /\ holds (interp b2) s1 s2)
  [SMTPat (holds (interp (gand b1 b2)))]
= ()

let gor (b1 b2 : gexp bool) : GTot (gexp bool) =
  gop op_BarBar b1 b2

let holds_gor (b1 b2 : gexp bool) : Lemma
  (forall s1 s2 . holds (interp (gor b1 b2)) s1 s2 <==> holds (interp b1) s1 s2 \/ holds (interp b2) s1 s2)
  [SMTPat (holds (interp (gor b1 b2)))]
= ()

let holds_gnot (b: gexp bool) : Lemma
  (forall s1 s2 . holds (interp (gnot b)) s1 s2 <==> ~ (holds (interp b) s1 s2))
  [SMTPat (holds (interp (gnot b)))]
= ()

let geq
  (#t: eqtype)
  (e1 e2 : gexp t)
: GTot (gexp bool)
= gop op_Equality e1 e2

let holds_geq (#t: eqtype) (e1 e2 : gexp t) : Lemma
  (forall s1 s2 . holds (interp (geq e1 e2)) s1 s2 <==> e1 s1 s2 == e2 s1 s2)
  [SMTPat (holds (interp (geq e1 e2)))]
= ()

let holds_exp_to_gexp_left
  (e: exp bool)
: Lemma
  (forall s1 s2 . holds (interp (exp_to_gexp e Left)) s1 s2 <==> fst (reify_exp e s1) == true)
  [SMTPat (holds (interp (exp_to_gexp e Left)))]
= ()

let holds_exp_to_gexp_right
  (e: exp bool)
: Lemma
  (forall s1 s2 . holds (interp (exp_to_gexp e Right)) s1 s2 <==> fst (reify_exp e s2) == true)
  [SMTPat (holds (interp (exp_to_gexp e Right)))]
= ()

let r_if_precond_true
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: GTot (gexp bool)
= gand p (gand (exp_to_gexp b Left) (exp_to_gexp b' Right))

let holds_r_if_precond_true
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
= ()

let r_if_precond_false
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: GTot (gexp bool)
= gand p (gnot (gor (exp_to_gexp b Left) (exp_to_gexp b' Right)))

let holds_r_if_precond_false
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: Lemma
  (forall s1 s2 .
  holds (interp (r_if_precond_false b b' c c' d d' p p')) s1 s2 <==> (
    holds (interp p) s1 s2 /\
    ( ~ (fst (reify_exp b s1) == true \/ fst (reify_exp b' s2) == true))   
  ))
= ()  

let r_if_precond
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: GTot (gexp bool)
= gand p (geq (exp_to_gexp b Left) (exp_to_gexp b' Right))

let holds_r_if_precond
  (b b': exp bool)
  (c c' d d' : computation)
  (p p' : gexp bool)
: Lemma
  (forall s1 s2 .
  holds (interp (r_if_precond b b' c c' d d' p p')) s1 s2 <==> (
    holds (interp p) s1 s2 /\
    fst (reify_exp b s1) == fst (reify_exp b' s2)
  ))
= ()

let r_if
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
= holds_r_if_precond_true b b' c c' d d' p p';
  holds_r_if_precond_false b b' c c' d d' p p';
  holds_r_if_precond b b' c c' d d' p p'

let r_seq
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
  [SMTPat (exec_equiv p0 p2 (seq c01 c12) (seq c01' c12'))]
= d_seq (interp p0) (interp p1) (interp p2) c01 c01' c12 c12'

let r_ass
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
= ()

let included (p1 p2: gexp bool) : GTot Type0 =
  Benton2004.included (interp p1) (interp p2)

let included_alt (p1 p2 : gexp bool) : Lemma
  (included p1 p2 <==> (forall s1 s2 . p1 s1 s2 == true ==> p2 s1 s2 == true))
  [SMTPat (included p1 p2)]
= assert (forall s1 s2 . holds (interp p1) s1 s2 <==> p1 s1 s2 == true);
  assert (forall s1 s2 . holds (interp p2) s1 s2 <==> p2 s1 s2 == true)

let r_sub
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
= d_csub (interp p1) (interp p2) (interp p1') (interp p2') f f'

let is_per (p: gexp bool) = Benton2004.is_per (interp p)

(* Aparte: 4.4 How to prove is_per *)

let is_per_geq_exp_to_gexp
  (#t: eqtype)
  (e: exp t)
: Lemma
  (is_per (geq (exp_to_gexp e Left) (exp_to_gexp e Right)))
= ()

let is_per_gand_exp_to_gexp
  (b: exp bool)
: Lemma
  (is_per (gand (exp_to_gexp b Left) (exp_to_gexp b Right)))
= ()

let is_per_gand
  (e1 e2 : gexp bool)
: Lemma
  (requires (is_per e1 /\ is_per e2))
  (ensures (is_per (gand e1 e2)))
= assert (forall s1 s2 . holds (interp (gand e1 e2)) s1 s2 <==> holds (interp e1) s1 s2 /\ holds (interp e2) s1 s2)

let is_per_gor
  (e1 e2 : gexp bool)
: Lemma
  (requires (is_per e1 /\ is_per e2 /\ (forall s1 s2 . ~ (holds (interp e1) s1 s2 /\ holds (interp e2) s1 s2))))
  (ensures (is_per (gor e1 e2)))
= assert (forall s1 s2 . holds (interp (gor e1 e2)) s1 s2 <==> holds (interp e1) s1 s2 \/ holds (interp e2) s1 s2)

let r_sym
  (p p': gexp bool)
  (f f' : computation)
: Lemma
  (requires (is_per p /\ is_per p'))
  (exec_equiv p p' f f' <==> exec_equiv p p' f' f)
  [SMTPat (exec_equiv p p' f f')]
= exec_equiv_sym (interp p) (interp p') f f'

let interpolable (p: gexp bool) = Benton2004.interpolable (interp p)

(* Aparte: 4.4 How to prove interpolable *)

let interpolable_geq_exp_to_gexp
  (#t: eqtype)
  (e: exp t)
: Lemma
  (interpolable (geq (exp_to_gexp e Left) (exp_to_gexp e Right)))
= ()

let interpolable_gand_exp_to_gexp
  (b: exp bool)
: Lemma
  (interpolable (gand (exp_to_gexp b Left) (exp_to_gexp b Right)))
= ()

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

let r_trans
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
    [SMTPat (exec_equiv p p' c1 c2); SMTPat (exec_equiv p p' c2 c3)];
    [SMTPat (exec_equiv p p' c1 c2); SMTPat (exec_equiv p p' c1 c3)];
    [SMTPat (exec_equiv p p' c2 c3); SMTPat (exec_equiv p p' c2 c3)];
  ]]
= exec_equiv_trans (interp p) (interp p') c1 c2 c3
