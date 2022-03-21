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
module Benton2004.DDCC
include Benton2004

type per (t: Type0) = ( f: rel t { is_per f } )

type nstype (t: Type0) = per t

let ns_f (#t: Type0) : nstype t =
  let f (x y: t) = False in
  Classical.forall_intro_2 (holds_equiv f);
  f

val holds_ns_f (#t: Type0) (x y: t): Lemma
  (holds ns_f x y <==> False)
  [SMTPat (holds ns_f x y)]

let ns_t (#t: Type0) : nstype t =
  let f (x y: t) = True in
  Classical.forall_intro_2 (holds_equiv f);
  f

val holds_ns_t (#t: Type0) (x y: t): Lemma
  (holds ns_t x y <==> True)
  [SMTPat (holds ns_t x y)]

let ns_singl (#t: Type0) (c: t) : nstype t =
  let f (x y: t) = (x == c /\ y == c) in
  Classical.forall_intro_2 (holds_equiv f);
  f

val holds_ns_singl (#t: Type0) (c: t) (x y: t) : Lemma
  (holds (ns_singl c) x y <==> (x == c /\ y == c))
  [SMTPat (holds (ns_singl c) x y)]

let ns_delta (#t: Type0) : nstype t =
  let f (x y: t) = (x == y) in
  Classical.forall_intro_2 (holds_equiv f);
  f

val holds_ns_delta (#t: Type0) (x y : t) : Lemma
  (holds ns_delta x y <==> x == y)
  [SMTPat (holds ns_delta x y)]

val interpolable_ns_f (#t:Type) : Lemma (interpolable #t ns_f)
val interpolable_ns_t (#t:Type) : Lemma (interpolable #t ns_t)
val interpolable_ns_singl (#t:Type) (c: t) : Lemma (interpolable (ns_singl c))
val interpolable_ns_delta (#t:Type) : Lemma (interpolable #t ns_delta)

type sttype = (f: per heap { interpolable f } )

let st_nil: sttype =
  let f (x y : heap) : GTot Type0 = True in
  f

val holds_st_nil
  (x y: heap)
: Lemma
  (holds st_nil x y <==> True)
  [SMTPat (holds st_nil x y)]

let st_var
  (x: var)
  (v: nstype int)
: GTot sttype
= let f (s1 s2: heap) : GTot Type0 = holds v (sel s1 x) (sel s2 x) in
  Classical.forall_intro_2 (holds_equiv f);
  f

val holds_st_var
  (x: var)
  (v: nstype int)
  (a b: heap)
: Lemma
  (holds (st_var x v) a b <==> holds v (sel a x) (sel b x))
  [SMTPat (holds (st_var x v) a b)]

let st_intersect
  (p1 p2: sttype)
: GTot sttype
= intersect p1 p2

val holds_st_intersect
  (ns1 ns2: sttype)
  (x y: heap)
: Lemma
  (holds (st_intersect ns1 ns2) x y <==> (holds ns1 x y /\ holds ns2 x y))
  [SMTPat (holds (st_intersect ns1 ns2) x y)]

let st_fresh_in
  (x: var)
  (p: sttype)
: GTot Type0
= forall s1 s1' s2 s2' . 
  (holds p s1 s2 /\ (
    forall y . y <> x ==> (sel s1' y == sel s1 y /\ sel s2' y == sel s2 y)
  )) ==>
  holds p s1' s2'

val st_fresh_in_nil
  (x: var)
: Lemma
  (x `st_fresh_in` st_nil)

let st_cons
  (p: sttype)
  (x: var)
  (v: nstype int)
: Ghost sttype
  (requires (x `st_fresh_in` p))
  (ensures (fun _ -> True))
= st_intersect p (st_var x v)

val st_fresh_in_var
  (x: var)
  (v: nstype int)
  (y: var)
: Lemma
  (requires (y <> x))
  (ensures (y `st_fresh_in` (st_var x v)))

val st_fresh_in_intersect
  (x: var)
  (p1 p2: sttype)
: Lemma
  (requires (
    x `st_fresh_in` p1 /\
    x `st_fresh_in` p2
  ))
  (ensures (x `st_fresh_in` (st_intersect p1 p2)))

val st_fresh_in_cons
  (p: sttype)
  (x: var)
  (v: nstype int)
  (y: var)
: Lemma
  (requires (
    x `st_fresh_in` p /\
    y `st_fresh_in` p /\
    x <> y
  ))
  (ensures (
    x `st_fresh_in` p /\
    y `st_fresh_in` (st_cons p x v)
  ))

val subtype_ns_f (#t: Type0) (phi: nstype t) : Lemma
  (included ns_f phi)

val subtype_ns_singl_delta (#t: Type0) (c: t) : Lemma
  (ns_singl c `included` ns_delta)

val subtype_ns_t (#t: Type0) (phi: nstype t) : Lemma
  (included phi ns_t)

val subtype_st_nil (phi: sttype) : Lemma
  (included phi st_nil)

val subtype_st_f (phi phi' : sttype) (x: var) : Lemma
  (requires (x `st_fresh_in` phi))
  (ensures (x `st_fresh_in` phi /\ included (st_cons phi x ns_f) phi'))

val subtype_st_t (phi phi' : sttype) (x: var) : Lemma
  (requires (x `st_fresh_in` phi' /\ included phi phi'))
  (ensures (x `st_fresh_in` phi' /\ included phi (st_cons phi' x ns_t)))

val subtype_st_cons (phi phi' : sttype) (f f' : nstype int) (x: var) : Lemma
  (requires (
    included phi phi' /\
    included f f' /\
    x `st_fresh_in` phi /\
    x `st_fresh_in` phi'
  ))
  (ensures (
    x `st_fresh_in` phi /\
    x `st_fresh_in` phi' /\
    included (st_cons phi x f) (st_cons phi' x f')
  ))

val eval_equiv_reified
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': reified_exp t)
: GTot Type0

val eval_equiv_reified_elim
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': reified_exp t)
  (s s' : heap)
: Lemma
  (requires (eval_equiv_reified p e f f' /\ holds p s s'))
  (ensures (holds e (fst (f s)) (fst (f' s'))))

val terminates_equiv_reified
  (p : sttype)
  (f f' : reified_computation)
: GTot Type0

val terminates_equiv_reified_elim
  (p : sttype)
  (f f' : reified_computation)
  (s s' : heap)
: Lemma
  (requires (terminates_equiv_reified p f f' /\ holds p s s'))
  (ensures (terminates_on f s <==> terminates_on f' s'))

val exec_equiv_reified
  (p p' : sttype)
  (f f' : reified_computation)
: GTot Type0

val exec_equiv_reified_terminates
  (p p' : sttype)
  (f f' : reified_computation)
: Lemma
  (requires (exec_equiv_reified p p' f f'))
  (ensures (terminates_equiv_reified p f f'))

val exec_equiv_reified_elim
  (p p' : sttype)
  (f f' : reified_computation)
  (s s' : heap)
  (fuel: nat)
: Lemma
  (requires (exec_equiv_reified p p' f f' /\ holds p s s' /\ fst (f fuel s) == true /\ fst (f' fuel s') == true))
  (ensures (holds p' (snd (f fuel s)) (snd (f' fuel s'))))

let exec_equiv
  (p p' : sttype)
  (f f' : computation)
: GTot Type0
= let f = reify_computation f in
  let f' = reify_computation f' in
  exec_equiv_reified p p' f f'

val eval_equiv_sym
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': exp t)
: Lemma
  (requires (eval_equiv p e f f'))
  (ensures (eval_equiv p e f' f))

val exec_equiv_sym
  (p p': sttype)
  (f f' : computation)
: Lemma
  (exec_equiv p p' f f' <==> exec_equiv p p' f' f)
  [SMTPat (exec_equiv p p' f f')]

val eval_equiv_trans
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f1 f2 f3 : exp t)
: Lemma
  (requires (eval_equiv p e f1 f2 /\ eval_equiv p e f2 f3))
  (ensures (eval_equiv p e f1 f3))

val exec_equiv_reified_trans
  (p p': sttype)
  (f1 f2 f3 : reified_computation)
: Lemma
  (requires (exec_equiv_reified p p' f1 f2 /\ exec_equiv_reified p p' f2 f3))
  (ensures (exec_equiv_reified p p' f1 f3))

val exec_equiv_trans
  (p p' : sttype)
  (c1 c2 c3 : computation)
: Lemma
  (requires (
    exec_equiv p p' c1 c2 /\
    exec_equiv p p' c2 c3
  ))
  (ensures (exec_equiv p p' c1 c3))
  [SMTPatOr [
    [SMTPat (exec_equiv p p' c1 c2); SMTPat (exec_equiv p p' c2 c3)];
    [SMTPat (exec_equiv p p' c1 c2); SMTPat (exec_equiv p p' c1 c3)];
    [SMTPat (exec_equiv p p' c2 c3); SMTPat (exec_equiv p p' c1 c3)];
  ]]

(* Subtyping and structural *)

(* The following, from the POPL paper, is wrong (because of divergence), and has been removed from the revised version available at:
https://www.researchgate.net/publication/2928156_Simple_Relational_Correctness_Proofs_for_Static_Analyses_and_Program_Transformations_DRAFT_--_Revised_Long_Version_--_DRAFT
<<
let d_ct1
  (c c' : computation)
  (p: sttype)
: Lemma
  (exec_equiv p st_nil c c')
= ()
>>
*)

val d_ct
  (c c' : computation)
  (p p' : sttype)
  (x: var)
: Lemma
  (requires (x `st_fresh_in` p))
  (ensures (x `st_fresh_in` p /\ exec_equiv (st_cons p x ns_f) p' c c'))
  [SMTPat (exec_equiv (st_cons p x ns_f) p' c c')]

val d_et1
  (#t: Type0)
  (f f' : exp t)
  (p: sttype)
: Lemma
  (eval_equiv p ns_t f f')
  [SMTPat (eval_equiv p ns_t f f')]

val d_et2
  (#t: Type0)
  (f f' : exp t)
  (p: sttype)
  (x: var)
  (p' : nstype t)
: Lemma
  (requires (x `st_fresh_in` p))
  (ensures (x `st_fresh_in` p /\ eval_equiv (st_cons p x ns_f) p' f f'))
  [SMTPat (eval_equiv (st_cons p x ns_f) p' f f')]

let d_esym = eval_equiv_sym

let d_etr = eval_equiv_trans

let d_csym = exec_equiv_sym

let d_ctr = exec_equiv_trans

val d_esub
  (#t: Type0)
  (f f' : exp t)
  (ph ph': sttype)
  (p p': nstype t)
: Lemma
  (requires (
    eval_equiv ph p f f' /\
    included ph' ph /\
    included p p'
  ))
  (ensures (eval_equiv ph' p' f f'))
  [SMTPat (eval_equiv ph' p' f f'); SMTPat (eval_equiv ph p f f')]

val d_csub
  (p1 p2 p1' p2' : sttype)
  (f f' : computation)
: Lemma
  (requires (
    exec_equiv p1 p2 f f' /\
    included p1' p1 /\
    included p2 p2'
  ))
  (ensures (exec_equiv p1' p2' f f'))
  [SMTPat (exec_equiv p1' p2' f f'); SMTPat (exec_equiv p1 p2 f f')]

(* Expressions *)

val d_v
  (x: var)
  (p: sttype)
  (f: nstype int)
: Lemma
  (requires (x `st_fresh_in` p))
  (ensures (x `st_fresh_in` p /\ eval_equiv (st_cons p x f) f (evar x) (evar x)))
  [SMTPat (eval_equiv (st_cons p x f) f (evar x) (evar x))]

val eval_equiv_const
  (#t: Type0)
  (c: t)
  (p: sttype)
: Lemma
  (eval_equiv p (ns_singl c) (const c) (const c))
  [SMTPat (eval_equiv p (ns_singl c) (const c) (const c))]

let d_n = eval_equiv_const #int
let d_b = eval_equiv_const #bool

val d_op
  (#from #to: Type0)
  (op: (from -> from -> Tot to))
  (e1 e1' e2 e2': exp from)
  (ns1 ns2: nstype from)
  (ns: nstype to)
  (phi: sttype)
: Lemma
  (requires (
    eval_equiv phi ns1 e1 e1' /\
    eval_equiv phi ns2 e2 e2' /\
    op_abs op ns1 ns2 ns
  ))
  (ensures (eval_equiv phi ns (eop op e1 e2) (eop op e1' e2')))

(* Commands *)

val d_skip
  (p: sttype)
: Lemma
  (exec_equiv p p skip skip)
  [SMTPat (exec_equiv p p skip skip)]

val d_assign
  (p: sttype)
  (x: var)
  (f f': nstype int)
  (e e' : exp int)
: Lemma
  (requires (
    x `st_fresh_in` p /\
    eval_equiv (st_cons p x f) f' e e'
  ))
  (ensures (
    x `st_fresh_in` p /\
    exec_equiv (st_cons p x f) (st_cons p x f') (assign x e) (assign x e')
  ))
  [SMTPat (exec_equiv (st_cons p x f) (st_cons p x f') (assign x e) (assign x e'))]  

val d_seq
  (p0 p1 p2 : sttype)
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

val d_ifthenelse
  (b b' : exp bool)
  (c1 c1' c2 c2' : computation)
  (phi phi' : sttype)
: Lemma
  (requires (
    eval_equiv phi ns_delta b b' /\
    exec_equiv phi phi' c1 c1' /\
    exec_equiv phi phi' c2 c2'
  ))
  (ensures (exec_equiv phi phi' (ifthenelse b c1 c2) (ifthenelse b' c1' c2')))
  [SMTPat (exec_equiv phi phi' (ifthenelse b c1 c2) (ifthenelse b' c1' c2'))]

val d_whl_terminates
  (b b' : exp bool)
  (c c' : computation)
  (phi : sttype)
  (s0 s0' : heap)
  (fuel: nat)
: Lemma
  (requires (
    eval_equiv phi ns_delta b b' /\
    exec_equiv phi phi c c' /\
    holds phi s0 s0' /\
    fst (reify_computation (while b c) fuel s0) == true
  ))
  (ensures (
    terminates_on (reify_computation (while b' c')) s0'
  ))
  (decreases fuel)

val d_whl
  (b b' : exp bool)
  (c c' : computation)
  (phi : sttype)
: Lemma
  (requires (
    eval_equiv phi ns_delta b b' /\
    exec_equiv phi phi c c'
  ))
  (ensures (exec_equiv phi phi (while b c) (while b' c')))
  [SMTPat (exec_equiv phi phi (while b c) (while b' c'))]

(* 3.1 Basic equations *)

val d_su1
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' c c))
  (ensures (exec_equiv phi phi' (seq skip c) c))
  [SMTPat (exec_equiv phi phi' (seq skip c) c)]

val d_su1'
  (c c' c'' : computation)
  (phi phi' phi'' : sttype)
: Lemma
  (requires (
    exec_equiv phi phi' c skip /\
    exec_equiv phi' phi'' c' c''
  ))
  (ensures (exec_equiv phi phi'' (seq c c') c''))
  [SMTPatOr [
    [SMTPat (exec_equiv phi phi'' (seq c c') c''); SMTPat (exec_equiv phi phi' c skip)];
    [SMTPat (exec_equiv phi phi'' (seq c c') c''); SMTPat (exec_equiv phi' phi'' c' c'')];
    [SMTPat (exec_equiv phi phi' c skip); SMTPat (exec_equiv phi' phi'' c' c'')];
  ]]

val d_su1''
  (c c' c'' : computation)
  (phi phi' phi_ phi'' : sttype)
: Lemma
  (requires (
    exec_equiv phi phi' c skip /\
    included phi' phi_ /\
    exec_equiv phi_ phi'' c' c''
  ))
  (ensures (exec_equiv phi phi'' (seq c c') c''))
  [SMTPat (exec_equiv phi phi' c skip); SMTPat (exec_equiv phi_ phi'' c' c'')]

val d_su2
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' c c))
  (ensures (exec_equiv phi phi' (seq c skip) c))
  [SMTPat (exec_equiv phi phi' (seq c skip) c)]

val d_assoc
  (c1 c2 c3: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq (seq c1 c2) c3)))
  (ensures (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq c1 (seq c2 c3))))
  [SMTPat (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq c1 (seq c2 c3)))]

val d_cc
  (b: exp bool)
  (c1 c2 c3: computation)
  (phi phi' phi'' : sttype)
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
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' (while b c) (while b c)))
  (ensures (exec_equiv phi phi' (while b c) (ifthenelse b (seq c (while b c)) skip)))

val d_lu2
  (b: exp bool)
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' (while b c) (while b c)))
  (ensures (exec_equiv phi phi' (while b c) (while b (seq c (ifthenelse b c skip)))))

val d_sas
  (x: var)
  (phi: sttype)
  (f: nstype int)
: Lemma
  (requires (
    x `st_fresh_in` phi
  ))
  (ensures (
    x `st_fresh_in` phi /\
    exec_equiv (st_cons phi x f) (st_cons phi x f) (assign x (evar x)) skip
  ))
  [SMTPat (exec_equiv (st_cons phi x f) (st_cons phi x f) (assign x (evar x)) skip)]

(* 3.2 Optimizing Transformations *)

(* Dead assignment elimination *)

val d_das
  (x: var)
  (e: exp int)
  (phi: sttype)
  (f: nstype int)
: Lemma
  (requires (x `st_fresh_in` phi))
  (ensures (
    x `st_fresh_in` phi /\
    exec_equiv (st_cons phi x f) (st_cons phi x ns_t) (assign x e) skip
  ))
  [SMTPat (exec_equiv (st_cons phi x f) (st_cons phi x ns_t) (assign x e) skip)]

(* Equivalent branches for conditional *)

val d_bre
  (c1 c2 c0: computation)
  (phi phi' : sttype)
  (b: exp bool)
: Lemma
  (requires (
    exec_equiv phi phi' c1 c0 /\
    exec_equiv phi phi' c2 c0
  ))
  (ensures (exec_equiv phi phi' (ifthenelse b c1 c2) c0))
  [SMTPat (exec_equiv phi phi' (ifthenelse b c1 c2) c0)]

(* Constant folding *)

val d_cf
  (t: Type0)
  (f: exp t)
  (c: t)
  (phi: sttype)
: Lemma
  (requires (eval_equiv phi (ns_singl c) f f))
  (ensures (eval_equiv phi (ns_singl c) f (const c)))
  [SMTPat (eval_equiv phi (ns_singl c) f (const c))]

(* Known branch *)

val d_kb
  (v: bool)
  (b: exp bool)
  (phi: sttype)
  (c1 c2 c' : computation)
  (phi' : sttype)
: Lemma
  (requires (
    eval_equiv phi (ns_singl v) b b /\
    exec_equiv phi phi' (if v then c1 else c2) c'
  ))
  (ensures (exec_equiv phi phi' (ifthenelse b c1 c2) c'))
  [SMTPat (eval_equiv phi (ns_singl v) b b); SMTPat (exec_equiv phi phi' (ifthenelse b c1 c2) c')]

let d_kbt = d_kb true
let d_kbf = d_kb false

(* Dead while *)

val d_dwh
  (b: exp bool)
  (phi: sttype)
  (c: computation)
: Lemma
  (requires (eval_equiv phi (ns_singl false) b b))
  (ensures (exec_equiv phi phi (while b c) skip))
  [SMTPat (exec_equiv phi phi (while b c) skip)]

(* Divergence *)

val d_div
  (b: exp bool)
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (
    eval_equiv phi (ns_singl true) b b /\
    exec_equiv phi phi c c
  ))
  (ensures (
    exec_equiv phi phi' (while b c) (while b c)
  ))
