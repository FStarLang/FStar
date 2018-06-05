module Benton2004.DDCC
include Benton2004

type per (t: Type0) = ( f: rel t { is_per f } )

type nstype (t: Type0) = per t

let ns_f (#t: Type0) : nstype t =
  let f (x y: t) = False in
  Classical.forall_intro_2 (holds_equiv f);
  f

let holds_ns_f (#t: Type0) (x y: t): Lemma
  (holds ns_f x y <==> False)
  [SMTPat (holds ns_f x y)]
= holds_equiv ns_f x y

let ns_t (#t: Type0) : nstype t =
  let f (x y: t) = True in
  Classical.forall_intro_2 (holds_equiv f);
  f

let holds_ns_t (#t: Type0) (x y: t): Lemma
  (holds ns_t x y <==> True)
  [SMTPat (holds ns_t x y)]
= holds_equiv ns_t x y

let ns_singl (#t: Type0) (c: t) : nstype t =
  let f (x y: t) = (x == c /\ y == c) in
  Classical.forall_intro_2 (holds_equiv f);
  f

let holds_ns_singl (#t: Type0) (c: t) (x y: t) : Lemma
  (holds (ns_singl c) x y <==> (x == c /\ y == c))
  [SMTPat (holds (ns_singl c) x y)]
= holds_equiv (ns_singl c) x y

let ns_delta (#t: Type0) : nstype t =
  let f (x y: t) = (x == y) in
  Classical.forall_intro_2 (holds_equiv f);
  f

let holds_ns_delta (#t: Type0) (x y : t) : Lemma
  (holds ns_delta x y <==> x == y)
  [SMTPat (holds ns_delta x y)]
= holds_equiv ns_delta x y

let interpolable_ns_f #t : Lemma (interpolable #t ns_f) = ()
let interpolable_ns_t #t : Lemma (interpolable #t ns_t) = ()
let interpolable_ns_singl #t (c: t) : Lemma (interpolable (ns_singl c)) = ()
let interpolable_ns_delta #t : Lemma (interpolable #t ns_delta) = ()

type sttype = (f: per heap { interpolable f } )

let st_nil: sttype =
  let f (x y : heap) : GTot Type0 = True in
  f

#set-options "--z3rlimit 128 --max_fuel 8 --max_ifuel 8"

let holds_st_nil
  (x y: heap)
: Lemma
  (holds st_nil x y <==> True)
  [SMTPat (holds st_nil x y)]
= Classical.forall_intro_2 (holds_equiv st_nil)

let st_var
  (x: var)
  (v: nstype int)
: GTot sttype
= let f (s1 s2: heap) : GTot Type0 = holds v (sel s1 x) (sel s2 x) in
  Classical.forall_intro_2 (holds_equiv f);
  f

let holds_st_var
  (x: var)
  (v: nstype int)
  (a b: heap)
: Lemma
  (holds (st_var x v) a b <==> holds v (sel a x) (sel b x))
  [SMTPat (holds (st_var x v) a b)]
= holds_equiv (st_var x v) a b

let st_intersect
  (p1 p2: sttype)
: GTot sttype
= intersect p1 p2

let holds_st_intersect
  (ns1 ns2: sttype)
  (x y: heap)
: Lemma
  (holds (st_intersect ns1 ns2) x y <==> (holds ns1 x y /\ holds ns2 x y))
  [SMTPat (holds (st_intersect ns1 ns2) x y)]
= ()

let st_fresh_in
  (x: var)
  (p: sttype)
: GTot Type0
= forall s1 s1' s2 s2' . 
  (holds p s1 s2 /\ (
    forall y . y <> x ==> (sel s1' y == sel s1 y /\ sel s2' y == sel s2 y)
  )) ==>
  holds p s1' s2'

let st_fresh_in_nil
  (x: var)
: Lemma
  (x `st_fresh_in` st_nil)
= ()

let st_cons
  (p: sttype)
  (x: var)
  (v: nstype int)
: Ghost sttype
  (requires (x `st_fresh_in` p))
  (ensures (fun _ -> True))
= st_intersect p (st_var x v)

let st_fresh_in_var
  (x: var)
  (v: nstype int)
  (y: var)
: Lemma
  (requires (y <> x))
  (ensures (y `st_fresh_in` (st_var x v)))
= ()

let st_fresh_in_intersect
  (x: var)
  (p1 p2: sttype)
: Lemma
  (requires (
    x `st_fresh_in` p1 /\
    x `st_fresh_in` p2
  ))
  (ensures (x `st_fresh_in` (st_intersect p1 p2)))
= ()

let st_fresh_in_cons
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
= ()

let subtype_ns_f (#t: Type0) (phi: nstype t) : Lemma
  (included ns_f phi)
= ()

let subtype_ns_singl_delta (#t: Type0) (c: t) : Lemma
  (ns_singl c `included` ns_delta)
= ()

let subtype_ns_t (#t: Type0) (phi: nstype t) : Lemma
  (included phi ns_t)
= ()

let subtype_st_nil (phi: sttype) : Lemma
  (included phi st_nil)
= ()

let subtype_st_f (phi phi' : sttype) (x: var) : Lemma
  (requires (x `st_fresh_in` phi))
  (ensures (x `st_fresh_in` phi /\ included (st_cons phi x ns_f) phi'))
= ()

let subtype_st_t (phi phi' : sttype) (x: var) : Lemma
  (requires (x `st_fresh_in` phi' /\ included phi phi'))
  (ensures (x `st_fresh_in` phi' /\ included phi (st_cons phi' x ns_t)))
= ()

let subtype_st_cons (phi phi' : sttype) (f f' : nstype int) (x: var) : Lemma
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
= ()

abstract
let eval_equiv_reified
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': reified_exp t)
: GTot Type0
= Benton2004.eval_equiv_reified p e f f'

let eval_equiv_reified_elim
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': reified_exp t)
  (s s' : heap)
: Lemma
  (requires (eval_equiv_reified p e f f' /\ holds p s s'))
  (ensures (holds e (fst (f s)) (fst (f' s'))))
= ()  

abstract
let terminates_equiv_reified
  (p : sttype)
  (f f' : reified_computation)
: GTot Type0
= Benton2004.terminates_equiv_reified p f f'

let terminates_equiv_reified_elim
  (p : sttype)
  (f f' : reified_computation)
  (s s' : heap)
: Lemma
  (requires (terminates_equiv_reified p f f' /\ holds p s s'))
  (ensures (terminates_on f s <==> terminates_on f' s'))
= ()

abstract
let exec_equiv_reified
  (p p' : sttype)
  (f f' : reified_computation)
: GTot Type0
= Benton2004.exec_equiv_reified p p' f f'

let exec_equiv_reified_terminates
  (p p' : sttype)
  (f f' : reified_computation)
: Lemma
  (requires (exec_equiv_reified p p' f f'))
  (ensures (terminates_equiv_reified p f f'))
= ()

let exec_equiv_reified_elim
  (p p' : sttype)
  (f f' : reified_computation)
  (s s' : heap)
  (fuel: nat)
: Lemma
  (requires (exec_equiv_reified p p' f f' /\ holds p s s' /\ fst (f fuel s) == true /\ fst (f' fuel s') == true))
  (ensures (holds p' (snd (f fuel s)) (snd (f' fuel s'))))
= ()

let exec_equiv
  (p p' : sttype)
  (f f' : computation)
: GTot Type0
= let f = reify_computation f in
  let f' = reify_computation f' in
  exec_equiv_reified p p' f f'

let eval_equiv_sym
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': exp t)
: Lemma
  (requires (eval_equiv p e f f'))
  (ensures (eval_equiv p e f' f))
= Benton2004.eval_equiv_sym p e f f'

let exec_equiv_sym
  (p p': sttype)
  (f f' : computation)
: Lemma
  (exec_equiv p p' f f' <==> exec_equiv p p' f' f)
  [SMTPat (exec_equiv p p' f f')]
= Benton2004.exec_equiv_sym p p' f f'

let eval_equiv_trans
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f1 f2 f3 : exp t)
: Lemma
  (requires (eval_equiv p e f1 f2 /\ eval_equiv p e f2 f3))
  (ensures (eval_equiv p e f1 f3))
= Benton2004.eval_equiv_trans p e f1 f2 f3

let exec_equiv_reified_trans
  (p p': sttype)
  (f1 f2 f3 : reified_computation)
: Lemma
  (requires (exec_equiv_reified p p' f1 f2 /\ exec_equiv_reified p p' f2 f3))
  (ensures (exec_equiv_reified p p' f1 f3))
= Benton2004.exec_equiv_reified_trans p p' f1 f2 f3

let exec_equiv_trans
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
= let z1 = reify_computation c1 in
  let z2 = reify_computation c2 in
  let z3 = reify_computation c3 in
  exec_equiv_reified_trans p p' z1 z2 z3

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

let d_ct
  (c c' : computation)
  (p p' : sttype)
  (x: var)
: Lemma
  (requires (x `st_fresh_in` p))
  (ensures (x `st_fresh_in` p /\ exec_equiv (st_cons p x ns_f) p' c c'))
  [SMTPat (exec_equiv (st_cons p x ns_f) p' c c')]
= ()

let d_et1
  (#t: Type0)
  (f f' : exp t)
  (p: sttype)
: Lemma
  (eval_equiv p ns_t f f')
  [SMTPat (eval_equiv p ns_t f f')]
= ()

let d_et2
  (#t: Type0)
  (f f' : exp t)
  (p: sttype)
  (x: var)
  (p' : nstype t)
: Lemma
  (requires (x `st_fresh_in` p))
  (ensures (x `st_fresh_in` p /\ eval_equiv (st_cons p x ns_f) p' f f'))
  [SMTPat (eval_equiv (st_cons p x ns_f) p' f f')]
= ()

let d_esym = eval_equiv_sym

let d_etr = eval_equiv_trans

let d_csym = exec_equiv_sym

let d_ctr = exec_equiv_trans

let d_esub
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
= Benton2004.d_esub f f' ph ph' p p'

let d_csub
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
= Benton2004.d_csub p1 p2 p1' p2' f f'

(* Expressions *)

let d_v
  (x: var)
  (p: sttype)
  (f: nstype int)
: Lemma
  (requires (x `st_fresh_in` p))
  (ensures (x `st_fresh_in` p /\ eval_equiv (st_cons p x f) f (evar x) (evar x)))
  [SMTPat (eval_equiv (st_cons p x f) f (evar x) (evar x))]
= ()

let eval_equiv_const
  (#t: Type0)
  (c: t)
  (p: sttype)
: Lemma
  (eval_equiv p (ns_singl c) (const c) (const c))
  [SMTPat (eval_equiv p (ns_singl c) (const c) (const c))]
= ()

let d_n = eval_equiv_const #int
let d_b = eval_equiv_const #bool

let d_op
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
= Benton2004.d_op op e1 e1' e2 e2' ns1 ns2 ns phi

(* Commands *)

let d_skip
  (p: sttype)
: Lemma
  (exec_equiv p p skip skip)
  [SMTPat (exec_equiv p p skip skip)]
= Benton2004.d_skip p

let d_assign
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
= ()

let d_seq
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
= Benton2004.d_seq p0 p1 p2 c01 c01' c12 c12'

#set-options "--z3rlimit 1024"

let d_ifthenelse
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
= ()

let rec d_whl_terminates
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
= let fc = reify_computation c in
  let fc' = reify_computation c' in
  let f = reify_computation (while b c) in
  let f' = reify_computation (while b' c') in
  let e = fst (reify_exp b s0) in
  assert (e == fst (reify_exp b' s0'));
  if e
  then begin
    assert (terminates_on fc' s0');
    let g
      (fuel0: nat)
    : Lemma
      (requires (fst (fc' fuel0 s0') == true))
      (ensures (terminates_on f' s0'))
    = let fuel1 = fuel + fuel0 in
      assert (fc' fuel1 s0' == fc' fuel0 s0');
      assert  (fc fuel1 s0 == fc fuel s0);
      let s1 = snd (fc fuel1 s0) in
      let s1' = snd (fc' fuel1 s0') in
      assert (holds phi s1 s1');
      assert (f fuel s0 == f (fuel - 1) s1);
      assert (f' fuel1 s0' == f' (fuel1 - 1) s1');
      d_whl_terminates b b' c c' phi s1 s1' (fuel - 1);
      let g'
        (fuel2 : nat)
      : Lemma
        (requires (fst (f' fuel2 s1') == true))
        (ensures (terminates_on f' s0'))
      = let fuel3 = fuel1 + fuel2 + 1 in
        assert (fc' fuel3 s0' == fc' fuel1 s0');
        assert (f' fuel3 s0' == f' (fuel3 - 1) s1')
      in
      Classical.forall_intro (Classical.move_requires g')
    in
    Classical.forall_intro (Classical.move_requires g)
  end else
    assert (f' fuel s0' == (true, s0'))

let d_whl
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
= let eb = reify_exp b in
  let eb' = reify_exp b' in
  let eb_rel : squash (eval_equiv_reified phi ns_delta eb eb') = () in
  let fc = reify_computation c in
  let fc' = reify_computation c' in
  let c_rel : squash (exec_equiv_reified phi phi fc fc') = () in
  let f = reify_computation (while b c) in
  let f' = reify_computation (while b' c') in
  let prf1
    (s0 s0' : heap)
  : Lemma
    (requires (holds phi s0 s0'))
    (ensures (terminates_on f s0 <==> terminates_on f' s0'))
  = exec_equiv_sym phi phi c c' ;
    eval_equiv_sym phi ns_delta b b' ;
    Classical.forall_intro (Classical.move_requires (d_whl_terminates b b' c c' phi s0 s0'));
    Classical.forall_intro (Classical.move_requires (d_whl_terminates b' b c' c phi s0' s0))
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf1 x));
  let rec prf2
    (fuel: nat)
    (s0 s0' : heap)
  : Lemma
    (requires (
      holds phi s0 s0' /\
      fst (f fuel s0) == true /\
      fst (f' fuel s0') == true
    ))
    (ensures (
      holds phi (snd (f fuel s0)) (snd (f' fuel s0'))
    ))
    (decreases fuel)
  = let e = fst (eb s0) in
    let e' = fst (eb' s0') in
    assert (holds phi s0 s0');
    let e_rel : squash (holds ns_delta e e') =
      eb_rel;
      ()
    in
    assert (e == fst (eb' s0'));
    if e
    then begin
      let k = fc fuel s0 in
      let k' = fc' fuel s0' in
      let s1 = snd k in
      let s1' = snd k' in
      let s_rel : squash (holds phi s1 s1') =
        c_rel;
        ()
      in
      assert (f fuel s0 == f (fuel - 1) s1);
      assert (f' fuel s0' == f' (fuel - 1) s1');
      prf2 (fuel - 1) s1 s1'
    end else ()
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (prf2 x y))

(* 3.1 Basic equations *)

let d_su1
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' c c))
  (ensures (exec_equiv phi phi' (seq skip c) c))
  [SMTPat (exec_equiv phi phi' (seq skip c) c)]
= Benton2004.d_su1 c phi phi'

let d_su1'
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
= Benton2004.d_su1' c c' c'' phi phi' phi''

let d_su1''
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
= d_su1' c c' c'' phi phi_ phi''

let d_su2
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' c c))
  (ensures (exec_equiv phi phi' (seq c skip) c))
  [SMTPat (exec_equiv phi phi' (seq c skip) c)]
= Benton2004.d_su2 c phi phi'

let d_assoc
  (c1 c2 c3: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq (seq c1 c2) c3)))
  (ensures (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq c1 (seq c2 c3))))
  [SMTPat (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq c1 (seq c2 c3)))]
= Benton2004.d_assoc c1 c2 c3 phi phi'

let d_cc
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
= Benton2004.d_cc b c1 c2 c3 phi phi' phi''

let d_lu1
  (b: exp bool)
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' (while b c) (while b c)))
  (ensures (exec_equiv phi phi' (while b c) (ifthenelse b (seq c (while b c)) skip)))
= Benton2004.d_lu1 b c phi phi'

let d_lu2
  (b: exp bool)
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' (while b c) (while b c)))
  (ensures (exec_equiv phi phi' (while b c) (while b (seq c (ifthenelse b c skip)))))
= Benton2004.d_lu2 b c phi phi'

let d_sas
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
= ()

(* 3.2 Optimizing Transformations *)

(* Dead assignment elimination *)

let d_das
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
= assert (Benton2004.mention (reify_exp e)) // TODO: WHY is this necessary?

(* Equivalent branches for conditional *)

let d_bre
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
= Benton2004.d_bre c1 c2 c0 phi phi' b

(* Constant folding *)

let d_cf
  (t: Type0)
  (f: exp t)
  (c: t)
  (phi: sttype)
: Lemma
  (requires (eval_equiv phi (ns_singl c) f f))
  (ensures (eval_equiv phi (ns_singl c) f (const c)))
  [SMTPat (eval_equiv phi (ns_singl c) f (const c))]
= ()

(* Known branch *)

let d_kb
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
= ()

let d_kbt = d_kb true
let d_kbf = d_kb false

(* Dead while *)

let d_dwh
  (b: exp bool)
  (phi: sttype)
  (c: computation)
: Lemma
  (requires (eval_equiv phi (ns_singl false) b b))
  (ensures (exec_equiv phi phi (while b c) skip))
  [SMTPat (exec_equiv phi phi (while b c) skip)]
= ()

(* Divergence *)

let d_div
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
= let f = reify_computation (while b c) in
  let e = reify_exp b in
  let e_rel : squash (eval_equiv phi (ns_singl true) b b) = () in
  let fc = reify_computation c in
  let f_rel : squash (exec_equiv_reified phi phi fc fc) = () in
  let rec prf
    (s0 s0' : heap)
    (fuel: nat)
  : Lemma
    (requires (holds phi s0 s0'))
    (ensures (fst (f fuel s0) == false))
    (decreases fuel)
  = let _ : squash (e s0 == (true, s0) /\ e s0' == (true, s0')) =
      e_rel;
      ()
    in
    let k = fc fuel s0 in
    if fst k
    then
      let s1 = snd k in
      if fuel = 0
      then assert (fst (f fuel s0) == false)
      else begin
        assert (terminates_on fc s0);
        assert (terminates_on fc s0');
        let g
          (fuel' : nat)
        : Lemma
          (requires (fst (fc fuel' s0') == true))
          (ensures (fst (f fuel s0) == false))
        = let s1' = snd (fc fuel' s0') in
          assert (fc (fuel + fuel') s0 == fc fuel s0);
          assert (fc (fuel + fuel') s0' == fc fuel' s0');
          assert (f fuel s0 == f (fuel - 1) s1);
          let _ : squash (holds phi s1 s1') =
            f_rel;
            ()
          in
          prf s1 s1' (fuel - 1)
        in
        Classical.forall_intro (Classical.move_requires g)
    end else
      assert (fst (f fuel s0) == false)
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (prf x y))
