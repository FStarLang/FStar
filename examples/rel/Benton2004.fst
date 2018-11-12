module Benton2004

include Benton2004.Aux
include FStar.DM4F.Heap.IntStoreFixed
include FStar.DM4F.IntStoreFixed

type reified_raw_computation =
  (f: (
    nat ->
    heap ->
    GTot (bool * heap)
  ))

let fuel_monotonic
  (f: reified_raw_computation)
: GTot Type0
= forall (fuel fuel' : nat) h . (
    fuel <= fuel' /\
    fst (f fuel h) == true
  ) ==> (
    f fuel' h == f fuel h
  )

type reified_computation =
  (f: reified_raw_computation { fuel_monotonic f } )

type raw_computation =
  (f: ((fuel: nat) -> ISNull bool))

let reify_raw_computation (f : raw_computation) : reified_raw_computation =
  fun n h -> reify (f n) h

type computation =
  (f: raw_computation { fuel_monotonic (reify_raw_computation f) })

let reify_computation (c: computation) : GTot reified_computation =
  let f n = reify (c n) in
  f

let skip : computation = let f (fuel: nat) : ISNull bool = true in f

type var = id

#set-options "--z3rlimit 128 --max_fuel 8 --max_ifuel 8"

type exp (t: Type0) : Type0 = unit -> IntStore t (requires (fun _ -> True)) (ensures (fun h _ h' -> h' == h))
let reified_exp (t: Type0) : Tot Type0 = (h: heap) -> Ghost (t * heap) (requires True) (ensures (fun rh -> snd rh == h))

let reify_exp (#t: Type0) (e: exp t) : GTot (reified_exp t) =
  let f = reify (e ()) in
  f

let const (#t: Type0) (v: t) : Tot (exp t) = fun _ -> v

let evar (x: var) : Tot (exp int) = fun _ -> read x

let assign (r: var) (n: exp int) : Tot computation =
  let g _ : ISNull bool =
    let n = n () in
    write r n;
    true
  in
  g

let ifthenelse (b: exp bool) (c1 c2: computation) : Tot computation =
  let g (fuel: nat) : ISNull bool =
    if b () then c1 fuel else c2 fuel
  in
  assert (
    let f : reified_raw_computation =
      let h fuel = reify (g fuel) in h
    in
    let f1 = reify_computation c1 in
    let f2 = reify_computation c2 in
    let e = reify_exp b in (
    (forall fuel h . fst (e h) == true ==> f fuel h == f1 fuel h) /\
    (forall fuel h . fst (e h) == false ==> f fuel h == f2 fuel h)
  ));
  g

let seq (c1 c2: computation) : Tot computation =
  let g (fuel: nat) : ISNull bool =
    if c1 fuel then c2 fuel else false
  in
  assert (
    let f : reified_raw_computation =
      let h fuel = reify (g fuel) in h
    in
    let f1 = reify_computation c1 in
    let f2 = reify_computation c2 in
    (forall fuel h . fst (f fuel h) == true <==> (fst (f1 fuel h) == true /\ fst (f2 fuel (snd (f1 fuel h))) == true)) /\
    (forall fuel h . fst (f fuel h) == true ==> f fuel h == f2 fuel (snd (f1 fuel h)))
  );
  g

let rec while_raw (b: exp bool) (c: computation) (fuel: nat) : ISNull bool (decreases fuel) =
  if b ()
  then
    if c fuel
    then
      if fuel = 0
      then false
      else while_raw b c (fuel - 1)
    else false
  else true

let fuel_monotonic_while
  (b: exp bool)
  (c: computation)
  (f: reified_raw_computation)
: Lemma
  (requires (forall fuel h . f fuel h == reify (while_raw b c fuel) h))
  (ensures (
    fuel_monotonic f
  ))
= let f (fuel: nat) = reify (while_raw b c fuel) in
  let fb = reify_exp b in
  let fc = reify_computation c in
  let rec prf
    (fuel fuel' : nat)
    (h: heap)
  : Lemma
    (requires (
      fuel <= fuel' /\
      fst (f fuel h) == true
    ))
    (ensures (f fuel' h == f fuel h))
    (decreases fuel)
  = let (_, h1) = f fuel h in
    let (_, h1') = f fuel' h in
    let (b0, _) = fb h in
    if b0
    then begin
      let (_, h') = fc fuel h in
      prf (fuel - 1) (fuel' - 1) h'
    end else ()
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (prf x y))

let while (b: exp bool) (c: computation) : Tot computation =
  let f : raw_computation = while_raw b c in
  let g = reify_raw_computation f in
  fuel_monotonic_while b c g;
  f

(* Termination *)

let terminates_on (f: reified_computation) (h: heap) : GTot Type0 =
  exists fuel . fst (f fuel h) == true

let included
  (#t: Type0)
  (r1 r2: rel t)
: GTot Type0
= forall x y . holds r1 x y ==> holds r2 x y

let is_per (#t: Type0) (f: rel t) : GTot Type0 =
  (forall x1 x2 . f x1 x2 <==> f x2 x1) /\
  (forall x1 x2 x3 . (f x1 x2 /\ f x2 x3) ==> f x1 x3)

let is_per_holds_sym
  (#t: Type0)
  (p: rel t)
  (s s' : t)
: Lemma
  (requires (is_per p))
  (ensures (holds p s s' <==> holds p s' s))
  [SMTPat (holds p s s')]
= holds_equiv p s s';
  holds_equiv p s' s

let per_holds_trans
  (#t: Type0)
  (f: rel t)
  (x1 x2 x3: t)
: Lemma
  (requires (is_per f /\ holds f x1 x2 /\ holds f x2 x3))
  (ensures (holds f x1 x3))
  [SMTPatOr [
    [SMTPat (holds f x1 x2); SMTPat (holds f x2 x3)];
    [SMTPat (holds f x1 x2); SMTPat (holds f x1 x3)];
    [SMTPat (holds f x2 x3); SMTPat (holds f x1 x3)];
  ]]
= holds_equiv f x1 x2;
  holds_equiv f x2 x3;
  holds_equiv f x1 x3

let intersect
  (#t: Type0)
  (ns1 ns2: rel t)
: GTot (rel t)
= let f x y = holds ns1 x y /\ holds ns2 x y in
  Classical.forall_intro_2 (holds_equiv f);
  f

let holds_intersect
  (#t: Type0)
  (ns1 ns2: rel t)
  (x y: t)
: Lemma
  (holds (intersect ns1 ns2) x y <==> (holds ns1 x y /\ holds ns2 x y))
  [SMTPat (holds (intersect ns1 ns2) x y)]
= holds_equiv (intersect ns1 ns2) x y

type nstype (t: Type0) = rel t

let interpolable
  (#t: Type0)
  (f: rel t)
: GTot Type0
= forall (x1 x3 : t) . f x1 x3 ==> (exists x2 . f x1 x2 /\ f x2 x3)

let interpolable_elim
  (#t: Type0)
  (f: rel t)
  (x1 x3: t)
: Lemma
  (requires (interpolable f /\ holds f x1 x3))
  (ensures (exists x2 . holds f x1 x2 /\ holds f x2 x3))
= Classical.forall_intro_2 (holds_equiv f)

type sttype = (f: rel heap)

(* 3.1.3. Judgements *)

let eval_equiv_reified
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': reified_exp t)
: GTot Type0
= forall (s s' : heap) .
  holds p s s' ==> holds e (fst (f s)) (fst (f' s'))

let eval_equiv
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': exp t)
: GTot Type0
= let f = reify_exp f in
  let f' = reify_exp f' in
  eval_equiv_reified p e f f'

let terminates_equiv_reified
  (p : sttype)
  (f f' : reified_computation)
: GTot Type0
= forall s s' . holds p s s' ==> (terminates_on f s <==> terminates_on f' s')

let terminates_equiv_reified_sym
  (p : sttype)
  (f f' : reified_computation)
: Lemma
  (requires (terminates_equiv_reified p f f' /\ is_per p))
  (ensures (terminates_equiv_reified p f' f))
= ()

let exec_equiv_reified
  (p p' : sttype)
  (f f' : reified_computation)
: GTot Type0
= terminates_equiv_reified p f f' /\
  (forall (s s' : heap) (fuel: nat) .
    (holds p s s' /\ fst (f fuel s) == true /\ fst (f' fuel s') == true) ==> holds p' (snd (f fuel s)) (snd (f' fuel s')))

let exec_equiv
  (p p' : sttype)
  (f f' : computation)
: GTot Type0
= let f = reify_computation f in
  let f' = reify_computation f' in
  exec_equiv_reified p p' f f'

(* Flipping a relation *)

let flip (#t: Type0) (r: rel t) : Tot (rel t) =
  let g x y = holds r y x in
  g

let holds_flip (#t: Type0) (r: rel t) : Lemma
  (forall x y . holds (flip r) x y <==> holds r y x)
= Classical.forall_intro_2 (holds_equiv (flip r))

let holds_flip' (#t: Type0) (r: rel t) x y : Lemma
  (ensures (holds (flip r) x y <==> holds r y x))
  [SMTPat (holds (flip r) x y)]
= holds_flip r

let eval_equiv_flip
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': exp t)
: Lemma
  (eval_equiv (flip p) (flip e) f' f <==> eval_equiv p e f f')
  [SMTPat (eval_equiv (flip p) (flip e) f' f)]
= holds_flip p;
  holds_flip e

let exec_equiv_flip
  (p p': sttype)
  (f f' : computation)
: Lemma
  (exec_equiv (flip p) (flip p') f f' <==> exec_equiv p p' f' f)
  [SMTPat (exec_equiv (flip p) (flip p') f f')]
= holds_flip p;
  holds_flip p'

(* Lemma 2 *)

let eval_equiv_sym
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': exp t)
: Lemma
  (requires (is_per p /\ is_per e /\ eval_equiv p e f f'))
  (ensures (eval_equiv p e f' f))
= ()

let exec_equiv_sym
  (p p': sttype)
  (f f' : computation)
: Lemma
  (requires (is_per p /\ is_per p'))
  (ensures (exec_equiv p p' f f' <==> exec_equiv p p' f' f))
  [SMTPat (exec_equiv p p' f f')]
= ()

let eval_equiv_trans
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f1 f2 f3 : exp t)
: Lemma
  (requires (is_per e /\ interpolable p /\ eval_equiv p e f1 f2 /\ eval_equiv p e f2 f3))
  (ensures (eval_equiv p e f1 f3))
= Classical.forall_intro_2 (fun x -> Classical.move_requires (interpolable_elim p x))

let exec_equiv_reified_trans
  (p p': sttype)
  (f1 f2 f3 : reified_computation)
: Lemma
  (requires (is_per p' /\ interpolable p /\ exec_equiv_reified p p' f1 f2 /\ exec_equiv_reified p p' f2 f3))
  (ensures (exec_equiv_reified p p' f1 f3))
= let prf1
    (s1 s3 : heap)
  : Lemma
    (requires (holds p s1 s3))
    (ensures (terminates_on f1 s1 <==> terminates_on f3 s3))
  = interpolable_elim p s1 s3
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf1 x));
  let prf2
    (s1 s3: heap)
    (fuel: nat)
  : Lemma
    (requires (holds p s1 s3 /\ fst (f1 fuel s1) == true /\ fst (f3 fuel s3) == true))
    (ensures (holds p' (snd (f1 fuel s1)) (snd (f3 fuel s3))))
  = interpolable_elim p s1 s3;
    let g
      (s2: heap)
    : Lemma
      (requires (holds p s1 s2 /\ holds p s2 s3))
      (ensures (holds p' (snd (f1 fuel s1)) (snd (f3 fuel s3))))
    = let g'
        (fuel' : nat)
      : Lemma
        (requires (fst (f2 fuel' s2) == true))
        (ensures (holds p' (snd (f1 fuel s1)) (snd (f3 fuel s3))))
      = assert (f1 (fuel + fuel') s1 == f1 fuel s1);
        assert (f2 (fuel + fuel') s2 == f2 fuel' s2);
        assert (f3 (fuel + fuel') s3 == f3 fuel s3);
        assert (holds p' (snd (f1 (fuel + fuel') s1)) (snd (f2 (fuel + fuel') s2)))
      in
      Classical.forall_intro (Classical.move_requires g')
    in
    Classical.forall_intro (Classical.move_requires g)
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (prf2 x y))

let exec_equiv_trans
  (p p' : sttype)
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
    [SMTPat (exec_equiv p p' c2 c3); SMTPat (exec_equiv p p' c1 c3)];
  ]]
= let z1 = reify_computation c1 in
  let z2 = reify_computation c2 in
  let z3 = reify_computation c3 in
  exec_equiv_reified_trans p p' z1 z2 z3

(* Figure 2. Theorem 1. *)

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
= ()

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
= ()

let eop
  (#from #to: Type0)
  (op: (from -> from -> Tot to))
  (e1 e2: exp from)
: Tot (exp to)
= fun () -> (e1 ()) `op` (e2 ())

(* Definition 1 *)

let op_abs
  (#from #to: Type0)
  (op: (from -> from -> Tot to))
  (ns1 ns2: nstype from)
  (ns: nstype to)
: GTot Type0
= forall x x' y y' .
  (holds ns1 x x' /\ holds ns2 y y') ==>
  holds ns (op x y) (op x' y')

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
= ()

(* Commands *)

let d_skip
  (p: sttype)
: Lemma
  (exec_equiv p p skip skip)
  [SMTPat (exec_equiv p p skip skip)]
= ()

#set-options "--z3rlimit 1024"

let d_seq_terminates
  (p0 p1 p2 : sttype)
  (c01 c01' c12 c12' : computation)
  (s0 s0': heap)
: Lemma
  (requires (
    exec_equiv p0 p1 c01 c01' /\
    exec_equiv p1 p2 c12 c12' /\
    holds p0 s0 s0' /\
    terminates_on (reify_computation (seq c01 c12)) s0
  ))
  (ensures (
    terminates_on (reify_computation (seq c01' c12')) s0'
  ))
= let f01 = reify_computation c01 in
  let f01' = reify_computation c01' in
  let f12 = reify_computation c12 in
  let f12' = reify_computation c12' in
  let f = reify_computation (seq c01 c12) in
  let f' = reify_computation (seq c01' c12') in
  let g
    (fuel: nat)
  : Lemma
    (requires (fst (f01 fuel s0) == true /\ fst (f01' fuel s0') == true))
    (ensures (terminates_on f' s0'))
  = let k01 = f01 fuel s0 in
    let k01' = f01' fuel s0' in
    let s1 = snd k01 in
    let s1' = snd k01' in
    assert (holds p1 s1 s1');
    assert (terminates_on f12' s1');
    let g'
      (fuel' : nat)
    : Lemma
      (requires (fst (f12' fuel' s1') == true))
      (ensures (terminates_on f' s0'))
    = assert (f01' (fuel + fuel') s0' == (true, s1'));
      assert (f12' (fuel + fuel') s1' == f12' fuel' s1');
      assert (f' (fuel + fuel') s0' == f12' (fuel + fuel') s1');
      assert (fst (f' (fuel + fuel') s0') == true)
    in
    Classical.forall_intro (Classical.move_requires g')
  in
  Classical.forall_intro (Classical.move_requires g)

(* We now need to prove the converse, too, because p is not necessarily a PER. *)

let d_seq_terminates_recip
  (p0 p1 p2 : sttype)
  (c01 c01' c12 c12' : computation)
  (s0 s0': heap)
: Lemma
  (requires (
    exec_equiv p0 p1 c01 c01' /\
    exec_equiv p1 p2 c12 c12' /\
    holds p0 s0 s0' /\
    terminates_on (reify_computation (seq c01' c12')) s0'
  ))
  (ensures (
    terminates_on (reify_computation (seq c01 c12)) s0
  ))
= holds_flip' p0 s0' s0;
  d_seq_terminates (flip p0) (flip p1) (flip p2) c01' c01 c12' c12 s0' s0

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
    [SMTPat (exec_equiv p0 p1 c01 c01'); SMTPat (exec_equiv p1 p2 c12 c12')];
    [SMTPat (exec_equiv p0 p1 c01 c01'); SMTPat (exec_equiv p0 p2 (seq c01 c12) (seq c01' c12'))];
    [SMTPat (exec_equiv p1 p2 c12 c12'); SMTPat (exec_equiv p0 p2 (seq c01 c12) (seq c01' c12'))];
  ]]
= let f01 = reify_computation c01 in
  let f01' = reify_computation c01' in
  let f12 = reify_computation c12 in
  let f12' = reify_computation c12' in
  let f = reify_computation (seq c01 c12) in
  let f' = reify_computation (seq c01' c12') in
  let prf1
    (s0 s0' : heap)
  : Lemma
    (requires (holds p0 s0 s0'))
    (ensures (terminates_on f s0 <==> terminates_on f' s0'))
  = Classical.move_requires (d_seq_terminates p0 p1 p2 c01 c01' c12 c12' s0) s0';
    Classical.move_requires (d_seq_terminates_recip p0 p1 p2 c01 c01' c12 c12' s0) s0'
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf1 x));
  let prf2
    (s0 s0': heap)
    (fuel: nat)
  : Lemma
    (requires (holds p0 s0 s0' /\ fst (f fuel s0) == true /\ fst (f' fuel s0') == true))
    (ensures (holds p2 (snd (f fuel s0)) (snd (f' fuel s0'))))
  = let k01 = f01 fuel s0 in
    let k01' = f01' fuel s0' in
    let s1 = snd k01 in
    let s1' = snd k01' in
    assert (holds p1 s1 s1')
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
= ()

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
    [SMTPat (exec_equiv phi phi' c skip); SMTPat (exec_equiv phi phi'' (seq c c') c'')];
    [SMTPat (exec_equiv phi' phi'' c' c''); SMTPat (exec_equiv phi phi'' (seq c c') c'')];
    [SMTPat (exec_equiv phi phi' c skip); SMTPat (exec_equiv phi' phi'' c' c'')];
  ]]
= assert (exec_equiv phi phi'' (seq c c') (seq skip c'')) ;
  let f1 = reify_computation (seq skip c'') in
  let f2 = reify_computation c'' in
  assert (forall fuel s0 . f1 fuel s0 == f2 fuel s0)
  // NOTE: this rule is NOT a consequence of d_su1 + d_seq + d_ctr

let d_su2
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' c c))
  (ensures (exec_equiv phi phi' (seq c skip) c))
  [SMTPat (exec_equiv phi phi' (seq c skip) c)]
= ()

let d_assoc
  (c1 c2 c3: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq (seq c1 c2) c3)))
  (ensures (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq c1 (seq c2 c3))))
  [SMTPat (exec_equiv phi phi' (seq (seq c1 c2) c3) (seq c1 (seq c2 c3)))]
= let fl = reify_computation (seq (seq c1 c2) c3) in
  let fr = reify_computation (seq c1 (seq c2 c3)) in
  assert (forall s0 fuel . fl s0 fuel == fr s0 fuel)

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
    [SMTPat (exec_equiv phi phi' (ifthenelse b c1 c2) (ifthenelse b c1 c2)); SMTPat (exec_equiv phi' phi'' c3 c3)];
    [SMTPat (exec_equiv phi phi' (ifthenelse b c1 c2) (ifthenelse b c1 c2)); SMTPat (exec_equiv phi phi'' (seq (ifthenelse b c1 c2) c3) (ifthenelse b (seq c1 c3) (seq c2 c3)))];
    [SMTPat (exec_equiv phi' phi'' c3 c3); SMTPat (exec_equiv phi phi'' (seq (ifthenelse b c1 c2) c3) (ifthenelse b (seq c1 c3) (seq c2 c3)))];
  ]]
= let fl = reify_computation (seq (ifthenelse b c1 c2) c3) in
  let fr = reify_computation (ifthenelse b (seq c1 c3) (seq c2 c3)) in
  assert (forall s0 fuel . fl s0 fuel == fr s0 fuel);
  assert (exec_equiv phi phi'' (seq (ifthenelse b c1 c2) c3) (seq (ifthenelse b c1 c2) c3))

let d_lu1
  (b: exp bool)
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' (while b c) (while b c)))
  (ensures (exec_equiv phi phi' (while b c) (ifthenelse b (seq c (while b c)) skip)))
= let fc = reify_computation c in
  let fl = reify_computation (while b c) in
  let fr = reify_computation (ifthenelse b (seq c (while b c)) skip) in
  let eb = reify_exp b in
  let prf1
    (s0: heap)
    (fuel: nat)
  : Lemma
    (requires (fst (fl fuel s0) == true))
    (ensures (fr fuel s0 == fl fuel s0))
  = if fst (eb s0)
    then begin
      let s1 = snd (fc fuel s0) in
      assert (fl fuel s0 == fl (fuel - 1) s1);
      assert (fr fuel s0 == fl fuel s1)
    end else ()
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf1 x));
  assert (forall s0 fuel . fst (fr fuel s0) == true ==> fl (fuel + 1) s0 == fr fuel s0)

let d_lu2
  (b: exp bool)
  (c: computation)
  (phi phi' : sttype)
: Lemma
  (requires (exec_equiv phi phi' (while b c) (while b c)))
  (ensures (exec_equiv phi phi' (while b c) (while b (seq c (ifthenelse b c skip)))))
= let fc = reify_computation c in
  let fl = reify_computation (while b c) in
  let fr = reify_computation (while b (seq c (ifthenelse b c skip))) in
  let eb = reify_exp b in
  let rec prf1
    (s0: heap)
    (fuel: nat)
  : Lemma
    (requires (fst (fl fuel s0) == true))
    (ensures (fr fuel s0 == fl fuel s0))
    (decreases fuel)
  = if fst (eb s0)
    then begin
      let s1 = snd (fc fuel s0) in
      assert (fl fuel s0 == fl (fuel - 1) s1);
      if fst (eb s1)
      then begin
        let s2 = snd (fc (fuel - 1) s1) in
        assert (fl fuel s0 == fl (fuel - 2) s2);
        assert (fc fuel s1 == fc (fuel - 1) s1);
        assert (fr fuel s0 == fr (fuel - 1) s2);
        prf1 s2 (fuel - 2);
        assert (fr (fuel - 1) s2 == fr (fuel - 2) s2)
      end else ()
    end else ()
  in
  let rec prf2
    (s0: heap)
    (fuel: nat)
  : Lemma
    (requires (fst (fr fuel s0) == true))
    (ensures (fl (fuel + fuel) s0 == fr fuel s0))
    (decreases fuel)
  = if fst (eb s0)
    then begin
      let s1 = snd (fc fuel s0) in
      if fst (eb s1)
      then begin
        let s2 = snd (fc fuel s1) in
        assert (fr fuel s0 == fr (fuel - 1) s2);
        prf2 s2 (fuel - 1);
        assert (fl (fuel + fuel) s0 == fl (fuel - 1 + fuel - 1) s2)
      end else ()
    end else ()
  in
  let prf1' (s0:heap) (fuel:nat) :Lemma (fst (fl fuel s0) == true ==> fr fuel s0 == fl fuel s0)
    = Classical.move_requires (prf1 s0) fuel
  in
  let prf2' (s0:heap) (fuel:nat) :Lemma (fst (fr fuel s0) == true ==> fl (fuel + fuel) s0 == fr fuel s0)
    = Classical.move_requires (prf2 s0) fuel
  in
  Classical.forall_intro_2 prf1';  //AR: same pattern as in Pointer, see the comment there
  Classical.forall_intro_2 prf2'

(* 3.2 Optimizing Transformations *)

(* Equivalent branches for conditional *)

(* FIXME: the following rule is WRONG, because the relations are not necessarily reflexive.
let d_bre
  (c1 c2: computation)
  (phi phi' : sttype)
  (b: exp bool)
: Lemma
  (requires (exec_equiv phi phi' c1 c2))
  (ensures (exec_equiv phi phi' (ifthenelse b c1 c2) c1))
*)

let mention (#a:Type) (x:a) = True

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
= assert (mention (reify_exp b)) //Just mentioning `reify_exp b` triggers the necessary reduction; not sure exactly why though
