module Benton2004

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed

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

type computation =
  (f: raw_computation { 
    let g n = reify (f n) in
    fuel_monotonic g
  })

let reify_computation (c: computation) : Tot reified_computation =
  let f n = reify (c n) in
  f

let skip : computation = let f (fuel: nat) : ISNull bool = true in f

type var = id

#set-options "--z3rlimit 128 --max_fuel 32 --max_ifuel 32"

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

(* FIXME: WHY WHY WHY does this NOT work?
<<
let ifthenelse (b: exp bool) (c1 c2: computation) : Tot computation =
  let g (fuel: nat) : ISNull bool =
    if b () then c1 fuel else c2 fuel
  in
  g
>>
*)

let ifthenelse_raw (b: exp bool) (c1 c2: computation) (fuel: nat) : ISNull bool =
  if b () then c1 fuel else c2 fuel

let reified_ifthenelse_raw
  (b: exp bool)
  (c1 c2: computation)
  (fuel: nat)
  (h: heap)
: GTot (bool * heap)
= reify (ifthenelse_raw b c1 c2 fuel) h

let fuel_monotonic_ifthenelse
  (b: exp bool)
  (c1 c2: computation)
  (f: reified_raw_computation)
: Lemma
  (requires (forall fuel h . f fuel h == reified_ifthenelse_raw b c1 c2 fuel h))
  (ensures (
    fuel_monotonic f
  ))
= let fb = reify (b ()) in
  let fc1 fuel = reify (c1 fuel) in
  let fc2 fuel = reify (c2 fuel) in
  let g
    (fuel: nat)
    (h: heap)
  : Lemma (
      f fuel h == (
      if fst (fb h) then fc1 fuel h else fc2 fuel h
    ))
  = assert (
      f fuel h == (
      if fst (fb h) then fc1 fuel h else fc2 fuel h
    ))
  in
  Classical.forall_intro_2 g

let ifthenelse (b: exp bool) (c1 c2: computation) : Tot computation =
  let f : raw_computation = ifthenelse_raw b c1 c2 in
  let g (fuel: nat) (h: heap) : GTot (bool * heap) = reify (f fuel) h in
  fuel_monotonic_ifthenelse b c1 c2 g;
  f

let seq_raw (c1 c2: computation) (fuel: nat) : ISNull bool =
  if c1 fuel then c2 fuel else false

let reified_seq_raw
  (c1 c2: computation)
  (fuel: nat)
  (h: heap)
: GTot (bool * heap)
= reify (seq_raw c1 c2 fuel) h

let fuel_monotonic_seq
  (c1 c2: computation)
  (f: reified_raw_computation)
: Lemma
  (requires (forall fuel h . f fuel h == reified_seq_raw c1 c2 fuel h))
  (ensures (fuel_monotonic f))
= let prf
    (fuel fuel' : nat)
    (h : heap)
  : Lemma
    (requires (
      fuel <= fuel' /\
      fst (f fuel h) == true
    ))
    (ensures (f fuel' h == f fuel h))
  = let z1 = reify (c1 fuel) in
    assert (fst (z1 h) == true)
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (prf x y))

let seq (c1 c2: computation) : Tot computation =
  let f : raw_computation = seq_raw c1 c2 in
  let g (fuel: nat) (h: heap) : GTot (bool * heap) = reify (f fuel) h in
  fuel_monotonic_seq c1 c2 g;
  f

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

let reify_while_raw_intro_true
  (b: exp bool)
  (c: computation)
  (f: reified_raw_computation)
  (fuel: nat)
  (h: heap)
  (h1: heap)
: Lemma
  (requires (
    (forall fuel h . f fuel h == reify (while_raw b c fuel) h) /\
    fst (reify (b ()) h) == true /\
    reify (c fuel) h == (true, h1) /\
    fuel > 0
  ))
  (ensures (
    fuel > 0 /\
    f fuel h == f (fuel - 1) h1
  ))
= let (b0, h0) = reify (b ()) h in // WHY is this needed?
  ()

let reify_while_raw_intro_false
  (b: exp bool)
  (c: computation)
  (f: reified_raw_computation)
  (fuel: nat)
  (h: heap)
: Lemma
  (requires (
    (forall fuel h . f fuel h == reify (while_raw b c fuel) h) /\
    fst (reify (b ()) h) == false
  ))
  (ensures (
    f fuel h == (true, h)
  ))
= let (b0, h0) = reify (b ()) h in // WHY is this needed?
  ()

let reify_while_raw_elim_true
  (b: exp bool)
  (c: computation)
  (f: reified_raw_computation)
  (fuel: nat)
  (h: heap)
: Lemma
  (requires (
    (forall fuel h . f fuel h == reify (while_raw b c fuel) h) /\
    fst (reify (b ()) h) == true /\
    fst (f fuel h) == true
  ))
  (ensures (
    fuel > 0 /\
    fst (reify (c fuel) h) == true
  ))
= let (b0, h0) = reify (b ()) h in // WHY is this needed?
  ()

let fuel_monotonic_while
  (b: exp bool)
  (c: computation)
  (f: reified_raw_computation)
: Lemma
  (requires (forall fuel h . f fuel h == reify (while_raw b c fuel) h))
  (ensures (fuel_monotonic f))
= let _ : squash (forall fuel h . f fuel h == reify (while_raw b c fuel) h) = () in // WHY is this needed?
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
    let (b0, _) = reify (b ()) h in
    if b0
    then begin
      reify_while_raw_elim_true b c f fuel h;
      let (_, h') = reify (c fuel) h in
      reify_while_raw_intro_true b c f fuel h h';
      reify_while_raw_intro_true b c f fuel' h h';
      prf (fuel - 1) (fuel' - 1) h'
    end else begin
      reify_while_raw_intro_false b c f fuel h;
      reify_while_raw_intro_false b c f fuel' h
    end
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (prf x y))

let while (b: exp bool) (c: computation) : Tot computation =
  let f : raw_computation = while_raw b c in
  let g (fuel: nat) (h: heap) : GTot (bool * heap) = reify (f fuel) h in
  fuel_monotonic_while b c g;
  f

(* Termination *)

let terminates_on (f: reified_computation) (h: heap) : GTot Type0 =
  exists fuel . fst (f fuel h) == true

(*
assume val terminates_on_equiv
  (f: reified_computation) (h: heap)
: Lemma
  (terminates_on f h <==> (
    exists fuel . fst (f fuel h) == true
  ))
//  [SMTPat (terminates_on f h)]

let terminates_on_intro
  (f: reified_computation)
  (fuel: nat)
  (h: heap)  
  (h' : heap)
: Lemma
  (requires (f fuel h == (true, h')))
  (ensures (f `terminates_on` h))
= terminates_on_equiv  f h

let terminates_on_intro_fst
  (f: reified_computation)
  (fuel: nat)
  (h: heap)  
: Lemma
  (requires (fst (f fuel h) == true))
  (ensures (f `terminates_on` h))
= let (x, y) = f fuel h in
  terminates_on_intro f fuel h y
*)

type rel (t: Type0) = t -> t -> GTot Type0

(* NOTE: the following is necessary (and I cannot define it, I HAVE to axiomatize it like this), otherwise Z3 loops. *)

assume val holds (#t: Type0) (p: rel t) (s s' : t) : GTot Type0
assume val holds_equiv (#t: Type0) (p: rel t) (s s' : t) : Lemma
  (holds p s s' <==> p s s')

let included
  (#t: Type0)
  (r1 r2: rel t)
: GTot Type0
= forall x y . holds r1 x y ==> holds r2 x y

let is_per (#t: Type0) (f: rel t) : GTot Type0 =
  (forall x1 x2 . f x1 x2 <==> f x2 x1) /\
  (forall x1 x2 x3 . (f x1 x2 /\ f x2 x3) ==> f x1 x3)

type per (t: Type0) = ( f: rel t { is_per f } )

let per_holds_sym
  (#t: Type0)
  (p: per t)
  (s s' : t)
: Lemma
  (holds p s s' <==> holds p s' s)
  [SMTPat (holds p s s')]
= holds_equiv p s s';
  holds_equiv p s' s

let per_holds_trans
  (#t: Type0)
  (f: per t)
  (x1 x2 x3: t)
: Lemma
  (requires (holds f x1 x2 /\ holds f x2 x3))
  (ensures (holds f x1 x3))
  [SMTPatOr [
    [SMTPat (holds f x1 x2); SMTPat (holds f x2 x3)];
    [SMTPat (holds f x1 x2); SMTPat (holds f x1 x3)];
    [SMTPat (holds f x2 x3); SMTPat (holds f x1 x3)];
  ]]
= holds_equiv f x1 x2;
  holds_equiv f x2 x3;
  holds_equiv f x1 x3

let per_intersect
  (#t: Type0)
  (ns1 ns2: per t)
: GTot (per t)
= let f x y = holds ns1 x y /\ holds ns2 x y in
  Classical.forall_intro_2 (holds_equiv f);
  f

let holds_per_intersect
  (#t: Type0)
  (ns1 ns2: per t)
  (x y: t)
: Lemma
  (holds (per_intersect ns1 ns2) x y <==> (holds ns1 x y /\ holds ns2 x y))
  [SMTPat (holds (per_intersect ns1 ns2) x y)]
= holds_equiv (per_intersect ns1 ns2) x y

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

let interpolable_ns_f #t : Lemma (interpolable #t ns_f) = ()
let interpolable_ns_t #t : Lemma (interpolable #t ns_t) = ()
let interpolable_ns_singl #t (c: t) : Lemma (interpolable (ns_singl c)) = ()
let interpolable_ns_delta #t : Lemma (interpolable #t ns_delta) = ()

type sttype = (f: per heap { interpolable f } )

let st_nil: sttype =
  let f (x y : heap) : GTot Type0 = True in
  Classical.forall_intro_2 (holds_equiv f);
  f

let holds_st_nil
  (x y: heap)
: Lemma
  (holds st_nil x y <==> True)
  [SMTPat (holds st_nil x y)]
= holds_equiv st_nil x y

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
= per_intersect p1 p2

let holds_st_intersect
  (ns1 ns2: sttype)
  (x y: heap)
: Lemma
  (holds (st_intersect ns1 ns2) x y <==> (holds ns1 x y /\ holds ns2 x y))
  [SMTPat (holds (st_intersect ns1 ns2) x y)]
= holds_equiv (st_intersect ns1 ns2) x y

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

(* Subtyping *)

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
  (requires (terminates_equiv_reified p f f'))
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

(* Lemma 2 *)

let eval_equiv_sym
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f f': exp t)
: Lemma
  (requires (eval_equiv p e f f'))
  (ensures (eval_equiv p e f' f))
= ()

let exec_equiv_sym
  (p p': sttype)
  (f f' : computation)
: Lemma
  (exec_equiv p p' f f' <==> exec_equiv p p' f' f)
= ()

let eval_equiv_trans
  (#t: Type0)
  (p: sttype)
  (e: nstype t)
  (f1 f2 f3 : exp t)
: Lemma
  (requires (eval_equiv p e f1 f2 /\ eval_equiv p e f2 f3))
  (ensures (eval_equiv p e f1 f3))
= ()

let exec_equiv_reified_trans
  (p p': sttype)
  (f1 f2 f3 : reified_computation)
: Lemma
  (requires (exec_equiv_reified p p' f1 f2 /\ exec_equiv_reified p p' f2 f3))
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
    exec_equiv p p' c1 c2 /\
    exec_equiv p p' c2 c3
  ))
  (ensures (exec_equiv p p' c1 c3))
= let z1 = reify_computation c1 in
  let z2 = reify_computation c2 in
  let z3 = reify_computation c3 in
  exec_equiv_reified_trans p p' z1 z2 z3

(* Figure 2. Theorem 1. *)

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
= ()

let d_et1
  (#t: Type0)
  (f f' : exp t)
  (p: sttype)
: Lemma
  (eval_equiv p ns_t f f')
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
= ()

let d_esym = eval_equiv_sym

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
= ()

let d_etr = eval_equiv_trans

let d_csym = exec_equiv_sym

let d_ctr = exec_equiv_trans

(* Expressions *)

let d_v
  (x: var)
  (p: sttype)
  (f: nstype int)
: Lemma
  (requires (x `st_fresh_in` p))
  (ensures (x `st_fresh_in` p /\ eval_equiv (st_cons p x f) f (evar x) (evar x)))
= ()

let eval_equiv_const
  (#t: Type0)
  (c: t)
  (p: sttype)
: Lemma
  (eval_equiv p (ns_singl c) (const c) (const c))
= ()

let d_n = eval_equiv_const #int
let d_b = eval_equiv_const #bool

(*
let d_op
  (#from #to: typ)
  (o: op from to)
  (e g e' g' : exp from)
  (p: phi)
  (f f' : nstype from)
: Lemma
  (requires (
    eval_equiv p f e g /\
    eval_equiv p f' e' g'
  ))
  (ensures (eval_equiv p (abs_op o f f') (Op o e e') (Op o g g')))
= ()
*)

(* Commands *)

let d_skip
  (p: sttype)
: Lemma
  (exec_equiv p p skip skip)
= ()

#set-options "--z3rlimit 1024"

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
= ()

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
  = exec_equiv_sym p0 p1 c01 c01';
    exec_equiv_sym p1 p2 c12 c12';
    Classical.move_requires (d_seq_terminates p0 p1 p2 c01 c01' c12 c12' s0) s0';
    Classical.move_requires (d_seq_terminates p0 p1 p2 c01' c01 c12' c12 s0') s0
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
= ()

