module Steel.ST.GenElim


irreducible let gen_elim_reduce = ()

let gen_elim_pred
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
  (ij: (gen_elim_i & gen_elim_nondep_t))
: Tot prop
= let (i, j) = ij in
  p == compute_gen_elim_p i /\
  check_gen_elim_nondep_sem i j /\ 
  a == compute_gen_elim_nondep_a i j /\
  post == compute_gen_elim_nondep_post i j /\
  q == compute_gen_elim_nondep_q i j

let gen_elim_prop
  enable_nondep_opt p a q post
= exists ij . gen_elim_pred enable_nondep_opt p a q post ij

let gen_elim_prop_intro'
  i j enable_nondep_opt p a q post sq_p sq_j sq_a sq_q sq_post
= assert (gen_elim_pred enable_nondep_opt p a q post (i, j))

let gen_elim_f
  (p: vprop)
  (a: Type0) // FIXME: generalize this universe
  (q: (a -> vprop))
  (post: (a -> prop))
: Tot Type
= ((opened: inames) -> STGhost a opened p q True post)

let gen_unit_elim_t (i: gen_unit_elim_i) : Tot Type =
  gen_elim_f (compute_gen_unit_elim_p i) unit (fun _ -> compute_gen_unit_elim_q i) (fun _ -> compute_gen_unit_elim_post i)

let compute_gen_unit_elim_f_id
  (v: vprop)
: Tot (gen_unit_elim_t (GUEId v))
= fun _ -> noop ()

let compute_gen_unit_elim_f_pure
  (p: prop)
: Tot (gen_unit_elim_t (GUEPure p))
= fun _ ->
  rewrite (compute_gen_unit_elim_p (GUEPure p)) (pure p);
  elim_pure p

let compute_gen_unit_elim_f_star
  (i1 i2: gen_unit_elim_i)
  (f1: gen_unit_elim_t i1)
  (f2: gen_unit_elim_t i2)
: Tot (gen_unit_elim_t (GUEStar i1 i2))
= fun _ ->
  rewrite (compute_gen_unit_elim_p (GUEStar i1 i2)) (compute_gen_unit_elim_p i1 `star` compute_gen_unit_elim_p i2);
  f1 _; f2 _;
  rewrite (compute_gen_unit_elim_q i1 `star` compute_gen_unit_elim_q i2) (compute_gen_unit_elim_q (GUEStar i1 i2))

let rec compute_gen_unit_elim_f
  (i: gen_unit_elim_i)
: Tot (gen_unit_elim_t i)
= match i returns (gen_unit_elim_t i) with
  | GUEId v -> compute_gen_unit_elim_f_id v
  | GUEPure p -> compute_gen_unit_elim_f_pure p
  | GUEStar i1 i2 -> compute_gen_unit_elim_f_star i1 i2 (compute_gen_unit_elim_f i1) (compute_gen_unit_elim_f i2)

let gen_elim_t (i: gen_elim_i) : Tot Type =
  gen_elim_f (compute_gen_elim_p i) (compute_gen_elim_a i) (compute_gen_elim_q i) (compute_gen_elim_post i)

let compute_gen_elim_f_unit
  (i: gen_unit_elim_i)
: Tot (gen_elim_t (GEUnit i))
= compute_gen_unit_elim_f i

let compute_gen_elim_f_star_l
  (i1: gen_elim_i)
  (f1: gen_elim_t i1)
  (i2: gen_unit_elim_i)
: Tot (gen_elim_t (GEStarL i1 i2))
= let f2 = compute_gen_unit_elim_f i2 in
  fun _ ->
  rewrite (compute_gen_elim_p (GEStarL i1 i2)) (compute_gen_elim_p i1 `star` compute_gen_unit_elim_p i2);
  let res = f1 _ in
  f2 _;
  let res' : compute_gen_elim_a (GEStarL i1 i2) = coerce_with_trefl res in
  rewrite (compute_gen_elim_q i1 res `star` compute_gen_unit_elim_q i2) (compute_gen_elim_q (GEStarL i1 i2) res');
  res'

let compute_gen_elim_f_star_r
  (i1: gen_unit_elim_i)
  (i2: gen_elim_i)
  (f2: gen_elim_t i2)
: Tot (gen_elim_t (GEStarR i1 i2))
= let f1 = compute_gen_unit_elim_f i1 in
  fun _ ->
  rewrite (compute_gen_elim_p (GEStarR i1 i2)) (compute_gen_unit_elim_p i1 `star` compute_gen_elim_p i2);
  f1 _;
  let res = f2 _ in
  let res' : compute_gen_elim_a (GEStarR i1 i2) = coerce_with_trefl res in
  rewrite (compute_gen_unit_elim_q i1 `star` compute_gen_elim_q i2 res) (compute_gen_elim_q (GEStarR i1 i2) res');
  res'

let compute_gen_elim_f_star
  (i1: gen_elim_i)
  (f1: gen_elim_t i1)
  (i2: gen_elim_i)
  (f2: gen_elim_t i2)
: Tot (gen_elim_t (GEStar i1 i2))
= fun _ ->
  rewrite (compute_gen_elim_p (GEStar i1 i2)) (compute_gen_elim_p i1 `star` compute_gen_elim_p i2);
  let res1 = f1 _ in
  let res2 = f2 _ in
  let res : compute_gen_elim_a (GEStar i1 i2) = coerce_with_trefl (res1, res2) in
  rewrite (compute_gen_elim_q i1 res1 `star` compute_gen_elim_q i2 res2) (compute_gen_elim_q (GEStar i1 i2) res);
  res

let compute_gen_elim_f_exists_no_abs
  (a: Type0)
  (body: (a -> vprop))
: Tot (gen_elim_t (GEExistsNoAbs body))
= fun _ ->
  rewrite (compute_gen_elim_p (GEExistsNoAbs body)) (exists_ body);
  let gres = elim_exists () in
  let res : compute_gen_elim_a (GEExistsNoAbs body) = coerce_with_trefl (Ghost.reveal gres) in
  rewrite (body gres) (compute_gen_elim_q (GEExistsNoAbs body) res);
  res

let rewrite_with_trefl (#opened:_) (p q:vprop)
  : STGhost unit opened
      p
      (fun _ -> q)
      (requires T.with_tactic T.trefl (p == q))
      (ensures fun _ -> True)
= rewrite p q

let compute_gen_elim_f_exists_unit
  (a: Type0)
  (body: a -> gen_unit_elim_i)
: Tot (gen_elim_t (GEExistsUnit body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExistsUnit body)) (exists_ (fun x -> compute_gen_unit_elim_p (body x)));
  let gres = elim_exists () in
  compute_gen_unit_elim_f (body gres) _;
  let res : compute_gen_elim_a (GEExistsUnit body) = coerce_with_trefl (Ghost.reveal gres) in
  rewrite (compute_gen_unit_elim_q (body gres)) (compute_gen_elim_q (GEExistsUnit body) res);
  res

let compute_gen_elim_f_exists
  (a: Type0)
  (body: a -> gen_elim_i)
  (f: (x: a) -> gen_elim_t (body x))
: Tot (gen_elim_t (GEExists body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExists body)) (exists_ (fun x -> compute_gen_elim_p (body x)));
  let gres1 = elim_exists () in
  let gres2 = f gres1 _ in
  let res : compute_gen_elim_a (GEExists body) = coerce_with_trefl (Mkdtuple2 #a #(fun x -> compute_gen_elim_a (body x)) (Ghost.reveal gres1) (Ghost.reveal gres2)) in
  rewrite (compute_gen_elim_q (body gres1) gres2) (compute_gen_elim_q (GEExists body) res);
  res

let rec compute_gen_elim_f
  (i: gen_elim_i)
: Tot (gen_elim_t i)
= match i returns (gen_elim_t i) with
  | GEUnit i -> compute_gen_elim_f_unit i
  | GEStarL i1 i2 -> compute_gen_elim_f_star_l i1 (compute_gen_elim_f i1) i2
  | GEStarR i1 i2 -> compute_gen_elim_f_star_r i1 i2 (compute_gen_elim_f i2)
  | GEStar i1 i2 -> compute_gen_elim_f_star i1 (compute_gen_elim_f i1) i2 (compute_gen_elim_f i2)
  | GEExistsNoAbs body -> compute_gen_elim_f_exists_no_abs _ body
  | GEExistsUnit body -> compute_gen_elim_f_exists_unit _ body
  | GEExists body -> compute_gen_elim_f_exists _ body (fun x -> compute_gen_elim_f (body x))

let coerce_with_smt (#tfrom #tto: Type) (x: tfrom) : Pure tto (requires ( (tfrom == tto))) (ensures (fun _ -> True)) = x

let gen_elim' = admit ()
(*
  #opened p i a q post sq _
= rewrite p (compute_gen_elim_p' i);
  let vres' : compute_gen_elim_a' i = compute_gen_elim_f i _ in
  let vres : a = coerce_with_smt #(compute_gen_elim_a' i) vres' in
  let res : Ghost.erased a = Ghost.hide vres in
  rewrite (compute_gen_elim_q' i vres') (q res);
  res
*)

let gen_elim
  #opened #p #a #q #post #sq _
= gen_elim' #opened _ p a q post sq ()

let gen_elim_dep
  #opened #p #a #q #post #sq _
= gen_elim' #opened _ p a q post sq ()
