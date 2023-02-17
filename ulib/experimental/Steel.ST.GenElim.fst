module Steel.ST.GenElim

let gen_elim_f
  (p: vprop)
  (a: Type)
  (q: (a -> vprop))
  (post: (a -> prop))
: Tot Type
= ((opened: inames) -> STGhost a opened p q True post)

module U = FStar.Universe

let gen_unit_elim_t (i: gen_unit_elim_i) : Tot Type =
  gen_elim_f (compute_gen_unit_elim_p i) (U.raise_t u#_ u#1 unit) (fun _ -> compute_gen_unit_elim_q i) (fun _ -> compute_gen_unit_elim_post i)

let compute_gen_unit_elim_f_id
  (v: vprop)
: Tot (gen_unit_elim_t (GUEId v))
= fun _ -> noop (); U.raise_val ()

let compute_gen_unit_elim_f_pure
  (p: prop)
: Tot (gen_unit_elim_t (GUEPure p))
= fun _ ->
  rewrite (compute_gen_unit_elim_p (GUEPure p)) (pure p);
  elim_pure p;
  U.raise_val ()

let compute_gen_unit_elim_f_star
  (i1 i2: gen_unit_elim_i)
  (f1: gen_unit_elim_t i1)
  (f2: gen_unit_elim_t i2)
: Tot (gen_unit_elim_t (GUEStar i1 i2))
= fun _ ->
  rewrite (compute_gen_unit_elim_p (GUEStar i1 i2)) (compute_gen_unit_elim_p i1 `star` compute_gen_unit_elim_p i2);
  let _ = f1 _ in
  let _ = f2 _ in
  rewrite (compute_gen_unit_elim_q i1 `star` compute_gen_unit_elim_q i2) (compute_gen_unit_elim_q (GUEStar i1 i2));
  U.raise_val ()

let rec compute_gen_unit_elim_f
  (i: gen_unit_elim_i)
: GTot (gen_unit_elim_t i)
= match i returns (gen_unit_elim_t i) with
  | GUEId v -> compute_gen_unit_elim_f_id v
  | GUEPure p -> compute_gen_unit_elim_f_pure p
  | GUEStar i1 i2 -> compute_gen_unit_elim_f_star i1 i2 (compute_gen_unit_elim_f i1) (compute_gen_unit_elim_f i2)

let gen_elim_t (i: gen_elim_i) : Tot Type =
  gen_elim_f (compute_gen_elim_p i) (compute_gen_elim_a i) (compute_gen_elim_q i) (compute_gen_elim_post i)

let compute_gen_elim_f_unit
  (i: gen_unit_elim_i)
: GTot (gen_elim_t (GEUnit i))
= compute_gen_unit_elim_f i

let compute_gen_elim_f_star_l
  (i1: gen_elim_i)
  (f1: gen_elim_t i1)
  (i2: gen_unit_elim_i)
: GTot (gen_elim_t (GEStarL i1 i2))
= let f2 = compute_gen_unit_elim_f i2 in
  fun _ ->
  rewrite (compute_gen_elim_p (GEStarL i1 i2)) (compute_gen_elim_p i1 `star` compute_gen_unit_elim_p i2);
  let res = f1 _ in
  let _ = f2 _ in
  let res' : compute_gen_elim_a (GEStarL i1 i2) = coerce_with_trefl res in
  rewrite (compute_gen_elim_q i1 res `star` compute_gen_unit_elim_q i2) (compute_gen_elim_q (GEStarL i1 i2) res');
  res'

let compute_gen_elim_f_star_r
  (i1: gen_unit_elim_i)
  (i2: gen_elim_i)
  (f2: gen_elim_t i2)
: GTot (gen_elim_t (GEStarR i1 i2))
= let f1 = compute_gen_unit_elim_f i1 in
  fun _ ->
  rewrite (compute_gen_elim_p (GEStarR i1 i2)) (compute_gen_unit_elim_p i1 `star` compute_gen_elim_p i2);
  let _ = f1 _ in
  let res = f2 _ in
  let res' : compute_gen_elim_a (GEStarR i1 i2) = coerce_with_trefl res in
  rewrite (compute_gen_unit_elim_q i1 `star` compute_gen_elim_q i2 res) (compute_gen_elim_q (GEStarR i1 i2) res');
  res'

let compute_gen_elim_f_star
  (i1: gen_elim_i)
  (f1: gen_elim_t i1)
  (i2: gen_elim_i)
  (f2: gen_elim_t i2)
: GTot (gen_elim_t (GEStar i1 i2))
= fun _ ->
  rewrite (compute_gen_elim_p (GEStar i1 i2)) (compute_gen_elim_p i1 `star` compute_gen_elim_p i2);
  let res1 = f1 _ in
  let res2 = f2 _ in
  let res : compute_gen_elim_a (GEStar i1 i2) = coerce_with_trefl (res1, res2) in
  rewrite (compute_gen_elim_q i1 res1 `star` compute_gen_elim_q i2 res2) (compute_gen_elim_q (GEStar i1 i2) res);
  res

let compute_gen_elim_f_exists_no_abs0
  (a: Type0)
  (body: (a -> vprop))
: GTot (gen_elim_t (GEExistsNoAbs0 body))
= fun _ ->
  rewrite (compute_gen_elim_p (GEExistsNoAbs0 body)) (exists_ body);
  let gres = elim_exists () in
  let res : compute_gen_elim_a (GEExistsNoAbs0 body) = U.raise_val (Ghost.reveal gres) in //  coerce_with_trefl (Ghost.reveal gres) in
  rewrite (body gres) (compute_gen_elim_q (GEExistsNoAbs0 body) res);
  res

let rewrite_with_trefl (#opened:_) (p q:vprop)
  : STGhost unit opened
      p
      (fun _ -> q)
      (requires T.with_tactic T.trefl (p == q))
      (ensures fun _ -> True)
= rewrite p q

let compute_gen_elim_f_exists_unit0
  (a: Type0)
  (body: a -> gen_unit_elim_i)
: Tot (gen_elim_t (GEExistsUnit0 body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExistsUnit0 body)) (exists_ (fun x -> compute_gen_unit_elim_p (body x)));
  let gres = elim_exists () in
  let _ = compute_gen_unit_elim_f (body gres) _ in
  let res : compute_gen_elim_a (GEExistsUnit0 body) = U.raise_val (Ghost.reveal gres) in // coerce_with_trefl (Ghost.reveal gres) in
  rewrite (compute_gen_unit_elim_q (body gres)) (compute_gen_elim_q (GEExistsUnit0 body) res);
  res

let compute_gen_elim_f_exists0
  (a: Type0)
  (body: a -> gen_elim_i)
  (f: (x: a) -> GTot (gen_elim_t (body x)))
: Tot (gen_elim_t (GEExists0 body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExists0 body)) (exists_ (fun x -> compute_gen_elim_p (body x)));
  let gres1 = elim_exists () in
  let gres2 = f gres1 _ in
  let res : compute_gen_elim_a (GEExists0 body) = coerce_with_trefl (Mkdtuple2 #a #(fun x -> compute_gen_elim_a (body x)) (Ghost.reveal gres1) (Ghost.reveal gres2)) in
  rewrite (compute_gen_elim_q (body gres1) gres2) (compute_gen_elim_q (GEExists0 body) res);
  res

let compute_gen_elim_f_exists_no_abs1
  (a: Type)
  (body: (a -> vprop))
: GTot (gen_elim_t (GEExistsNoAbs1 body))
= fun _ ->
  rewrite (compute_gen_elim_p (GEExistsNoAbs1 body)) (exists_ body);
  let gres = elim_exists () in
  let res : compute_gen_elim_a (GEExistsNoAbs1 body) = coerce_with_trefl (Ghost.reveal gres) in
  rewrite (body gres) (compute_gen_elim_q (GEExistsNoAbs1 body) res);
  res

let compute_gen_elim_f_exists_unit1
  (a: Type)
  (body: a -> gen_unit_elim_i)
: Tot (gen_elim_t (GEExistsUnit1 body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExistsUnit1 body)) (exists_ (fun x -> compute_gen_unit_elim_p (body x)));
  let gres = elim_exists () in
  let _ = compute_gen_unit_elim_f (body gres) _ in
  let res : compute_gen_elim_a (GEExistsUnit1 body) = coerce_with_trefl (Ghost.reveal gres) in
  rewrite (compute_gen_unit_elim_q (body gres)) (compute_gen_elim_q (GEExistsUnit1 body) res);
  res

let compute_gen_elim_f_exists1
  (a: Type)
  (body: a -> gen_elim_i)
  (f: (x: a) -> GTot (gen_elim_t (body x)))
: Tot (gen_elim_t (GEExists1 body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p (GEExists1 body)) (exists_ (fun x -> compute_gen_elim_p (body x)));
  let gres1 = elim_exists () in
  let gres2 = f gres1 _ in
  let res : compute_gen_elim_a (GEExists1 body) = coerce_with_trefl (Mkdtuple2 #a #(fun x -> compute_gen_elim_a (body x)) (Ghost.reveal gres1) (Ghost.reveal gres2)) in
  rewrite (compute_gen_elim_q (body gres1) gres2) (compute_gen_elim_q (GEExists1 body) res);
  res

let rec compute_gen_elim_f
  (i: gen_elim_i)
: GTot (gen_elim_t i)
= match i returns (gen_elim_t i) with
  | GEUnit i -> compute_gen_elim_f_unit i
  | GEStarL i1 i2 -> compute_gen_elim_f_star_l i1 (compute_gen_elim_f i1) i2
  | GEStarR i1 i2 -> compute_gen_elim_f_star_r i1 i2 (compute_gen_elim_f i2)
  | GEStar i1 i2 -> compute_gen_elim_f_star i1 (compute_gen_elim_f i1) i2 (compute_gen_elim_f i2)
  | GEExistsNoAbs0 body -> compute_gen_elim_f_exists_no_abs0 _ body
  | GEExistsUnit0 body -> compute_gen_elim_f_exists_unit0 _ body
  | GEExists0 body -> compute_gen_elim_f_exists0 _ body (fun x -> compute_gen_elim_f (body x))
  | GEExistsNoAbs1 body -> compute_gen_elim_f_exists_no_abs1 _ body
  | GEExistsUnit1 body -> compute_gen_elim_f_exists_unit1 _ body
  | GEExists1 body -> compute_gen_elim_f_exists1 _ body (fun x -> compute_gen_elim_f (body x))

let rec tele_p (x: gen_elim_tele) : Tot vprop =
  match x with
  | TRet v p -> v `star` pure p
  | TExists ty body -> exists_ (fun x -> tele_p (body x))

let elim_exists' (#a:Type)
                (#opened_invariants:_)
                (#p:a -> vprop)
                (_:unit)
  : STGhostT (a) opened_invariants
             (exists_ p)
             (fun x -> p x)
= let gx = elim_exists () in
  let x = Ghost.reveal gx in
  rewrite (p gx) (p x);
  x

let vprop_rewrite (from to: vprop) : Tot Type =
  gen_elim_f from unit (fun _ -> to) (fun _ -> True)

let tele_star_vprop_correct_ret
  (v': vprop) (p': prop) (v: vprop) (p: prop)
: Tot (vprop_rewrite (tele_p (TRet v' p') `star` v `star` pure p) (tele_p (tele_star_vprop (TRet v' p') v p)))
= fun _ ->
    elim_pure p;
    rewrite (tele_p _) (v' `star` pure p');
    elim_pure p';
    intro_pure (p /\ p');
    rewrite ((v `star` v') `star` pure (p /\ p')) (tele_p _)

let tele_star_vprop_correct_exists
  (v: vprop) (p: prop)
  (ty: _) (body: ty -> gen_elim_tele) (ih: (x: ty) -> GTot (vprop_rewrite (tele_p (body x) `star` v `star` pure p) (tele_p (tele_star_vprop (body x) v p))))
: Tot (vprop_rewrite (tele_p (TExists ty body) `star` v `star` pure p) (tele_p (tele_star_vprop (TExists ty body) v p)))
= fun _ ->
    rewrite_with_trefl (tele_p _) (exists_ (fun x -> tele_p (body x)));
    let x = elim_exists' () in
    ih x _;
    intro_exists x (fun x -> tele_p (tele_star_vprop (body x) v p));
    rewrite_with_trefl (exists_ (fun x -> tele_p (tele_star_vprop (body x) v p))) (tele_p _)

let rec tele_star_vprop_correct
  (i: gen_elim_tele) (v: vprop) (p: prop)
: GTot (vprop_rewrite
    (tele_p i `star` v `star` pure p)
    (tele_p (tele_star_vprop i v p))
  )
= match i returns vprop_rewrite
    (tele_p i `star` v `star` pure p)
    (tele_p (tele_star_vprop i v p)) with
  | TRet v' p' -> tele_star_vprop_correct_ret v' p' v p
  | TExists ty body -> tele_star_vprop_correct_exists v p ty body (fun x -> tele_star_vprop_correct (body x) v p)

let tele_star_correct_ret_l
  (v1: vprop) (p1: prop) (i2: gen_elim_tele)
: Tot (vprop_rewrite (tele_p (TRet v1 p1) `star` tele_p i2) (tele_p (TRet v1 p1 `tele_star` i2)))
= fun _ ->
  rewrite (tele_p (TRet v1 p1)) (v1 `star` pure p1);
  tele_star_vprop_correct i2 v1 p1 _;
  rewrite (tele_p _) (tele_p _)

let tele_star_correct_ret_r
  (i1: gen_elim_tele { ~ (TRet? i1) }) (v2: vprop) (p2: prop)
: Tot (vprop_rewrite (tele_p i1 `star` tele_p (TRet v2 p2)) (tele_p (i1 `tele_star` TRet v2 p2)))
= fun _ ->
  rewrite (tele_p (TRet v2 p2)) (v2 `star` pure p2);
  tele_star_vprop_correct i1 v2 p2 _;
  rewrite (tele_p _) (tele_p (i1 `tele_star` TRet v2 p2))

let tele_star_correct_exists
  (ty1: _) (f1: ty1 -> gen_elim_tele) (ty2: _) (f2: ty2 -> gen_elim_tele)
  (ih: (x1: ty1) -> (x2: ty2) -> GTot (vprop_rewrite (tele_p (f1 x1) `star` tele_p (f2 x2)) (tele_p (f1 x1 `tele_star` f2 x2))))
: Tot (vprop_rewrite (tele_p (TExists ty1 f1) `star` tele_p (TExists ty2 f2)) (tele_p (tele_star (TExists ty1 f1) (TExists ty2 f2))))
= fun _ ->
  rewrite_with_trefl (tele_p (TExists ty1 f1)) (exists_ (fun x1 -> tele_p (f1 x1)));
  let x1 = elim_exists' () in
  rewrite_with_trefl (tele_p (TExists ty2 f2)) (exists_ (fun x2 -> tele_p (f2 x2)));
  let x2 = elim_exists' () in
  ih x1 x2 _;
  intro_exists x2 (fun x2 -> tele_p (tele_star (f1 x1) (f2 x2)));
  intro_exists x1 (fun x1 -> exists_ (fun x2 -> tele_p (tele_star (f1 x1) (f2 x2))));
  rewrite_with_trefl (exists_ _) (tele_p _)

let rec tele_star_correct
  (i1 i2: gen_elim_tele)
: GTot (vprop_rewrite (tele_p i1 `star` tele_p i2) (tele_p (i1 `tele_star` i2)))
= match i1 returns vprop_rewrite (tele_p i1 `star` tele_p i2) (tele_p (i1 `tele_star` i2)) with
  | TRet v1 p1 -> tele_star_correct_ret_l v1 p1 i2
  | TExists ty1 f1 ->
    begin match i2 returns vprop_rewrite (tele_p (TExists ty1 f1) `star` tele_p i2) (tele_p (TExists ty1 f1 `tele_star` i2)) with
    | TRet v2 p2 -> tele_star_correct_ret_r (TExists ty1 f1) v2 p2
    | TExists ty2 f2 -> tele_star_correct_exists ty1 f1 ty2 f2 (fun x1 x2 -> tele_star_correct (f1 x1) (f2 x2))
    end

[@@noextract_to "Plugin" ]
let ge_to_tele_t
  (i: gen_elim_i)
: Tot Type
= vprop_rewrite (compute_gen_elim_p i) (tele_p (compute_gen_elim_tele i))

let compute_gen_elim_tele_correct_unit
  (v: gen_unit_elim_i)
: Tot (ge_to_tele_t (GEUnit v))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (compute_gen_unit_elim_p v);
  let _ = compute_gen_unit_elim_f v _ in
  intro_pure (compute_gen_unit_elim_post v);
  rewrite_with_trefl (compute_gen_unit_elim_q v `star` pure _) (tele_p _)

let compute_gen_elim_tele_correct_star_l
  (l: gen_elim_i)
  (ihl: ge_to_tele_t l)
  (ru: gen_unit_elim_i)
: Tot (ge_to_tele_t (GEStarL l ru))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (compute_gen_elim_p l `star` compute_gen_unit_elim_p ru);
  ihl _;
  let _ = compute_gen_unit_elim_f ru _ in
  intro_pure (compute_gen_unit_elim_post ru);
  tele_star_vprop_correct _ _ _ _;
  rewrite_with_trefl (tele_p _) (tele_p _)

let compute_gen_elim_tele_correct_star_r
  (lu: gen_unit_elim_i)
  (r: gen_elim_i)
  (ihr: ge_to_tele_t r)
: Tot (ge_to_tele_t (GEStarR lu r))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (compute_gen_unit_elim_p lu `star` compute_gen_elim_p r);
  ihr _;
  let _ = compute_gen_unit_elim_f lu _ in
  intro_pure (compute_gen_unit_elim_post lu);
  tele_star_vprop_correct _ _ _ _;
  rewrite_with_trefl (tele_p _) (tele_p _)

let compute_gen_elim_tele_correct_star
  (l: gen_elim_i)
  (ihl: ge_to_tele_t l)
  (r: gen_elim_i)
  (ihr: ge_to_tele_t r)
: Tot (ge_to_tele_t (GEStar l r))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (compute_gen_elim_p l `star` compute_gen_elim_p r);
  ihl _;
  ihr _;
  tele_star_correct (compute_gen_elim_tele l) (compute_gen_elim_tele r) _;
  rewrite_with_trefl (tele_p _) (tele_p _)

let compute_gen_elim_tele_correct_exists_no_abs0
  (ty: _)
  (body: ty -> vprop)
: Tot (ge_to_tele_t (GEExistsNoAbs0 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ body);
  let x = elim_exists' () in
  intro_pure True;
  rewrite (body x) (body (U.downgrade_val (U.raise_val x)));
  intro_exists (U.raise_val u#0 u#1 x) (fun x -> body (U.downgrade_val x) `star` pure True);
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists_unit0
  (ty: _)
  (body: ty -> gen_unit_elim_i)
: Tot (ge_to_tele_t (GEExistsUnit0 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ (fun x -> compute_gen_unit_elim_p (body x)));
  let x = elim_exists' () in
  let _ = compute_gen_unit_elim_f (body x) _ in
  intro_pure (compute_gen_unit_elim_post (body (U.downgrade_val (U.raise_val u#0 u#1 x))));
  rewrite (compute_gen_unit_elim_q (body x)) (compute_gen_unit_elim_q (body (U.downgrade_val (U.raise_val x))));
  intro_exists (U.raise_val u#0 u#1 x) (fun x -> compute_gen_unit_elim_q (body (U.downgrade_val x)) `star` pure (compute_gen_unit_elim_post (body (U.downgrade_val x))));
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists0
  (ty: _)
  (body: ty -> gen_elim_i)
  (ih: (x: ty) -> GTot (ge_to_tele_t (body x)))
: Tot (ge_to_tele_t (GEExists0 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ (fun x -> compute_gen_elim_p (body x)));
  let x = elim_exists' () in
  ih x _;
  rewrite (tele_p (compute_gen_elim_tele (body x))) (tele_p (compute_gen_elim_tele (body (U.downgrade_val (U.raise_val u#0 u#1 x)))));
  intro_exists (U.raise_val u#0 u#1 x) (fun x -> tele_p (compute_gen_elim_tele (body (U.downgrade_val u#0 u#1 x))));
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists_no_abs1
  (ty: _)
  (body: ty -> vprop)
: Tot (ge_to_tele_t (GEExistsNoAbs1 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ body);
  let x = elim_exists' () in
  intro_pure True;
  intro_exists x (fun x -> body x `star` pure True);
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists_unit1
  (ty: _)
  (body: ty -> gen_unit_elim_i)
: Tot (ge_to_tele_t (GEExistsUnit1 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ (fun x -> compute_gen_unit_elim_p (body x)));
  let x = elim_exists' () in
  let _ = compute_gen_unit_elim_f (body x) _ in
  intro_pure (compute_gen_unit_elim_post (body x));
  intro_exists x (fun x -> compute_gen_unit_elim_q (body x) `star` pure (compute_gen_unit_elim_post (body x)));
  rewrite_with_trefl (exists_ _) (tele_p _)

let compute_gen_elim_tele_correct_exists1
  (ty: _)
  (body: ty -> gen_elim_i)
  (ih: (x: ty) -> GTot (ge_to_tele_t (body x)))
: Tot (ge_to_tele_t (GEExists1 #ty body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p _) (exists_ (fun x -> compute_gen_elim_p (body x)));
  let x = elim_exists' () in
  ih x _;
  intro_exists x (fun x -> tele_p (compute_gen_elim_tele (body x)));
  rewrite_with_trefl (exists_ _) (tele_p _)

let rec compute_gen_elim_tele_correct
  (x: gen_elim_i)
: GTot (ge_to_tele_t x)
= match x returns ge_to_tele_t x with
  | GEUnit v -> compute_gen_elim_tele_correct_unit v
  | GEStarL l ru -> compute_gen_elim_tele_correct_star_l l (compute_gen_elim_tele_correct l) ru
  | GEStarR lu r -> compute_gen_elim_tele_correct_star_r lu r (compute_gen_elim_tele_correct r)
  | GEStar l r -> compute_gen_elim_tele_correct_star l (compute_gen_elim_tele_correct l) r (compute_gen_elim_tele_correct r)
  | GEExistsNoAbs0 #ty body -> compute_gen_elim_tele_correct_exists_no_abs0 ty body
  | GEExistsUnit0 #ty body -> compute_gen_elim_tele_correct_exists_unit0 ty body
  | GEExists0 #ty body -> compute_gen_elim_tele_correct_exists0 ty body (fun x -> compute_gen_elim_tele_correct (body x))
  | GEExistsNoAbs1 #ty body -> compute_gen_elim_tele_correct_exists_no_abs1 ty body
  | GEExistsUnit1 #ty body -> compute_gen_elim_tele_correct_exists_unit1 ty body
  | GEExists1 #ty body -> compute_gen_elim_tele_correct_exists1 ty body (fun x -> compute_gen_elim_tele_correct (body x))

let rec gen_elim_nondep_p (ty: list (Type u#a)) : Tot (curried_function_type ty (U.raise_t u#_ u#(max 2 a) unit -> vprop) -> curried_function_type ty (U.raise_t u#_ u#(max 2 a) unit -> prop) -> Tot vprop) =
  match ty as ty' returns curried_function_type ty' (U.raise_t u#_ u#(max 2 a) unit -> vprop) -> curried_function_type ty' (U.raise_t u#_ u#(max 2 a) unit -> prop) -> Tot vprop with
  | [] -> fun q post -> q (U.raise_val ()) `star` pure (post (U.raise_val ()))
  | t :: tq -> fun q post -> exists_ (fun x -> gen_elim_nondep_p tq (q x) (post x))

let rec gen_elim_nondep_sem_correct
  (ty: list (Type u#a))
: Tot ((q: curried_function_type ty _) -> (post: curried_function_type ty _) -> Lemma
    (tele_p (gen_elim_nondep_sem ty q post) `equiv` gen_elim_nondep_p ty q post)
  )
= match ty returns ((q: curried_function_type ty _) -> (post: curried_function_type ty _) -> Lemma
    (tele_p (gen_elim_nondep_sem ty q post) `equiv` gen_elim_nondep_p ty q post)
  )
  with
  | [] -> fun q post -> equiv_refl (q (U.raise_val ()) `star` pure (post (U.raise_val ())))
  | ta :: tq -> fun q post ->
    let phi
      (x: ta)
    : Lemma
      (tele_p (gen_elim_nondep_sem tq (q x) (post x)) `equiv` gen_elim_nondep_p tq (q x) (post x))
    = gen_elim_nondep_sem_correct tq (q x) (post x)
    in
    Classical.forall_intro phi;
    let prf () : Lemma
      (exists_ (fun x -> tele_p (gen_elim_nondep_sem tq (q x) (post x))) `equiv` exists_ (fun x -> gen_elim_nondep_p tq (q x) (post x)))
    =
      exists_equiv (fun x -> tele_p (gen_elim_nondep_sem tq (q x) (post x))) (fun x -> gen_elim_nondep_p tq (q x) (post x))
    in
    assert_norm (tele_p (gen_elim_nondep_sem (ta :: tq) q post) == exists_ (fun x -> tele_p (gen_elim_nondep_sem tq (q x) (post x))));
    assert_norm (gen_elim_nondep_p (ta :: tq) q post == exists_ (fun x -> gen_elim_nondep_p tq (q x) (post x)));
    prf ()

let compute_gen_elim_nondep_correct_t
  (i0: gen_elim_i)
  (ty: list (Type u#1))
: Tot Type
= (q: _) ->
  (post: _) ->
  (intro: vprop_rewrite (compute_gen_elim_p i0) (gen_elim_nondep_p ty q post)) ->
  GTot (gen_elim_f
    (compute_gen_elim_p i0)
    (compute_gen_elim_nondep_a' ty)
    (fun x -> compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) ty q x (U.raise_val ()))
    (fun x -> compute_uncurry _ (fun _ -> True) ty post x (U.raise_val ()))
  )

let compute_gen_elim_nondep_correct0
  (i0: gen_elim_i)
: Tot (compute_gen_elim_nondep_correct_t i0 [])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (q (U.raise_val ()) `star` pure (post (U.raise_val ())));
    let res = U.raise_val () in
    elim_pure _;
    rewrite_with_trefl (q (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct1
  (i0: gen_elim_i)
  (t1: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> q x1 (U.raise_val ()) `star` pure (post x1 (U.raise_val ()))));
    let res = elim_exists' () in
    elim_pure _;
    rewrite_with_trefl (q _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct2
  (i0: gen_elim_i)
  (t1 t2: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> q x1 x2 (U.raise_val ()) `star` pure (post x1 x2 (U.raise_val ())))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let res = Mktuple2 x1 x2 in
    elim_pure _;
    rewrite_with_trefl (q _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct3
  (i0: gen_elim_i)
  (t1 t2 t3: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> q x1 x2 x3 (U.raise_val ()) `star` pure (post x1 x2 x3 (U.raise_val ()))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let res = Mktuple3 x1 x2 x3 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct4
  (i0: gen_elim_i)
  (t1 t2 t3 t4: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> q x1 x2 x3 x4 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 (U.raise_val ())))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let res = Mktuple4 x1 x2 x3 x4 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct5
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> q x1 x2 x3 x4 x5 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 (U.raise_val ()))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let res = Mktuple5 x1 x2 x3 x4 x5 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct6
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5; t6])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> exists_ (fun x6 -> q x1 x2 x3 x4 x5 x6 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 x6 (U.raise_val ())))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let x6 = elim_exists' () in
    let res = Mktuple6 x1 x2 x3 x4 x5 x6 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct7
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6 t7: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5; t6; t7])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> exists_ (fun x6 -> exists_ (fun x7 -> q x1 x2 x3 x4 x5 x6 x7 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 x6 x7 (U.raise_val ()))))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let x6 = elim_exists' () in
    let x7 = elim_exists' () in
    let res = Mktuple7 x1 x2 x3 x4 x5 x6 x7 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct8
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6 t7 t8: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5; t6; t7; t8])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> exists_ (fun x6 -> exists_ (fun x7 -> exists_ (fun x8 -> q x1 x2 x3 x4 x5 x6 x7 x8 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 x6 x7 x8 (U.raise_val ())))))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let x6 = elim_exists' () in
    let x7 = elim_exists' () in
    let x8 = elim_exists' () in
    let res = Mktuple8 x1 x2 x3 x4 x5 x6 x7 x8 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct9
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6 t7 t8 t9: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5; t6; t7; t8; t9])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> exists_ (fun x6 -> exists_ (fun x7 -> exists_ (fun x8 -> exists_ (fun x9 -> q x1 x2 x3 x4 x5 x6 x7 x8 x9 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 x6 x7 x8 x9 (U.raise_val ()))))))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let x6 = elim_exists' () in
    let x7 = elim_exists' () in
    let x8 = elim_exists' () in
    let x9 = elim_exists' () in
    let res = Mktuple9 x1 x2 x3 x4 x5 x6 x7 x8 x9 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct10
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> exists_ (fun x6 -> exists_ (fun x7 -> exists_ (fun x8 -> exists_ (fun x9 -> exists_ (fun x10 -> q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (U.raise_val ())))))))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let x6 = elim_exists' () in
    let x7 = elim_exists' () in
    let x8 = elim_exists' () in
    let x9 = elim_exists' () in
    let x10 = elim_exists' () in
    let res = Mktuple10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct11
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> exists_ (fun x6 -> exists_ (fun x7 -> exists_ (fun x8 -> exists_ (fun x9 -> exists_ (fun x10 -> exists_ (fun x11 -> q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (U.raise_val ()))))))))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let x6 = elim_exists' () in
    let x7 = elim_exists' () in
    let x8 = elim_exists' () in
    let x9 = elim_exists' () in
    let x10 = elim_exists' () in
    let x11 = elim_exists' () in
    let res = Mktuple11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ _ _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct12
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> exists_ (fun x6 -> exists_ (fun x7 -> exists_ (fun x8 -> exists_ (fun x9 -> exists_ (fun x10 -> exists_ (fun x11 -> exists_ (fun x12 -> q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (U.raise_val ())))))))))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let x6 = elim_exists' () in
    let x7 = elim_exists' () in
    let x8 = elim_exists' () in
    let x9 = elim_exists' () in
    let x10 = elim_exists' () in
    let x11 = elim_exists' () in
    let x12 = elim_exists' () in
    let res = Mktuple12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ _ _ _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct13
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> exists_ (fun x6 -> exists_ (fun x7 -> exists_ (fun x8 -> exists_ (fun x9 -> exists_ (fun x10 -> exists_ (fun x11 -> exists_ (fun x12 -> exists_ (fun x13 -> q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (U.raise_val ()))))))))))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let x6 = elim_exists' () in
    let x7 = elim_exists' () in
    let x8 = elim_exists' () in
    let x9 = elim_exists' () in
    let x10 = elim_exists' () in
    let x11 = elim_exists' () in
    let x12 = elim_exists' () in
    let x13 = elim_exists' () in
    let res = Mktuple13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ _ _ _ _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct14
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14: Type)
: Tot (compute_gen_elim_nondep_correct_t i0 [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14])
= fun q post intro _ ->
    intro _;
    rewrite_with_trefl (gen_elim_nondep_p _ _ _) (exists_ (fun x1 -> exists_ (fun x2 -> exists_ (fun x3 -> exists_ (fun x4 -> exists_ (fun x5 -> exists_ (fun x6 -> exists_ (fun x7 -> exists_ (fun x8 -> exists_ (fun x9 -> exists_ (fun x10 -> exists_ (fun x11 -> exists_ (fun x12 -> exists_ (fun x13 -> exists_ (fun x14 -> q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (U.raise_val ()) `star` pure (post x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (U.raise_val ())))))))))))))))));
    let x1 = elim_exists' () in
    let x2 = elim_exists' () in
    let x3 = elim_exists' () in
    let x4 = elim_exists' () in
    let x5 = elim_exists' () in
    let x6 = elim_exists' () in
    let x7 = elim_exists' () in
    let x8 = elim_exists' () in
    let x9 = elim_exists' () in
    let x10 = elim_exists' () in
    let x11 = elim_exists' () in
    let x12 = elim_exists' () in
    let x13 = elim_exists' () in
    let x14 = elim_exists' () in
    let res = Mktuple14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 in
    elim_pure _;
    rewrite_with_trefl (q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (U.raise_val ())) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct_default
  (i0: gen_elim_i)
  (t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15: Type) (tq: list Type)
: Tot (compute_gen_elim_nondep_correct_t i0 (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: t8 :: t9 :: t10 :: t11 :: t12 :: t13 :: t14 :: t15 :: tq))
= fun q post intro _ ->
    // default case: no exists is opened
    let res : compute_gen_elim_nondep_a' (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: t8 :: t9 :: t10 :: t11 :: t12 :: t13 :: t14 :: t15 :: tq) = (U.raise_val ()) in
    rewrite_with_trefl (compute_gen_elim_p i0) (compute_uncurry _ (fun _ -> compute_gen_elim_p' i0) _ _ res (U.raise_val ()));
    res

let compute_gen_elim_nondep_correct'
  (i0: gen_elim_i)
  (ty: list Type)
: Tot (compute_gen_elim_nondep_correct_t i0 ty)
= match ty returns compute_gen_elim_nondep_correct_t i0 ty with
  | [] -> compute_gen_elim_nondep_correct0 i0
  | [t1] -> compute_gen_elim_nondep_correct1 i0 t1
  | [t1; t2] -> compute_gen_elim_nondep_correct2 i0 t1 t2
  | [t1; t2; t3] -> compute_gen_elim_nondep_correct3 i0 t1 t2 t3
  | [t1; t2; t3; t4] -> compute_gen_elim_nondep_correct4 i0 t1 t2 t3 t4
  | [t1; t2; t3; t4; t5] -> compute_gen_elim_nondep_correct5 i0 t1 t2 t3 t4 t5
  | [t1; t2; t3; t4; t5; t6] -> compute_gen_elim_nondep_correct6 i0 t1 t2 t3 t4 t5 t6
  | [t1; t2; t3; t4; t5; t6; t7] -> compute_gen_elim_nondep_correct7 i0 t1 t2 t3 t4 t5 t6 t7
  | [t1; t2; t3; t4; t5; t6; t7; t8] -> compute_gen_elim_nondep_correct8 i0 t1 t2 t3 t4 t5 t6 t7 t8
  | [t1; t2; t3; t4; t5; t6; t7; t8; t9] -> compute_gen_elim_nondep_correct9 i0 t1 t2 t3 t4 t5 t6 t7 t8 t9
  | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10] -> compute_gen_elim_nondep_correct10 i0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
  | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11] -> compute_gen_elim_nondep_correct11 i0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11
  | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12] -> compute_gen_elim_nondep_correct12 i0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12
  | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13] -> compute_gen_elim_nondep_correct13 i0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13
  | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14] -> compute_gen_elim_nondep_correct14 i0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 
  | t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: t8 :: t9 :: t10 :: t11 :: t12 :: t13 :: t14 :: t15 :: tq -> compute_gen_elim_nondep_correct_default i0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 tq  

let compute_gen_elim_nondep_correct_0
  (i0: gen_elim_i)
  (i: gen_elim_nondep_t)
= match i returns 
  (sq: squash (check_gen_elim_nondep_sem i0 i)) ->
  GTot (gen_elim_f
    (compute_gen_elim_p i0)
    (compute_gen_elim_nondep_a i0 i)
    (compute_gen_elim_nondep_q0 i0 i)
    (compute_gen_elim_nondep_post0 i0 i)
  )
  with
  | GEDep -> fun _ -> compute_gen_elim_f i0
  | GENonDep ty q post -> fun _ ->
    let intro : vprop_rewrite (compute_gen_elim_p i0) (gen_elim_nondep_p ty q post) = fun _ ->
      compute_gen_elim_tele_correct i0 _;
      rewrite (tele_p _) (tele_p (gen_elim_nondep_sem ty q post));
      gen_elim_nondep_sem_correct ty q post;
      rewrite_equiv (tele_p _) (gen_elim_nondep_p _ _ _)
    in
    compute_gen_elim_nondep_correct' i0 ty q post intro

let compute_gen_elim_nondep_correct
  (i0: gen_elim_i)
  (i: gen_elim_nondep_t)
  (sq: squash (check_gen_elim_nondep_sem i0 i))
: Tot (gen_elim_f
    (compute_gen_elim_p i0)
    (Ghost.erased (compute_gen_elim_nondep_a i0 i))
    (compute_gen_elim_nondep_q i0 i)
    (compute_gen_elim_nondep_post i0 i)
  )
= fun _ ->
  let res0 = compute_gen_elim_nondep_correct_0 i0 i sq _ in
  let res = Ghost.hide res0 in
  rewrite (compute_gen_elim_nondep_q0 i0 i res0) (compute_gen_elim_nondep_q i0 i res);
  res

let coerce_with_smt (#tfrom #tto: Type) (x: tfrom) : Pure tto (requires ( (tfrom == tto))) (ensures (fun _ -> True)) = x

let gen_elim'
  #opened enable_nondep_opt p a q post _ ()
=
  let (i, j) = gen_elim_prop_elim enable_nondep_opt p a q post in
  rewrite p (compute_gen_elim_p i);
  let res' = compute_gen_elim_nondep_correct i j () _ in
  let res : Ghost.erased a = Ghost.hide (coerce_with_smt (Ghost.reveal res')) in
  rewrite (compute_gen_elim_nondep_q i j res') (guard_vprop (q res));
  res

let gen_elim
  #opened #p #a #q #post #sq _
= gen_elim' #opened _ p a q post sq ()

let gen_elim_dep
  #opened #p #a #q #post #sq _
= gen_elim' #opened _ p a q post sq ()
