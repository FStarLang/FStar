module Steel.ST.GenElim.Base
include Steel.ST.Util

module T = FStar.Tactics

let is_fvar     = Reflection.is_fvar
let is_any_fvar = Reflection.is_any_fvar

/// A tactic to automatically generate a unique binder

[@@erasable]
noeq
type gen_unit_elim_i
= | GUEId: (v: vprop) -> gen_unit_elim_i
  | GUEPure: (p: prop) -> gen_unit_elim_i
  | GUEStar: (left: gen_unit_elim_i) -> (right: gen_unit_elim_i) -> gen_unit_elim_i

[@@erasable]
noeq
type gen_elim_i =
  | GEUnit: (i: gen_unit_elim_i) -> gen_elim_i
  | GEStarL: (left: gen_elim_i) -> (right: gen_unit_elim_i) -> gen_elim_i
  | GEStarR: (left: gen_unit_elim_i) -> (right: gen_elim_i) -> gen_elim_i
  | GEStar: (left: gen_elim_i) -> (right: gen_elim_i) -> gen_elim_i
  | GEExistsNoAbs: (#a: Type0) -> (body: (a -> vprop)) -> gen_elim_i // FIXME: generalize the universe
  | GEExistsUnit: (#a: Type0) -> (body: (a -> gen_unit_elim_i)) -> gen_elim_i
  | GEExists: (#a: Type0) -> (body: (a -> gen_elim_i)) -> gen_elim_i

val gen_elim_reduce: unit

[@@ gen_elim_reduce]
let rec compute_gen_unit_elim_p
  (x: gen_unit_elim_i)
: Tot vprop
= match x with
  | GUEId v -> v
  | GUEPure p -> pure p
  | GUEStar left right -> compute_gen_unit_elim_p left `star` compute_gen_unit_elim_p right

[@@ gen_elim_reduce]
let rec compute_gen_unit_elim_q
  (x: gen_unit_elim_i)
: Tot vprop
= match x with
  | GUEId v -> v
  | GUEPure _ -> emp
  | GUEStar left right -> compute_gen_unit_elim_q left `star` compute_gen_unit_elim_q right

[@@gen_elim_reduce; noextract_to "Plugin"]
let rec compute_gen_unit_elim_post
  (x: gen_unit_elim_i)
: Tot prop
= match x with
  | GUEId _ -> True
  | GUEPure p -> p
  | GUEStar left right -> compute_gen_unit_elim_post left /\ compute_gen_unit_elim_post right

[@@gen_elim_reduce]
let rec compute_gen_elim_p
  (x: gen_elim_i)
: Tot vprop
= match x with
  | GEUnit i -> compute_gen_unit_elim_p i
  | GEStarL left right -> compute_gen_elim_p left `star` compute_gen_unit_elim_p right
  | GEStarR left right -> compute_gen_unit_elim_p left `star` compute_gen_elim_p right
  | GEStar left right -> compute_gen_elim_p left `star` compute_gen_elim_p right
  | GEExistsNoAbs #a p -> exists_ p
  | GEExistsUnit #a p -> exists_ (fun x -> compute_gen_unit_elim_p (p x))
  | GEExists #a body -> exists_ (fun x -> compute_gen_elim_p (body x))

let compute_gen_elim_p' = compute_gen_elim_p

[@@ gen_elim_reduce; __steel_reduce__; noextract_to "Plugin"]
let rec compute_gen_elim_a
  (x: gen_elim_i)
: Tot Type0
= match x with
  | GEUnit _ -> unit
  | GEStarL left _ -> compute_gen_elim_a left
  | GEStarR _ right -> compute_gen_elim_a right
  | GEStar left right -> (compute_gen_elim_a left & compute_gen_elim_a right)
  | GEExistsNoAbs #a _
  | GEExistsUnit #a _ -> a
  | GEExists #a body -> dtuple2 a (fun x -> compute_gen_elim_a (body x))

[@@noextract_to "Plugin"]
let dfstp #a #b t = dfst #a #b t
[@@noextract_to "Plugin"]
let dsndp #a #b t = dsnd #a #b t
[@@noextract_to "Plugin"]
let fstp #a #b t = fst #a #b t
[@@noextract_to "Plugin"]
let sndp #a #b t = snd #a #b t

[@@gen_elim_reduce; __steel_reduce__; noextract_to "Plugin"]
let coerce_with_trefl (#tfrom #tto: Type) (x: tfrom) : Pure tto (requires (T.with_tactic T.trefl (tfrom == tto))) (ensures (fun _ -> True)) = x

[@@gen_elim_reduce]
let rec compute_gen_elim_q
  (x: gen_elim_i)
: Tot (compute_gen_elim_a x -> Tot vprop)
  (decreases x)
= match x as x' returns (compute_gen_elim_a x' -> Tot vprop) with
  | GEUnit u -> fun _ -> compute_gen_unit_elim_q u
  | GEStarL left right -> fun v -> compute_gen_elim_q left (coerce_with_trefl v) `star` compute_gen_unit_elim_q right
  | GEStarR left right -> fun v -> compute_gen_unit_elim_q left `star` compute_gen_elim_q right (coerce_with_trefl v)
  | GEStar left right ->
    let tleft = compute_gen_elim_a left in
    let tright = compute_gen_elim_a right in
    fun v ->
      let v' : (tleft & tright) = coerce_with_trefl v in
      compute_gen_elim_q left (fstp #tleft #tright v') `star` compute_gen_elim_q right (sndp #tleft #tright v')
  | GEExistsNoAbs #a p -> p
  | GEExistsUnit #a p -> fun v -> compute_gen_unit_elim_q (p v)
  | GEExists #a body ->
    let dept = (fun x -> compute_gen_elim_a (body x)) in
    fun v ->
    let v' : dtuple2 a dept = coerce_with_trefl v in
    compute_gen_elim_q
      (body (dfstp #a #dept v'))
      (dsndp #a #dept v')

[@@gen_elim_reduce; noextract_to "Plugin"]
let rec compute_gen_elim_post
  (x: gen_elim_i)
: Tot (compute_gen_elim_a x -> Tot prop)
  (decreases x)
= match x as x' returns (compute_gen_elim_a x' -> Tot prop) with
  | GEUnit u -> fun _ -> compute_gen_unit_elim_post u
  | GEStarL left right -> fun v -> compute_gen_elim_post left (coerce_with_trefl v) /\ compute_gen_unit_elim_post right
  | GEStarR left right -> fun v -> compute_gen_unit_elim_post left /\ compute_gen_elim_post right (coerce_with_trefl v)
  | GEStar left right ->
    let tleft = compute_gen_elim_a left in
    let tright = compute_gen_elim_a right in
    fun v ->
      let v' : (tleft & tright) = coerce_with_trefl v in
      compute_gen_elim_post left (fstp #tleft #tright v') /\ compute_gen_elim_post right (sndp #tleft #tright v')
  | GEExistsNoAbs #a p -> fun _ -> True
  | GEExistsUnit #a p -> fun v -> compute_gen_unit_elim_post (p v)
  | GEExists #a body ->
    let dept = (fun x -> compute_gen_elim_a (body x)) in
    fun v ->
    let v' : dtuple2 a dept = coerce_with_trefl v in
    compute_gen_elim_post
      (body (dfstp #a #dept v'))
      (dsndp #a #dept v')

[@@erasable]
noeq
type gen_elim_tele =
  | TRet: vprop -> prop -> gen_elim_tele
  | TExists: (ty: Type u#0) -> (ty -> gen_elim_tele) -> gen_elim_tele

[@@gen_elim_reduce]
let rec tele_star_vprop (i: gen_elim_tele) (v: vprop) (p: prop) : Tot gen_elim_tele (decreases i) =
  match i with
  | TRet v' p' -> TRet (v `star` v') (p /\ p')
  | TExists ty f -> TExists ty (fun x -> tele_star_vprop (f x) v p)

[@@gen_elim_reduce]
let rec tele_star (i1 i2: gen_elim_tele) : Tot gen_elim_tele =
  match i1, i2 with
  | TRet v1 p1, _ -> tele_star_vprop i2 v1 p1
  | _, TRet v2 p2 -> tele_star_vprop i1 v2 p2
  | TExists ty1 f1, TExists ty2 f2 -> TExists ty1 (fun x1 -> TExists ty2 (fun x2 -> tele_star (f1 x1) (f2 x2)))

[@@gen_elim_reduce]
let rec compute_gen_elim_tele (x: gen_elim_i) : Tot gen_elim_tele =
  match x with
  | GEUnit v -> TRet (compute_gen_unit_elim_q v) (compute_gen_unit_elim_post v)
  | GEStarL l ru -> tele_star_vprop (compute_gen_elim_tele l) (compute_gen_unit_elim_q ru) (compute_gen_unit_elim_post ru)
  | GEStarR lu r -> tele_star_vprop (compute_gen_elim_tele r) (compute_gen_unit_elim_q lu) (compute_gen_unit_elim_post lu)
  | GEStar l r -> tele_star (compute_gen_elim_tele l) (compute_gen_elim_tele r)
  | GEExistsNoAbs #ty body -> TExists ty (fun x -> TRet (body x) True)
  | GEExistsUnit #ty body -> TExists ty (fun x -> TRet (compute_gen_unit_elim_q (body x)) (compute_gen_unit_elim_post (body x)))
  | GEExists #ty f -> TExists ty (fun x -> compute_gen_elim_tele (f x))

[@@gen_elim_reduce; noextract_to "Plugin"]
let rec curried_function_type (x: list (Type u#a)) (ret_t: Type u#(max a b)) : Tot (Type u#(max a b)) =
  match x with
  | [] -> ret_t
  | t1 :: q -> t1 -> Tot (curried_function_type q ret_t)

[@@erasable]
noeq
type gen_elim_nondep_t =
| GENonDep: (ty: list Type0) -> curried_function_type ty vprop -> curried_function_type ty prop -> gen_elim_nondep_t
| GEDep

[@@gen_elim_reduce]
let mk_gen_elim_nondep
  (ty: list Type0)
  (tvprop: Type)
  (q: tvprop)
  (tprop: Type)
  (post: tprop)
: Pure gen_elim_nondep_t
  (requires (
    tvprop == curried_function_type ty vprop /\
    tprop == curried_function_type ty prop
  ))
  (ensures (fun _ -> True))
= GENonDep ty q post

[@@gen_elim_reduce]
let mk_gen_elim_nondep_by_tac
  (ty: list Type0)
  (tvprop: Type)
  (q: tvprop)
  (tprop: Type)
  (post: tprop)
: Pure gen_elim_nondep_t
  (requires (
    T.with_tactic (fun _ -> T.norm [delta_attr [(`%gen_elim_reduce)]; iota; zeta]) (tvprop == curried_function_type ty vprop) /\
    T.with_tactic (fun _ -> T.norm [delta_attr [(`%gen_elim_reduce)]; iota; zeta]) (tprop == curried_function_type ty prop)
  ))
  (ensures (fun _ -> True))
= GENonDep ty q post

[@@gen_elim_reduce]
let rec gen_elim_nondep_sem (ty: list Type0) : Tot (curried_function_type ty vprop -> curried_function_type ty prop -> Tot gen_elim_tele) =
  match ty as ty' returns curried_function_type ty' vprop -> curried_function_type ty' prop -> Tot gen_elim_tele with
  | [] -> fun q post -> TRet q post
  | t :: tq -> fun q post -> TExists t (fun x -> gen_elim_nondep_sem tq (q x) (post x))

[@@gen_elim_reduce; noextract_to "Plugin"]
let check_gen_elim_nondep_sem (i: gen_elim_i) (nd: gen_elim_nondep_t) : Tot prop =
  match nd with
  | GENonDep ty q post -> compute_gen_elim_tele i == gen_elim_nondep_sem ty q post
  | GEDep -> True

[@@gen_elim_reduce; noextract_to "Plugin"]
let compute_gen_elim_nondep_a' (ty: list Type0) : Tot Type0 =
    match ty with
    | [] -> unit
    | [t1] -> t1
    | [t1; t2] -> tuple2 t1 t2
    | [t1; t2; t3] -> tuple3 t1 t2 t3
    | [t1; t2; t3; t4] -> tuple4 t1 t2 t3 t4
    | [t1; t2; t3; t4; t5] -> tuple5 t1 t2 t3 t4 t5
    | [t1; t2; t3; t4; t5; t6] -> tuple6 t1 t2 t3 t4 t5 t6
    | [t1; t2; t3; t4; t5; t6; t7] -> tuple7 t1 t2 t3 t4 t5 t6 t7
    | [t1; t2; t3; t4; t5; t6; t7; t8] -> tuple8 t1 t2 t3 t4 t5 t6 t7 t8
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9] -> tuple9 t1 t2 t3 t4 t5 t6 t7 t8 t9
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10] -> tuple10 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11] -> tuple11 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12] -> tuple12 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13] -> tuple13 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14] -> tuple14 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14
    | _ -> unit // unsupported

[@@gen_elim_reduce; noextract_to "Plugin"]
let compute_gen_elim_nondep_a (i0: gen_elim_i) (i: gen_elim_nondep_t) : Tot Type0 =
  match i with
  | GENonDep ty q post -> compute_gen_elim_nondep_a' ty
  | GEDep -> compute_gen_elim_a i0

[@@gen_elim_reduce; noextract_to "Plugin"]
let compute_uncurry (ret_type: Type u#a) (def: ret_type) (ty: list Type0) : curried_function_type ty ret_type -> compute_gen_elim_nondep_a' ty -> ret_type =
    match ty as ty' returns (curried_function_type ty' ret_type -> compute_gen_elim_nondep_a' ty' -> ret_type) with
    | [] -> fun q _ -> q
    | [t1] -> fun q -> q
    | [t1; t2] -> fun q x -> q (fstp x) (sndp x)
    | [t1; t2; t3] -> fun q x -> q x._1 x._2 x._3
    | [t1; t2; t3; t4] -> fun q x -> q x._1 x._2 x._3 x._4
    | [t1; t2; t3; t4; t5] -> fun q x -> q x._1 x._2 x._3 x._4 x._5
    | [t1; t2; t3; t4; t5; t6] -> fun q x -> q x._1 x._2 x._3 x._4 x._5 x._6
    | [t1; t2; t3; t4; t5; t6; t7] -> fun q x -> q x._1 x._2 x._3 x._4 x._5 x._6 x._7
    | [t1; t2; t3; t4; t5; t6; t7; t8] -> fun q x -> q x._1 x._2 x._3 x._4 x._5 x._6 x._7 x._8
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9] -> fun q x -> q x._1 x._2 x._3 x._4 x._5 x._6 x._7 x._8 x._9
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10] -> fun q x -> q x._1 x._2 x._3 x._4 x._5 x._6 x._7 x._8 x._9 x._10
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11] -> fun q x -> q x._1 x._2 x._3 x._4 x._5 x._6 x._7 x._8 x._9 x._10 x._11
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12] -> fun q x -> q x._1 x._2 x._3 x._4 x._5 x._6 x._7 x._8 x._9 x._10 x._11 x._12
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13] -> fun q x -> q x._1 x._2 x._3 x._4 x._5 x._6 x._7 x._8 x._9 x._10 x._11 x._12 x._13
    | [t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14] -> fun q x -> q x._1 x._2 x._3 x._4 x._5 x._6 x._7 x._8 x._9 x._10 x._11 x._12 x._13 x._14
    | _ -> fun _ _ -> def

[@@gen_elim_reduce]
let compute_gen_elim_nondep_q0 (i0: gen_elim_i) (i: gen_elim_nondep_t) : Tot (compute_gen_elim_nondep_a i0 i -> vprop) =
  match i with
  | GENonDep ty q post -> compute_uncurry vprop (compute_gen_elim_p' i0) ty q
      // that default value does not reduce, on purpose, to make the tactic fail if the type list is too long
  | GEDep -> compute_gen_elim_q i0

[@@gen_elim_reduce]
let compute_gen_elim_nondep_q (i0: gen_elim_i) (i: gen_elim_nondep_t) (x: Ghost.erased (compute_gen_elim_nondep_a i0 i)) : Tot vprop =
  compute_gen_elim_nondep_q0 i0 i (Ghost.reveal x)

[@@gen_elim_reduce; noextract_to "Plugin"]
let compute_gen_elim_nondep_post0 (i0: gen_elim_i) (i: gen_elim_nondep_t) : Tot (compute_gen_elim_nondep_a i0 i -> prop) =
  match i with
  | GENonDep ty q post -> compute_uncurry prop True ty post
  | GEDep -> compute_gen_elim_post i0

[@@gen_elim_reduce; noextract_to "Plugin"]
let compute_gen_elim_nondep_post (i0: gen_elim_i) (i: gen_elim_nondep_t) (x: Ghost.erased (compute_gen_elim_nondep_a i0 i)) : Tot prop =
  compute_gen_elim_nondep_post0 i0 i (Ghost.reveal x)

let is_squash (t:T.term) : T.Tac bool =
  is_any_fvar t [`%squash; `%auto_squash]

let is_star_or_vstar (t:T.term) : T.Tac bool =
  is_any_fvar t [`%star; `%VStar]

let rec term_has_head
  (t: T.term)
  (head: T.term)
: T.Tac bool
= let (hd, tl) = T.collect_app t in
  if hd `T.term_eq_old` head
  then true
  else if is_star_or_vstar hd
  then
    match tl with
    | [tg, T.Q_Explicit; td, T.Q_Explicit] ->
      if term_has_head tg head
      then true
      else term_has_head td head
    | _ -> false
  else false

let rec solve_gen_unit_elim
  (tl': T.term)
: T.Tac T.term
= 
      if not (term_has_head tl' (`pure))
      then T.mk_app (`GUEId) [tl', T.Q_Explicit]
      else
        let (hd, tl) = T.collect_app tl' in
        if hd `is_fvar` (`%pure)
        then T.mk_app (`GUEPure) tl
        else if is_star_or_vstar hd
        then match tl with
        | [t1, T.Q_Explicit; t2, T.Q_Explicit] ->
          let t1' = solve_gen_unit_elim t1 in
          let t2' = solve_gen_unit_elim t2 in
          T.mk_app (`GUEStar) [t1', T.Q_Explicit; t2', T.Q_Explicit]
        | _ -> T.fail "ill-formed star"
        else
          T.mk_app (`GUEId) [tl', T.Q_Explicit]

let abstr_has_exists
  (t: T.term)
: T.Tac bool
= match T.inspect t with
  | T.Tv_Abs _ body -> term_has_head body (`exists_)
  | _ -> false

let rec solve_gen_elim
  (tl': T.term)
: T.Tac T.term
= 
      if not (term_has_head tl' (`exists_))
      then begin
        let t' = solve_gen_unit_elim tl' in
        T.mk_app (`GEUnit) [t', T.Q_Explicit]
      end else
        let (hd, lbody) = T.collect_app tl' in
        if hd `is_fvar` (`%exists_)
        then
          let (ty, body) =
            match lbody with
            | [(ty, T.Q_Implicit); (body, T.Q_Explicit)] -> ([(ty, T.Q_Implicit)], body)
            | [(body, T.Q_Explicit)] -> ([], body)
            | _ -> T.fail "ill-formed exists_"
          in
          begin match T.inspect body with
            | T.Tv_Abs b abody ->
              if not (term_has_head abody (`exists_))
              then
                let body' = solve_gen_unit_elim abody in
                T.mk_app (`GEExistsUnit) (ty `List.Tot.append` [T.mk_abs [b] body', T.Q_Explicit])
              else
                let body' = solve_gen_elim abody in
                T.mk_app (`GEExists) (ty `List.Tot.append` [T.mk_abs [b] body', T.Q_Explicit])
            | _ ->
              T.mk_app (`GEExistsNoAbs) lbody
          end
        else if is_star_or_vstar hd
        then
          match lbody with
          | [(tl, T.Q_Explicit); (tr, T.Q_Explicit)] ->
            if term_has_head tl (`exists_)
            then
              let tl' = solve_gen_elim tl in
              if term_has_head tr (`exists_)
              then
                let tr' = solve_gen_elim tr in
                T.mk_app (`GEStar) [tl', T.Q_Explicit; tr', T.Q_Explicit]
              else
                let tr' = solve_gen_unit_elim tr in
                T.mk_app (`GEStarL) [tl', T.Q_Explicit; tr', T.Q_Explicit]
            else (* here, term_has_head tr (`exists_) holds, because otherwise we are in case (not (term_has_head tl (`exists_))) above *)
              let tl' = solve_gen_unit_elim tl in
              let tr' = solve_gen_elim tr in
              T.mk_app (`GEStarR) [tl', T.Q_Explicit; tr', T.Q_Explicit]
          | _ -> T.fail "ill-formed star"
        else
          T.mk_app (`GEUnit) [T.mk_app (`GUEId) lbody, T.Q_Explicit]

[@@ noextract_to "Plugin"]
val gen_elim_prop
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Tot prop

val gen_elim_prop_intro'
  (i: gen_elim_i)
  (j: gen_elim_nondep_t)
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
  (sq_p: squash (p == compute_gen_elim_p i))
  (sq_j: squash (check_gen_elim_nondep_sem i j))
  (sq_a: squash (a == compute_gen_elim_nondep_a i j))
  (sq_q: squash (q == compute_gen_elim_nondep_q i j))
  (sq_post: squash (post == compute_gen_elim_nondep_post i j))
: Lemma
  (gen_elim_prop enable_nondep_opt p a q post)

let gen_elim_prop_intro
  (i: gen_elim_i)
  (ty: list Type0)
  (tvprop: Type)
  (q0: tvprop)
  (tprop: Type)
  (post0: tprop)
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
  (sq_tvprop: squash (tvprop == curried_function_type ty vprop))
  (sq_tprop: squash (tprop == curried_function_type ty prop))
  (sq_p: squash (p == compute_gen_elim_p i))
  (sq_j: squash (check_gen_elim_nondep_sem i (mk_gen_elim_nondep ty tvprop q0 tprop post0)))
  (sq_a: squash (a == compute_gen_elim_nondep_a i (mk_gen_elim_nondep ty tvprop q0 tprop post0)))
  (sq_q: squash (q == compute_gen_elim_nondep_q i (mk_gen_elim_nondep ty tvprop q0 tprop post0)))
  (sq_post: squash (post == compute_gen_elim_nondep_post i (mk_gen_elim_nondep ty tvprop q0 tprop post0)))
: Lemma
  (gen_elim_prop enable_nondep_opt p a q post)
= gen_elim_prop_intro' i (mk_gen_elim_nondep ty tvprop q0 tprop post0) enable_nondep_opt p a q post sq_p sq_j sq_a sq_q sq_post

val gen_elim_prop_elim
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Ghost (gen_elim_i & gen_elim_nondep_t)
  (requires gen_elim_prop enable_nondep_opt p a q post)
  (ensures (fun (i, j) ->
    p == compute_gen_elim_p i /\
    check_gen_elim_nondep_sem i j /\
    a == compute_gen_elim_nondep_a i j /\
    q == compute_gen_elim_nondep_q i j /\
    post == compute_gen_elim_nondep_post i j
  ))

[@@noextract_to "Plugin"]
let gen_elim_prop_placeholder
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Tot prop
= True

let gen_elim_prop_placeholder_intro
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Lemma (gen_elim_prop_placeholder enable_nondep_opt p a q post)
= ()

let rec solve_gen_elim_nondep' (fuel: nat) (rev_types_and_binders: list (T.term & T.binder)) (t: T.term) : T.Tac (option (tuple5 T.term T.term T.term T.term T.term)) =
  if fuel = 0
  then None
  else
    let (hd, tl) = T.collect_app t in
    if hd `is_fvar` (`%TRet)
    then match tl with
    | [(v, T.Q_Explicit); (p, T.Q_Explicit)] ->
      let cons_type (accu: (unit -> T.Tac T.term)) (tb: (T.term & T.binder)) () : T.Tac T.term =
        let (ty, _) = tb in
        let tl = accu () in
        T.mk_app (`Cons) [(`Type0), T.Q_Implicit; ty, T.Q_Explicit; tl, T.Q_Explicit]
      in
      let nil_type () : T.Tac T.term = T.mk_app (`Nil) [(`Type0), T.Q_Implicit] in
      let type_list = List.Tot.fold_left cons_type nil_type rev_types_and_binders () in
      let type_list_typechecks =
        let open T in
        try
          let env = cur_env () in
          let ty = tc env type_list in
          ty `term_eq_old` (`(list Type0))
        with _ -> false
      in
      if not type_list_typechecks
      then None
      else
        let binders = List.Tot.map snd (List.Tot.rev rev_types_and_binders) in
        let norm_term = T.norm_term [delta_attr [(`%gen_elim_reduce)]; zeta; iota] in
        let v' = T.mk_abs binders v in
        let tv' = norm_term (T.mk_app (`curried_function_type) [type_list, T.Q_Explicit; (`vprop), T.Q_Explicit]) in
        let p' = T.mk_abs binders p in
        let tp' = norm_term (T.mk_app (`curried_function_type) [type_list, T.Q_Explicit; (`prop), T.Q_Explicit]) in
        Some (Mktuple5
          type_list
          tv'
          v'
          tp'
          p'
        )
    | _ -> None
    else if hd `is_fvar` (`%TExists)
    then match tl with
    | [(ty, _); (f, T.Q_Explicit)] ->
      begin match T.inspect f with
      | T.Tv_Abs bv body -> solve_gen_elim_nondep' (fuel - 1) ((ty, bv) :: rev_types_and_binders) body
      | _ -> None
      end
    | _ -> None
    else None

let solve_gen_elim_nondep0 (enable_nondep_opt: bool) (t: T.term) : T.Tac (option (tuple5 T.term T.term T.term T.term T.term)) =
  if enable_nondep_opt
  then
    let open T in
    try
      let tele = mk_app (`compute_gen_elim_tele) [t, Q_Explicit] in
      let t' = norm_term [delta_attr [(`%gen_elim_reduce)]; zeta; iota] tele in
      solve_gen_elim_nondep' 15 [] t'  // fuel necessary because F* standard tuple types only go from 0 up to 14 elts
    with _ -> None
  else None

let solve_gen_elim_nondep (enable_nondep_opt: bool) (t: T.term) : T.Tac T.term =
  match solve_gen_elim_nondep0 enable_nondep_opt t with
  | None -> (`GEDep)
  | Some (Mktuple5
          type_list
          tv'
          v'
          tp'
          p'
        ) -> T.mk_app (`mk_gen_elim_nondep_by_tac) [
          type_list, T.Q_Explicit;
          tv', T.Q_Explicit;
          v', T.Q_Explicit;
          tp', T.Q_Explicit;
          p', T.Q_Explicit;
        ]

let solve_gen_elim_prop
  ()
: T.Tac unit
=
  let (hd, tl) = T.collect_app (T.cur_goal ()) in
  if not (is_squash hd)
  then T.fail "not a squash goal";
  match tl with
  | [body1, T.Q_Explicit] ->
    let (hd1, tl1) = T.collect_app body1 in
    if not (hd1 `is_fvar` (`%gen_elim_prop))
    then T.fail "not a gen_elim_prop goal";
    begin match List.Tot.filter (fun (_, x) -> T.Q_Explicit? x) tl1 with
    | [(enable_nondep_opt_tm, _); (p, _); (a, _); (q, _); (post, _)] ->
      let enable_nondep_opt = enable_nondep_opt_tm `T.term_eq_old` (`true) in
      let i' = solve_gen_elim p in
      let norm () = T.norm [delta_attr [(`%gen_elim_reduce)]; zeta; iota] in
      begin match solve_gen_elim_nondep0 enable_nondep_opt i' with
      | None ->
        T.apply_lemma (T.mk_app (`gen_elim_prop_intro') [
          i', T.Q_Explicit;
          (`GEDep), T.Q_Explicit;
        ])
      | Some (Mktuple5 type_list tvprop q0 tprop post0) ->
        T.apply_lemma (T.mk_app (`gen_elim_prop_intro) [
          i', T.Q_Explicit;
          type_list, T.Q_Explicit;
          tvprop, T.Q_Explicit;
          q0, T.Q_Explicit;
          tprop, T.Q_Explicit;
          post0, T.Q_Explicit;
        ]);
        T.focus (fun _ -> norm (); T.trefl ()); // tvprop
        T.focus (fun _ -> norm (); T.trefl ()) // tprop
      end;
      T.focus (fun _ -> norm (); T.trefl ()); // p
      T.focus (fun _ -> norm (); T.trivial (); T.qed ()); // j
      T.focus (fun _ -> norm (); T.trefl ()); // a
      T.focus (fun _ -> norm (); T.trefl ()); // q
      T.focus (fun _ -> norm (); T.trefl ()) // post
    | _ -> T.fail "ill formed gen_elim_prop"
    end
  | _ -> T.fail "ill-formed squash"

let solve_gen_elim_prop_placeholder
  ()
: T.Tac bool
=
  let (hd, tl) = T.collect_app (T.cur_goal ()) in
  if not (is_squash hd)
  then T.fail "not a squash goal";
  match tl with
  | [body1, T.Q_Explicit] ->
    let (hd1, tl1) = T.collect_app body1 in
    if not (hd1 `is_fvar` (`%gen_elim_prop_placeholder))
    then T.fail "not a gen_elim_prop_placeholder goal";
    begin match List.Tot.filter (fun (_, x) -> T.Q_Explicit? x) tl1 with
    | [(enable_nondep_opt_tm, _); (p, _); (a, _); (q, _); (post, _)] ->
      if slterm_nbr_uvars p <> 0
      then T.fail "pre-resource not solved yet";
      let a_is_uvar = T.Tv_Uvar? (T.inspect a) in
      let q_is_uvar = T.Tv_Uvar? (T.inspect q) in
      let post_is_uvar = T.Tv_Uvar? (T.inspect post) in
      if not (a_is_uvar && q_is_uvar && post_is_uvar)
      then T.fail "gen_elim_prop_placeholder is already solved";
      let enable_nondep_opt = enable_nondep_opt_tm `T.term_eq_old` (`true) in
      let i' = solve_gen_elim p in
      let j' = solve_gen_elim_nondep enable_nondep_opt i' in
      let norm_term = T.norm_term [delta_attr [(`%gen_elim_reduce)]; zeta; iota] in
      let a' = norm_term (T.mk_app (`compute_gen_elim_nondep_a) [i', T.Q_Explicit; j', T.Q_Explicit]) in
      let q' = norm_term (T.mk_app (`compute_gen_elim_nondep_q) [i', T.Q_Explicit; j', T.Q_Explicit]) in
      let post' = norm_term (T.mk_app (`compute_gen_elim_nondep_post) [i', T.Q_Explicit; j', T.Q_Explicit]) in
      T.unshelve a;
      T.exact a';
      T.unshelve q;
      T.exact q';
      T.unshelve post;
      T.exact post';
      T.apply_lemma (`gen_elim_prop_placeholder_intro);
      true
    | _ -> T.fail "ill-formed gen_elim_prop_placeholder"
    end
  | _ -> T.fail "ill-formed squash"

[@@ resolve_implicits; framing_implicit; plugin;
    override_resolve_implicits_handler framing_implicit [`%Steel.Effect.Common.init_resolve_tac]]
let init_resolve_tac () = init_resolve_tac'
  [(`gen_elim_prop_placeholder), solve_gen_elim_prop_placeholder]
