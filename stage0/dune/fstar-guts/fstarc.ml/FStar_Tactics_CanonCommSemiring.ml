open Prims
let term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool=
  FStar_Reflection_TermEq_Simple.term_eq
type ('a, 'cmuadd, 'cmumult) distribute_left_lemma = unit
type ('a, 'cmuadd, 'cmumult) distribute_right_lemma = unit
type ('a, 'cmuadd, 'cmumult) mult_zero_l_lemma = unit
type ('a, 'cmuadd, 'opp) add_opp_r_lemma = unit
type 'a cr =
  | CR of 'a FStar_Algebra_CommMonoid.cm * 'a FStar_Algebra_CommMonoid.cm *
  ('a -> 'a) * unit * unit * unit 
let uu___is_CR (projectee : 'a cr) : Prims.bool= true
let __proj__CR__item__cm_add (projectee : 'a cr) :
  'a FStar_Algebra_CommMonoid.cm=
  match projectee with
  | CR (cm_add, cm_mult, opp, add_opp, distribute, mult_zero_l) -> cm_add
let __proj__CR__item__cm_mult (projectee : 'a cr) :
  'a FStar_Algebra_CommMonoid.cm=
  match projectee with
  | CR (cm_add, cm_mult, opp, add_opp, distribute, mult_zero_l) -> cm_mult
let __proj__CR__item__opp (projectee : 'a cr) : 'a -> 'a=
  match projectee with
  | CR (cm_add, cm_mult, opp, add_opp, distribute, mult_zero_l) -> opp




let norm_fully (x : 'a) : 'a= x
type index = Prims.nat
type varlist =
  | Nil_var 
  | Cons_var of index * varlist 
let uu___is_Nil_var (projectee : varlist) : Prims.bool=
  match projectee with | Nil_var -> true | uu___ -> false
let uu___is_Cons_var (projectee : varlist) : Prims.bool=
  match projectee with | Cons_var (_0, _1) -> true | uu___ -> false
let __proj__Cons_var__item___0 (projectee : varlist) : index=
  match projectee with | Cons_var (_0, _1) -> _0
let __proj__Cons_var__item___1 (projectee : varlist) : varlist=
  match projectee with | Cons_var (_0, _1) -> _1
type 'a canonical_sum =
  | Nil_monom 
  | Cons_monom of 'a * varlist * 'a canonical_sum 
  | Cons_varlist of varlist * 'a canonical_sum 
let uu___is_Nil_monom (projectee : 'a canonical_sum) : Prims.bool=
  match projectee with | Nil_monom -> true | uu___ -> false
let uu___is_Cons_monom (projectee : 'a canonical_sum) : Prims.bool=
  match projectee with | Cons_monom (_0, _1, _2) -> true | uu___ -> false
let __proj__Cons_monom__item___0 (projectee : 'a canonical_sum) : 'a=
  match projectee with | Cons_monom (_0, _1, _2) -> _0
let __proj__Cons_monom__item___1 (projectee : 'a canonical_sum) : varlist=
  match projectee with | Cons_monom (_0, _1, _2) -> _1
let __proj__Cons_monom__item___2 (projectee : 'a canonical_sum) :
  'a canonical_sum= match projectee with | Cons_monom (_0, _1, _2) -> _2
let uu___is_Cons_varlist (projectee : 'a canonical_sum) : Prims.bool=
  match projectee with | Cons_varlist (_0, _1) -> true | uu___ -> false
let __proj__Cons_varlist__item___0 (projectee : 'a canonical_sum) : varlist=
  match projectee with | Cons_varlist (_0, _1) -> _0
let __proj__Cons_varlist__item___1 (projectee : 'a canonical_sum) :
  'a canonical_sum= match projectee with | Cons_varlist (_0, _1) -> _1
let rec varlist_lt (x : varlist) (y : varlist) : Prims.bool=
  match (x, y) with
  | (Nil_var, Cons_var (uu___, uu___1)) -> true
  | (Cons_var (i, xs), Cons_var (j, ys)) ->
      if i < j then true else (i = j) && (varlist_lt xs ys)
  | (uu___, uu___1) -> false
let rec varlist_merge (l1 : varlist) (l2 : varlist) : varlist=
  match (l1, l2) with
  | (uu___, Nil_var) -> l1
  | (Nil_var, uu___) -> l2
  | (Cons_var (v1, t1), Cons_var (v2, t2)) -> vm_aux v1 t1 l2
and vm_aux (v1 : index) (t1 : varlist) (l2 : varlist) : varlist=
  match l2 with
  | Cons_var (v2, t2) ->
      if v1 < v2
      then Cons_var (v1, (varlist_merge t1 l2))
      else Cons_var (v2, (vm_aux v1 t1 t2))
  | uu___ -> Cons_var (v1, t1)
let rec canonical_sum_merge :
  'a . 'a cr -> 'a canonical_sum -> 'a canonical_sum -> 'a canonical_sum =
  fun r s1 s2 ->
    let aplus =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_add r) in
    let aone =
      FStar_Algebra_CommMonoid.__proj__CM__item__unit
        (__proj__CR__item__cm_mult r) in
    match s1 with
    | Cons_monom (c1, l1, t1) -> csm_aux r c1 l1 t1 s2
    | Cons_varlist (l1, t1) -> csm_aux r aone l1 t1 s2
    | Nil_monom -> s2
and csm_aux :
  'a .
    'a cr ->
      'a ->
        varlist -> 'a canonical_sum -> 'a canonical_sum -> 'a canonical_sum
  =
  fun r c1 l1 t1 s2 ->
    let aplus =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_add r) in
    let aone =
      FStar_Algebra_CommMonoid.__proj__CM__item__unit
        (__proj__CR__item__cm_mult r) in
    match s2 with
    | Cons_monom (c2, l2, t2) ->
        if l1 = l2
        then Cons_monom ((aplus c1 c2), l1, (canonical_sum_merge r t1 t2))
        else
          if varlist_lt l1 l2
          then Cons_monom (c1, l1, (canonical_sum_merge r t1 s2))
          else Cons_monom (c2, l2, (csm_aux r c1 l1 t1 t2))
    | Cons_varlist (l2, t2) ->
        if l1 = l2
        then Cons_monom ((aplus c1 aone), l1, (canonical_sum_merge r t1 t2))
        else
          if varlist_lt l1 l2
          then Cons_monom (c1, l1, (canonical_sum_merge r t1 s2))
          else Cons_varlist (l2, (csm_aux r c1 l1 t1 t2))
    | Nil_monom -> Cons_monom (c1, l1, t1)
let rec monom_insert :
  'a . 'a cr -> 'a -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r c1 l1 s2 ->
    let aplus =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_add r) in
    let aone =
      FStar_Algebra_CommMonoid.__proj__CM__item__unit
        (__proj__CR__item__cm_mult r) in
    match s2 with
    | Cons_monom (c2, l2, t2) ->
        if l1 = l2
        then Cons_monom ((aplus c1 c2), l1, t2)
        else
          if varlist_lt l1 l2
          then Cons_monom (c1, l1, s2)
          else Cons_monom (c2, l2, (monom_insert r c1 l1 t2))
    | Cons_varlist (l2, t2) ->
        if l1 = l2
        then Cons_monom ((aplus c1 aone), l1, t2)
        else
          if varlist_lt l1 l2
          then Cons_monom (c1, l1, s2)
          else Cons_varlist (l2, (monom_insert r c1 l1 t2))
    | Nil_monom ->
        if c1 = aone
        then Cons_varlist (l1, Nil_monom)
        else Cons_monom (c1, l1, Nil_monom)
let varlist_insert (r : 'a cr) (l1 : varlist) (s2 : 'a canonical_sum) :
  'a canonical_sum=
  let aone =
    FStar_Algebra_CommMonoid.__proj__CM__item__unit
      (__proj__CR__item__cm_mult r) in
  monom_insert r aone l1 s2
let rec canonical_sum_scalar :
  'a . 'a cr -> 'a -> 'a canonical_sum -> 'a canonical_sum =
  fun r c0 s ->
    let amult =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_mult r) in
    match s with
    | Cons_monom (c, l, t) ->
        Cons_monom ((amult c0 c), l, (canonical_sum_scalar r c0 t))
    | Cons_varlist (l, t) ->
        Cons_monom (c0, l, (canonical_sum_scalar r c0 t))
    | Nil_monom -> Nil_monom
let rec canonical_sum_scalar2 :
  'a . 'a cr -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r l0 s ->
    match s with
    | Cons_monom (c, l, t) ->
        monom_insert r c (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t)
    | Cons_varlist (l, t) ->
        varlist_insert r (varlist_merge l0 l) (canonical_sum_scalar2 r l0 t)
    | Nil_monom -> Nil_monom
let rec canonical_sum_scalar3 :
  'a . 'a cr -> 'a -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r c0 l0 s ->
    let amult =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_mult r) in
    match s with
    | Cons_monom (c, l, t) ->
        monom_insert r (amult c0 c) (varlist_merge l0 l)
          (canonical_sum_scalar3 r c0 l0 t)
    | Cons_varlist (l, t) ->
        monom_insert r c0 (varlist_merge l0 l)
          (canonical_sum_scalar3 r c0 l0 t)
    | Nil_monom -> s
let rec canonical_sum_prod :
  'a . 'a cr -> 'a canonical_sum -> 'a canonical_sum -> 'a canonical_sum =
  fun r s1 s2 ->
    match s1 with
    | Cons_monom (c1, l1, t1) ->
        canonical_sum_merge r (canonical_sum_scalar3 r c1 l1 s2)
          (canonical_sum_prod r t1 s2)
    | Cons_varlist (l1, t1) ->
        canonical_sum_merge r (canonical_sum_scalar2 r l1 s2)
          (canonical_sum_prod r t1 s2)
    | Nil_monom -> s1
type 'a spolynomial =
  | SPvar of index 
  | SPconst of 'a 
  | SPplus of 'a spolynomial * 'a spolynomial 
  | SPmult of 'a spolynomial * 'a spolynomial 
let uu___is_SPvar (projectee : 'a spolynomial) : Prims.bool=
  match projectee with | SPvar _0 -> true | uu___ -> false
let __proj__SPvar__item___0 (projectee : 'a spolynomial) : index=
  match projectee with | SPvar _0 -> _0
let uu___is_SPconst (projectee : 'a spolynomial) : Prims.bool=
  match projectee with | SPconst _0 -> true | uu___ -> false
let __proj__SPconst__item___0 (projectee : 'a spolynomial) : 'a=
  match projectee with | SPconst _0 -> _0
let uu___is_SPplus (projectee : 'a spolynomial) : Prims.bool=
  match projectee with | SPplus (_0, _1) -> true | uu___ -> false
let __proj__SPplus__item___0 (projectee : 'a spolynomial) : 'a spolynomial=
  match projectee with | SPplus (_0, _1) -> _0
let __proj__SPplus__item___1 (projectee : 'a spolynomial) : 'a spolynomial=
  match projectee with | SPplus (_0, _1) -> _1
let uu___is_SPmult (projectee : 'a spolynomial) : Prims.bool=
  match projectee with | SPmult (_0, _1) -> true | uu___ -> false
let __proj__SPmult__item___0 (projectee : 'a spolynomial) : 'a spolynomial=
  match projectee with | SPmult (_0, _1) -> _0
let __proj__SPmult__item___1 (projectee : 'a spolynomial) : 'a spolynomial=
  match projectee with | SPmult (_0, _1) -> _1
let rec spolynomial_normalize :
  'a . 'a cr -> 'a spolynomial -> 'a canonical_sum =
  fun r p ->
    match p with
    | SPvar i -> Cons_varlist ((Cons_var (i, Nil_var)), Nil_monom)
    | SPconst c -> Cons_monom (c, Nil_var, Nil_monom)
    | SPplus (l, q) ->
        canonical_sum_merge r (spolynomial_normalize r l)
          (spolynomial_normalize r q)
    | SPmult (l, q) ->
        canonical_sum_prod r (spolynomial_normalize r l)
          (spolynomial_normalize r q)
let rec canonical_sum_simplify :
  'a . 'a cr -> 'a canonical_sum -> 'a canonical_sum =
  fun r s ->
    let azero =
      FStar_Algebra_CommMonoid.__proj__CM__item__unit
        (__proj__CR__item__cm_add r) in
    let aone =
      FStar_Algebra_CommMonoid.__proj__CM__item__unit
        (__proj__CR__item__cm_mult r) in
    let aplus =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_add r) in
    match s with
    | Cons_monom (c, l, t) ->
        if c = azero
        then canonical_sum_simplify r t
        else
          if c = aone
          then Cons_varlist (l, (canonical_sum_simplify r t))
          else Cons_monom (c, l, (canonical_sum_simplify r t))
    | Cons_varlist (l, t) -> Cons_varlist (l, (canonical_sum_simplify r t))
    | Nil_monom -> s
let spolynomial_simplify (r : 'a cr) (p : 'a spolynomial) : 'a canonical_sum=
  canonical_sum_simplify r (spolynomial_normalize r p)
type var = Prims.nat
type 'a vmap = ((var * 'a) Prims.list * 'a)
let update (x : var) (xa : 'a) (vm : 'a vmap) : 'a vmap=
  let uu___ = vm in match uu___ with | (l, y) -> (((x, xa) :: l), y)
let rec quote_list :
  'a .
    FStar_Tactics_NamedView.term ->
      ('a ->
         (FStar_Tactics_NamedView.term, Obj.t) FStar_Tactics_Effect.tac_repr)
        ->
        'a Prims.list ->
          (FStar_Tactics_NamedView.term, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun ta quotea xs ->
    match xs with
    | [] ->
        (fun uu___ ->
           FStar_Reflection_V2_Derived.mk_app
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "Nil"])))
             [(ta, FStarC_Reflection_V2_Data.Q_Implicit)])
    | x::xs' ->
        FStar_Tactics_Effect.tac_bind () ()
          (FStar_Tactics_Effect.tac_bind () ()
             (FStar_Tactics_Effect.tac_bind () ()
                (FStar_Tactics_Effect.tac_bind () () (quotea x)
                   (fun uu___ uu___1 ->
                      (uu___, FStarC_Reflection_V2_Data.Q_Explicit)))
                (fun uu___ ps ->
                   let x1 =
                     let x2 =
                       let x3 = quote_list ta quotea xs' ps in
                       (x3, FStarC_Reflection_V2_Data.Q_Explicit) in
                     [x2] in
                   uu___ :: x1))
             (fun uu___ uu___1 -> (ta, FStarC_Reflection_V2_Data.Q_Implicit)
                :: uu___))
          (fun uu___ uu___1 ->
             FStar_Reflection_V2_Derived.mk_app
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "Cons"])))
               uu___)
let quote_vm (ta : FStar_Tactics_NamedView.term)
  (quotea :
    'a -> (FStar_Tactics_NamedView.term, Obj.t) FStar_Tactics_Effect.tac_repr)
  (vm : 'a vmap) :
  (FStar_Tactics_NamedView.term, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x p ps1 =
      let x1 =
        let x2 =
          let x3 =
            let x4 =
              let x5 =
                let x6 = quotea (FStar_Pervasives_Native.snd p) ps1 in
                (x6, FStarC_Reflection_V2_Data.Q_Explicit) in
              [x5] in
            ((FStar_Tactics_NamedView.pack
                (FStar_Tactics_NamedView.Tv_Const
                   (FStarC_Reflection_V2_Data.C_Int
                      (FStar_Pervasives_Native.fst p)))),
              FStarC_Reflection_V2_Data.Q_Explicit) :: x4 in
          (ta, FStarC_Reflection_V2_Data.Q_Implicit) :: x3 in
        ((FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "nat"]))),
          FStarC_Reflection_V2_Data.Q_Implicit) :: x2 in
      FStar_Reflection_V2_Derived.mk_app
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))) x1 in
    let x1 =
      FStar_Reflection_V2_Derived.mk_e_app
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Pervasives"; "Native"; "tuple2"])))
        [FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "nat"]));
        ta] in
    let x2 = quote_list x1 x (FStar_Pervasives_Native.fst vm) ps in
    let x3 =
      FStar_Reflection_V2_Derived.mk_e_app
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "list"])))
        [x1] in
    let x4 =
      let x5 =
        let x6 =
          let x7 =
            let x8 =
              let x9 = quotea (FStar_Pervasives_Native.snd vm) ps in
              (x9, FStarC_Reflection_V2_Data.Q_Explicit) in
            [x8] in
          (x2, FStarC_Reflection_V2_Data.Q_Explicit) :: x7 in
        (ta, FStarC_Reflection_V2_Data.Q_Implicit) :: x6 in
      (x3, FStarC_Reflection_V2_Data.Q_Implicit) :: x5 in
    FStar_Reflection_V2_Derived.mk_app
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))) x4
let interp_var (vm : 'a vmap) (i : index) : 'a=
  match FStar_List_Tot_Base.assoc i (FStar_Pervasives_Native.fst vm) with
  | FStar_Pervasives_Native.Some x -> x
  | uu___ -> FStar_Pervasives_Native.snd vm
let rec ivl_aux : 'a . 'a cr -> 'a vmap -> index -> varlist -> 'a =
  fun r vm x t ->
    let amult =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_mult r) in
    match t with
    | Nil_var -> interp_var vm x
    | Cons_var (x', t') -> amult (interp_var vm x) (ivl_aux r vm x' t')
let interp_vl (r : 'a cr) (vm : 'a vmap) (l : varlist) : 'a=
  let aone =
    FStar_Algebra_CommMonoid.__proj__CM__item__unit
      (__proj__CR__item__cm_mult r) in
  match l with | Nil_var -> aone | Cons_var (x, t) -> ivl_aux r vm x t
let interp_m (r : 'a cr) (vm : 'a vmap) (c : 'a) (l : varlist) : 'a=
  let amult =
    FStar_Algebra_CommMonoid.__proj__CM__item__mult
      (__proj__CR__item__cm_mult r) in
  match l with | Nil_var -> c | Cons_var (x, t) -> amult c (ivl_aux r vm x t)
let rec ics_aux : 'a . 'a cr -> 'a vmap -> 'a -> 'a canonical_sum -> 'a =
  fun r vm x s ->
    let aplus =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_add r) in
    match s with
    | Nil_monom -> x
    | Cons_varlist (l, t) -> aplus x (ics_aux r vm (interp_vl r vm l) t)
    | Cons_monom (c, l, t) -> aplus x (ics_aux r vm (interp_m r vm c l) t)
let interp_cs (r : 'a cr) (vm : 'a vmap) (s : 'a canonical_sum) : 'a=
  let azero =
    FStar_Algebra_CommMonoid.__proj__CM__item__unit
      (__proj__CR__item__cm_add r) in
  match s with
  | Nil_monom -> azero
  | Cons_varlist (l, t) -> ics_aux r vm (interp_vl r vm l) t
  | Cons_monom (c, l, t) -> ics_aux r vm (interp_m r vm c l) t
let rec interp_sp : 'a . 'a cr -> 'a vmap -> 'a spolynomial -> 'a =
  fun r vm p ->
    let aplus =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_add r) in
    let amult =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_mult r) in
    match p with
    | SPconst c -> c
    | SPvar i -> interp_var vm i
    | SPplus (p1, p2) -> aplus (interp_sp r vm p1) (interp_sp r vm p2)
    | SPmult (p1, p2) -> amult (interp_sp r vm p1) (interp_sp r vm p2)
type 'a polynomial =
  | Pvar of index 
  | Pconst of 'a 
  | Pplus of 'a polynomial * 'a polynomial 
  | Pmult of 'a polynomial * 'a polynomial 
  | Popp of 'a polynomial 
let uu___is_Pvar (projectee : 'a polynomial) : Prims.bool=
  match projectee with | Pvar _0 -> true | uu___ -> false
let __proj__Pvar__item___0 (projectee : 'a polynomial) : index=
  match projectee with | Pvar _0 -> _0
let uu___is_Pconst (projectee : 'a polynomial) : Prims.bool=
  match projectee with | Pconst _0 -> true | uu___ -> false
let __proj__Pconst__item___0 (projectee : 'a polynomial) : 'a=
  match projectee with | Pconst _0 -> _0
let uu___is_Pplus (projectee : 'a polynomial) : Prims.bool=
  match projectee with | Pplus (_0, _1) -> true | uu___ -> false
let __proj__Pplus__item___0 (projectee : 'a polynomial) : 'a polynomial=
  match projectee with | Pplus (_0, _1) -> _0
let __proj__Pplus__item___1 (projectee : 'a polynomial) : 'a polynomial=
  match projectee with | Pplus (_0, _1) -> _1
let uu___is_Pmult (projectee : 'a polynomial) : Prims.bool=
  match projectee with | Pmult (_0, _1) -> true | uu___ -> false
let __proj__Pmult__item___0 (projectee : 'a polynomial) : 'a polynomial=
  match projectee with | Pmult (_0, _1) -> _0
let __proj__Pmult__item___1 (projectee : 'a polynomial) : 'a polynomial=
  match projectee with | Pmult (_0, _1) -> _1
let uu___is_Popp (projectee : 'a polynomial) : Prims.bool=
  match projectee with | Popp _0 -> true | uu___ -> false
let __proj__Popp__item___0 (projectee : 'a polynomial) : 'a polynomial=
  match projectee with | Popp _0 -> _0
let rec polynomial_normalize :
  'a . 'a cr -> 'a polynomial -> 'a canonical_sum =
  fun r p ->
    match p with
    | Pvar i -> Cons_varlist ((Cons_var (i, Nil_var)), Nil_monom)
    | Pconst c -> Cons_monom (c, Nil_var, Nil_monom)
    | Pplus (l, q) ->
        canonical_sum_merge r (polynomial_normalize r l)
          (polynomial_normalize r q)
    | Pmult (l, q) ->
        canonical_sum_prod r (polynomial_normalize r l)
          (polynomial_normalize r q)
    | Popp p1 ->
        canonical_sum_scalar3 r
          (__proj__CR__item__opp r
             (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                (__proj__CR__item__cm_mult r))) Nil_var
          (polynomial_normalize r p1)
let polynomial_simplify (r : 'a cr) (p : 'a polynomial) : 'a canonical_sum=
  canonical_sum_simplify r (polynomial_normalize r p)
let rec spolynomial_of : 'a . 'a cr -> 'a polynomial -> 'a spolynomial =
  fun r p ->
    match p with
    | Pvar i -> SPvar i
    | Pconst c -> SPconst c
    | Pplus (l, q) -> SPplus ((spolynomial_of r l), (spolynomial_of r q))
    | Pmult (l, q) -> SPmult ((spolynomial_of r l), (spolynomial_of r q))
    | Popp p1 ->
        SPmult
          ((SPconst
              (__proj__CR__item__opp r
                 (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                    (__proj__CR__item__cm_mult r)))), (spolynomial_of r p1))
let rec interp_p : 'a . 'a cr -> 'a vmap -> 'a polynomial -> 'a =
  fun r vm p ->
    let aplus =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_add r) in
    let amult =
      FStar_Algebra_CommMonoid.__proj__CM__item__mult
        (__proj__CR__item__cm_mult r) in
    match p with
    | Pconst c -> c
    | Pvar i -> interp_var vm i
    | Pplus (p1, p2) -> aplus (interp_p r vm p1) (interp_p r vm p2)
    | Pmult (p1, p2) -> amult (interp_p r vm p1) (interp_p r vm p2)
    | Popp p1 -> __proj__CR__item__opp r (interp_p r vm p1)
let ddump (m : Prims.string) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.debugging () ps in
    if x then FStarC_Tactics_V2_Builtins.dump m ps else ()
let rec find_aux (n : Prims.nat) (x : FStar_Tactics_NamedView.term)
  (xs : FStar_Tactics_NamedView.term Prims.list) :
  (Prims.nat FStar_Pervasives_Native.option, Obj.t)
    FStar_Tactics_Effect.tac_repr=
  match xs with
  | [] -> (fun uu___ -> FStar_Pervasives_Native.None)
  | x'::xs' ->
      if term_eq x x'
      then
        FStar_Tactics_Effect.lift_div_tac ()
          (fun uu___ -> FStar_Pervasives_Native.Some n)
      else find_aux (n + Prims.int_one) x xs'
let find :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      (Prims.nat FStar_Pervasives_Native.option, Obj.t)
        FStar_Tactics_Effect.tac_repr=
  find_aux Prims.int_zero
let make_fvar (t : FStar_Tactics_NamedView.term)
  (unquotea :
    FStar_Tactics_NamedView.term -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr)
  (ts : FStar_Tactics_NamedView.term Prims.list) (vm : 'a vmap) :
  (('a polynomial * FStar_Tactics_NamedView.term Prims.list * 'a vmap),
    Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = find t ts ps in
    match x with
    | FStar_Pervasives_Native.Some v -> ((Pvar v), ts, vm)
    | FStar_Pervasives_Native.None ->
        let x1 = FStar_List_Tot_Base.length ts in
        let x2 = unquotea t ps in
        ((Pvar x1), (FStar_List_Tot_Base.op_At ts [t]), (update x1 x2 vm))
let rec reification_aux :
  'a .
    (FStar_Tactics_NamedView.term ->
       ('a, Obj.t) FStar_Tactics_Effect.tac_repr)
      ->
      FStar_Tactics_NamedView.term Prims.list ->
        'a vmap ->
          FStar_Tactics_NamedView.term ->
            FStar_Tactics_NamedView.term ->
              FStar_Tactics_NamedView.term ->
                FStar_Tactics_NamedView.term ->
                  FStar_Tactics_NamedView.term ->
                    (('a polynomial * FStar_Tactics_NamedView.term Prims.list
                       * 'a vmap),
                      Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun unquotea ts vm add opp mone mult t ps ->
    let x = FStar_Reflection_V2_Derived_Lemmas.collect_app_ref t in
    match x with
    | (hd, tl) ->
        let x1 =
          let x2 = FStar_Tactics_NamedView.inspect hd ps in
          (x2, (FStar_List_Tot_Base.list_unref () tl)) in
        (match x1 with
         | (FStar_Tactics_NamedView.Tv_FVar fv,
            (t1, uu___)::(t2, uu___1)::[]) ->
             let x2 op ps1 =
               let x3 =
                 reification_aux unquotea ts vm add opp mone mult t1 ps1 in
               match x3 with
               | (e1, ts1, vm1) ->
                   let x4 =
                     reification_aux unquotea ts1 vm1 add opp mone mult t2
                       ps1 in
                   (match x4 with | (e2, ts2, vm2) -> ((op e1 e2), ts2, vm2)) in
             if
               term_eq
                 (FStar_Tactics_NamedView.pack
                    (FStar_Tactics_NamedView.Tv_FVar fv)) add
             then x2 (fun uu___2 uu___3 -> Pplus (uu___2, uu___3)) ps
             else
               if
                 term_eq
                   (FStar_Tactics_NamedView.pack
                      (FStar_Tactics_NamedView.Tv_FVar fv)) mult
               then x2 (fun uu___2 uu___3 -> Pmult (uu___2, uu___3)) ps
               else make_fvar t unquotea ts vm ps
         | (FStar_Tactics_NamedView.Tv_FVar fv, (t1, uu___)::[]) ->
             let x2 op ps1 =
               let x3 =
                 reification_aux unquotea ts vm add opp mone mult t1 ps1 in
               match x3 with | (e, ts1, vm1) -> ((op e), ts1, vm1) in
             if
               term_eq
                 (FStar_Tactics_NamedView.pack
                    (FStar_Tactics_NamedView.Tv_FVar fv)) opp
             then x2 (fun uu___1 -> Popp uu___1) ps
             else make_fvar t unquotea ts vm ps
         | (FStar_Tactics_NamedView.Tv_Const uu___, []) ->
             let x2 = let x3 = unquotea t ps in Pconst x3 in (x2, ts, vm)
         | (uu___, uu___1) -> make_fvar t unquotea ts vm ps)
let steps : FStarC_NormSteps.norm_step Prims.list=
  [FStarC_NormSteps.primops;
  FStarC_NormSteps.iota;
  FStarC_NormSteps.zeta;
  FStarC_NormSteps.delta_attr ["FStar.Tactics.CanonCommSemiring.canon_attr"];
  FStarC_NormSteps.delta_only
    ["Prims.op_Star";
    "FStar.Algebra.CommMonoid.int_plus_cm";
    "FStar.Algebra.CommMonoid.int_multiply_cm";
    "FStar.Algebra.CommMonoid.__proj__CM__item__mult";
    "FStar.Algebra.CommMonoid.__proj__CM__item__unit";
    "FStar.Tactics.CanonCommSemiring.__proj__CR__item__cm_add";
    "FStar.Tactics.CanonCommSemiring.__proj__CR__item__opp";
    "FStar.Tactics.CanonCommSemiring.__proj__CR__item__cm_mult";
    "FStar.List.Tot.Base.assoc";
    "FStar.Pervasives.Native.fst";
    "FStar.Pervasives.Native.snd";
    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
    "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
    "FStar.List.Tot.Base.op_At";
    "FStar.List.Tot.Base.append"]]
let canon_norm (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V2_Builtins.norm steps
let reification
  (unquotea :
    FStar_Tactics_NamedView.term -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr)
  (quotea :
    'a -> (FStar_Tactics_NamedView.term, Obj.t) FStar_Tactics_Effect.tac_repr)
  (tadd : FStar_Tactics_NamedView.term) (topp : FStar_Tactics_NamedView.term)
  (tmone : FStar_Tactics_NamedView.term)
  (tmult : FStar_Tactics_NamedView.term) (munit : 'a)
  (ts : FStar_Tactics_NamedView.term Prims.list) :
  (('a polynomial Prims.list * 'a vmap), Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = tadd in
    let x1 = topp in
    let x2 = tmone in
    let x3 = tmult in
    let x4 =
      FStar_Tactics_Util.map (FStar_Tactics_V2_Derived.norm_term steps) ts ps in
    let x5 =
      FStar_Tactics_Util.fold_left
        (fun uu___ t ->
           match uu___ with
           | (es, vs, vm) ->
               FStar_Tactics_Effect.tac_bind () ()
                 (reification_aux unquotea vs vm x x1 x2 x3 t)
                 (fun uu___1 uu___2 ->
                    match uu___1 with
                    | (e, vs1, vm1) -> ((e :: es), vs1, vm1)))
        ([], [], ([], munit)) x4 ps in
    match x5 with | (es, uu___, vm) -> ((FStar_List_Tot_Base.rev es), vm)
let rec quote_polynomial :
  'a .
    FStar_Tactics_NamedView.term ->
      ('a ->
         (FStar_Tactics_NamedView.term, Obj.t) FStar_Tactics_Effect.tac_repr)
        ->
        'a polynomial ->
          (FStar_Tactics_NamedView.term, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun ta quotea e ->
    match e with
    | Pconst c ->
        FStar_Tactics_Effect.tac_bind () ()
          (FStar_Tactics_Effect.tac_bind () ()
             (FStar_Tactics_Effect.tac_bind () ()
                (FStar_Tactics_Effect.tac_bind () () (quotea c)
                   (fun uu___ uu___1 ->
                      (uu___, FStarC_Reflection_V2_Data.Q_Explicit)))
                (fun uu___ uu___1 -> [uu___]))
             (fun uu___ uu___1 -> (ta, FStarC_Reflection_V2_Data.Q_Implicit)
                :: uu___))
          (fun uu___ uu___1 ->
             FStar_Reflection_V2_Derived.mk_app
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Tactics"; "CanonCommSemiring"; "Pconst"])))
               uu___)
    | Pvar x ->
        FStar_Tactics_Effect.lift_div_tac ()
          (fun uu___ ->
             FStar_Reflection_V2_Derived.mk_e_app
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Tactics"; "CanonCommSemiring"; "Pvar"])))
               [FStar_Tactics_NamedView.pack
                  (FStar_Tactics_NamedView.Tv_Const
                     (FStarC_Reflection_V2_Data.C_Int x))])
    | Pplus (e1, e2) ->
        FStar_Tactics_Effect.tac_bind () ()
          (FStar_Tactics_Effect.tac_bind () ()
             (quote_polynomial ta quotea e1)
             (fun uu___ ps ->
                let x = let x1 = quote_polynomial ta quotea e2 ps in [x1] in
                uu___ :: x))
          (fun uu___ uu___1 ->
             FStar_Reflection_V2_Derived.mk_e_app
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Tactics"; "CanonCommSemiring"; "Pplus"])))
               uu___)
    | Pmult (e1, e2) ->
        FStar_Tactics_Effect.tac_bind () ()
          (FStar_Tactics_Effect.tac_bind () ()
             (quote_polynomial ta quotea e1)
             (fun uu___ ps ->
                let x = let x1 = quote_polynomial ta quotea e2 ps in [x1] in
                uu___ :: x))
          (fun uu___ uu___1 ->
             FStar_Reflection_V2_Derived.mk_e_app
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Tactics"; "CanonCommSemiring"; "Pmult"])))
               uu___)
    | Popp e1 ->
        FStar_Tactics_Effect.tac_bind () ()
          (FStar_Tactics_Effect.tac_bind () ()
             (quote_polynomial ta quotea e1) (fun uu___ uu___1 -> [uu___]))
          (fun uu___ uu___1 ->
             FStar_Reflection_V2_Derived.mk_e_app
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Tactics"; "CanonCommSemiring"; "Popp"])))
               uu___)
let canon_semiring_aux (ta : FStar_Tactics_NamedView.term)
  (unquotea :
    FStar_Tactics_NamedView.term -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr)
  (quotea :
    'a -> (FStar_Tactics_NamedView.term, Obj.t) FStar_Tactics_Effect.tac_repr)
  (tr : FStar_Tactics_NamedView.term) (tadd : FStar_Tactics_NamedView.term)
  (topp : FStar_Tactics_NamedView.term)
  (tmone : FStar_Tactics_NamedView.term)
  (tmult : FStar_Tactics_NamedView.term) (munit : 'a) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.focus
    (fun uu___ ps ->
       FStarC_Tactics_V2_Builtins.norm [] ps;
       (let x1 = FStar_Tactics_V2_Derived.cur_goal () ps in
        let x2 = FStar_Reflection_V2_Formula.term_as_formula x1 ps in
        match x2 with
        | FStar_Reflection_V2_Formula.Comp
            (FStar_Reflection_V2_Formula.Eq (FStar_Pervasives_Native.Some t),
             t1, t2)
            ->
            let x3 =
              FStar_Tactics_V2_Derived.tcut
                (FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_App
                      ((FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_FVar
                             (FStarC_Reflection_V2_Builtins.pack_fv
                                ["Prims"; "squash"]))),
                        ((FStarC_Reflection_V2_Builtins.pack_ln
                            (FStarC_Reflection_V2_Data.Tv_App
                               ((FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_App
                                      ((FStarC_Reflection_V2_Builtins.pack_ln
                                          (FStarC_Reflection_V2_Data.Tv_App
                                             ((FStarC_Reflection_V2_Builtins.pack_ln
                                                 (FStarC_Reflection_V2_Data.Tv_FVar
                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                       ["Prims"; "eq2"]))),
                                               (ta,
                                                 FStarC_Reflection_V2_Data.Q_Implicit)))),
                                        (t1,
                                          FStarC_Reflection_V2_Data.Q_Explicit)))),
                                 (t2, FStarC_Reflection_V2_Data.Q_Explicit)))),
                          FStarC_Reflection_V2_Data.Q_Explicit)))) ps in
            (FStar_Tactics_V2_Derived.try_with
               (fun uu___1 ->
                  match () with
                  | () ->
                      FStar_Tactics_V2_Derived.exact
                        (FStar_Tactics_V2_SyntaxCoercions.binding_to_term x3))
               (fun uu___1 -> FStar_Tactics_V2_Derived.smt ()) ps;
             (let x5 =
                reification unquotea quotea tadd topp tmone tmult munit
                  [t1; t2] ps in
              match x5 with
              | (e1::e2::[], vm) ->
                  let x6 = quote_vm ta quotea vm ps in
                  let x7 = quote_polynomial ta quotea e1 ps in
                  let x8 = quote_polynomial ta quotea e2 ps in
                  (FStar_Tactics_MApply.mapply
                     FStar_Tactics_MApply.termable_term
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_App
                           ((FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_App
                                  ((FStarC_Reflection_V2_Builtins.pack_ln
                                      (FStarC_Reflection_V2_Data.Tv_App
                                         ((FStarC_Reflection_V2_Builtins.pack_ln
                                             (FStarC_Reflection_V2_Data.Tv_App
                                                ((FStarC_Reflection_V2_Builtins.pack_ln
                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                       ((FStarC_Reflection_V2_Builtins.pack_ln
                                                           (FStarC_Reflection_V2_Data.Tv_App
                                                              ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                  (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommSemiring";
                                                                    "semiring_reflect"]))),
                                                                    (ta,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit)))),
                                                                (tr,
                                                                  FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                         (x6,
                                                           FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                  (x7,
                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                           (x8,
                                             FStarC_Reflection_V2_Data.Q_Explicit)))),
                                    (t1,
                                      FStarC_Reflection_V2_Data.Q_Explicit)))),
                             (t2, FStarC_Reflection_V2_Data.Q_Explicit)))) ps;
                   canon_norm () ps;
                   FStar_Tactics_V2_Derived.later () ps;
                   canon_norm () ps;
                   FStar_Tactics_V2_Derived.trefl () ps;
                   canon_norm () ps;
                   FStar_Tactics_V2_Derived.trefl () ps)
              | uu___1 -> FStar_Tactics_V2_Derived.fail "Unexpected" ps))
        | uu___1 ->
            let x3 =
              let x4 = FStarC_Tactics_V2_Builtins.term_to_string x1 ps in
              Prims.strcat "Goal should be an equality: " x4 in
            FStar_Tactics_V2_Derived.fail x3 ps))
let canon_semiring (r : 'a cr) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
    let x1 = Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
    let x2 =
      let x3 =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      FStar_Tactics_V2_Derived.norm_term steps x3 ps in
    let x3 =
      let x4 =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      FStar_Tactics_V2_Derived.norm_term steps x4 ps in
    let x4 =
      let x5 =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      FStar_Tactics_V2_Derived.norm_term steps x5 ps in
    let x5 =
      let x6 =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      FStar_Tactics_V2_Derived.norm_term steps x6 ps in
    canon_semiring_aux x FStarC_Tactics_V2_Builtins.unquote
      (fun x6 uu___ ->
         Obj.magic (failwith "Cannot evaluate open quotation at runtime")) x1
      x2 x3 x4 x5
      (FStar_Algebra_CommMonoid.__proj__CM__item__unit
         (__proj__CR__item__cm_add r)) ps
let int_cr : Prims.int cr=
  CR
    (FStar_Algebra_CommMonoid.int_plus_cm,
      FStar_Algebra_CommMonoid.int_multiply_cm, (~-), (), (), ())
let int_semiring (uu___ : unit) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr= canon_semiring int_cr
