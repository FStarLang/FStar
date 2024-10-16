open Prims
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
type ('a, 'cmuadd, 'cmumult) distribute_left_lemma = unit
type ('a, 'cmuadd, 'cmumult) distribute_right_lemma = unit
type ('a, 'cmuadd, 'cmumult) mult_zero_l_lemma = unit
type ('a, 'cmuadd, 'opp) add_opp_r_lemma = unit
type 'a cr =
  | CR of 'a FStar_Algebra_CommMonoid.cm * 'a FStar_Algebra_CommMonoid.cm *
  ('a -> 'a) * unit * unit * unit 
let uu___is_CR : 'a . 'a cr -> Prims.bool = fun projectee -> true
let __proj__CR__item__cm_add : 'a . 'a cr -> 'a FStar_Algebra_CommMonoid.cm =
  fun projectee ->
    match projectee with
    | CR (cm_add, cm_mult, opp, add_opp, distribute, mult_zero_l) -> cm_add
let __proj__CR__item__cm_mult : 'a . 'a cr -> 'a FStar_Algebra_CommMonoid.cm
  =
  fun projectee ->
    match projectee with
    | CR (cm_add, cm_mult, opp, add_opp, distribute, mult_zero_l) -> cm_mult
let __proj__CR__item__opp : 'a . 'a cr -> 'a -> 'a =
  fun projectee ->
    match projectee with
    | CR (cm_add, cm_mult, opp, add_opp, distribute, mult_zero_l) -> opp




let norm_fully : 'a . 'a -> 'a = fun x -> x
type index = Prims.nat
type varlist =
  | Nil_var 
  | Cons_var of index * varlist 
let (uu___is_Nil_var : varlist -> Prims.bool) =
  fun projectee -> match projectee with | Nil_var -> true | uu___ -> false
let (uu___is_Cons_var : varlist -> Prims.bool) =
  fun projectee ->
    match projectee with | Cons_var (_0, _1) -> true | uu___ -> false
let (__proj__Cons_var__item___0 : varlist -> index) =
  fun projectee -> match projectee with | Cons_var (_0, _1) -> _0
let (__proj__Cons_var__item___1 : varlist -> varlist) =
  fun projectee -> match projectee with | Cons_var (_0, _1) -> _1
type 'a canonical_sum =
  | Nil_monom 
  | Cons_monom of 'a * varlist * 'a canonical_sum 
  | Cons_varlist of varlist * 'a canonical_sum 
let uu___is_Nil_monom : 'a . 'a canonical_sum -> Prims.bool =
  fun projectee -> match projectee with | Nil_monom -> true | uu___ -> false
let uu___is_Cons_monom : 'a . 'a canonical_sum -> Prims.bool =
  fun projectee ->
    match projectee with | Cons_monom (_0, _1, _2) -> true | uu___ -> false
let __proj__Cons_monom__item___0 : 'a . 'a canonical_sum -> 'a =
  fun projectee -> match projectee with | Cons_monom (_0, _1, _2) -> _0
let __proj__Cons_monom__item___1 : 'a . 'a canonical_sum -> varlist =
  fun projectee -> match projectee with | Cons_monom (_0, _1, _2) -> _1
let __proj__Cons_monom__item___2 : 'a . 'a canonical_sum -> 'a canonical_sum
  = fun projectee -> match projectee with | Cons_monom (_0, _1, _2) -> _2
let uu___is_Cons_varlist : 'a . 'a canonical_sum -> Prims.bool =
  fun projectee ->
    match projectee with | Cons_varlist (_0, _1) -> true | uu___ -> false
let __proj__Cons_varlist__item___0 : 'a . 'a canonical_sum -> varlist =
  fun projectee -> match projectee with | Cons_varlist (_0, _1) -> _0
let __proj__Cons_varlist__item___1 :
  'a . 'a canonical_sum -> 'a canonical_sum =
  fun projectee -> match projectee with | Cons_varlist (_0, _1) -> _1
let rec (varlist_lt : varlist -> varlist -> Prims.bool) =
  fun x ->
    fun y ->
      match (x, y) with
      | (Nil_var, Cons_var (uu___, uu___1)) -> true
      | (Cons_var (i, xs), Cons_var (j, ys)) ->
          if i < j then true else (i = j) && (varlist_lt xs ys)
      | (uu___, uu___1) -> false
let rec (varlist_merge : varlist -> varlist -> varlist) =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | (uu___, Nil_var) -> l1
      | (Nil_var, uu___) -> l2
      | (Cons_var (v1, t1), Cons_var (v2, t2)) -> vm_aux v1 t1 l2
and (vm_aux : index -> varlist -> varlist -> varlist) =
  fun v1 ->
    fun t1 ->
      fun l2 ->
        match l2 with
        | Cons_var (v2, t2) ->
            if v1 < v2
            then Cons_var (v1, (varlist_merge t1 l2))
            else Cons_var (v2, (vm_aux v1 t1 t2))
        | uu___ -> Cons_var (v1, t1)
let rec canonical_sum_merge :
  'a . 'a cr -> 'a canonical_sum -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun s1 ->
      fun s2 ->
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
  fun r ->
    fun c1 ->
      fun l1 ->
        fun t1 ->
          fun s2 ->
            let aplus =
              FStar_Algebra_CommMonoid.__proj__CM__item__mult
                (__proj__CR__item__cm_add r) in
            let aone =
              FStar_Algebra_CommMonoid.__proj__CM__item__unit
                (__proj__CR__item__cm_mult r) in
            match s2 with
            | Cons_monom (c2, l2, t2) ->
                if l1 = l2
                then
                  Cons_monom
                    ((aplus c1 c2), l1, (canonical_sum_merge r t1 t2))
                else
                  if varlist_lt l1 l2
                  then Cons_monom (c1, l1, (canonical_sum_merge r t1 s2))
                  else Cons_monom (c2, l2, (csm_aux r c1 l1 t1 t2))
            | Cons_varlist (l2, t2) ->
                if l1 = l2
                then
                  Cons_monom
                    ((aplus c1 aone), l1, (canonical_sum_merge r t1 t2))
                else
                  if varlist_lt l1 l2
                  then Cons_monom (c1, l1, (canonical_sum_merge r t1 s2))
                  else Cons_varlist (l2, (csm_aux r c1 l1 t1 t2))
            | Nil_monom -> Cons_monom (c1, l1, t1)
let rec monom_insert :
  'a . 'a cr -> 'a -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun c1 ->
      fun l1 ->
        fun s2 ->
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
let varlist_insert :
  'a . 'a cr -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun l1 ->
      fun s2 ->
        let aone =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_mult r) in
        monom_insert r aone l1 s2
let rec canonical_sum_scalar :
  'a . 'a cr -> 'a -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun c0 ->
      fun s ->
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
  fun r ->
    fun l0 ->
      fun s ->
        match s with
        | Cons_monom (c, l, t) ->
            monom_insert r c (varlist_merge l0 l)
              (canonical_sum_scalar2 r l0 t)
        | Cons_varlist (l, t) ->
            varlist_insert r (varlist_merge l0 l)
              (canonical_sum_scalar2 r l0 t)
        | Nil_monom -> Nil_monom
let rec canonical_sum_scalar3 :
  'a . 'a cr -> 'a -> varlist -> 'a canonical_sum -> 'a canonical_sum =
  fun r ->
    fun c0 ->
      fun l0 ->
        fun s ->
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
  fun r ->
    fun s1 ->
      fun s2 ->
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
let uu___is_SPvar : 'a . 'a spolynomial -> Prims.bool =
  fun projectee -> match projectee with | SPvar _0 -> true | uu___ -> false
let __proj__SPvar__item___0 : 'a . 'a spolynomial -> index =
  fun projectee -> match projectee with | SPvar _0 -> _0
let uu___is_SPconst : 'a . 'a spolynomial -> Prims.bool =
  fun projectee -> match projectee with | SPconst _0 -> true | uu___ -> false
let __proj__SPconst__item___0 : 'a . 'a spolynomial -> 'a =
  fun projectee -> match projectee with | SPconst _0 -> _0
let uu___is_SPplus : 'a . 'a spolynomial -> Prims.bool =
  fun projectee ->
    match projectee with | SPplus (_0, _1) -> true | uu___ -> false
let __proj__SPplus__item___0 : 'a . 'a spolynomial -> 'a spolynomial =
  fun projectee -> match projectee with | SPplus (_0, _1) -> _0
let __proj__SPplus__item___1 : 'a . 'a spolynomial -> 'a spolynomial =
  fun projectee -> match projectee with | SPplus (_0, _1) -> _1
let uu___is_SPmult : 'a . 'a spolynomial -> Prims.bool =
  fun projectee ->
    match projectee with | SPmult (_0, _1) -> true | uu___ -> false
let __proj__SPmult__item___0 : 'a . 'a spolynomial -> 'a spolynomial =
  fun projectee -> match projectee with | SPmult (_0, _1) -> _0
let __proj__SPmult__item___1 : 'a . 'a spolynomial -> 'a spolynomial =
  fun projectee -> match projectee with | SPmult (_0, _1) -> _1
let rec spolynomial_normalize :
  'a . 'a cr -> 'a spolynomial -> 'a canonical_sum =
  fun r ->
    fun p ->
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
  fun r ->
    fun s ->
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
let spolynomial_simplify : 'a . 'a cr -> 'a spolynomial -> 'a canonical_sum =
  fun r -> fun p -> canonical_sum_simplify r (spolynomial_normalize r p)
type var = Prims.nat
type 'a vmap = ((var * 'a) Prims.list * 'a)
let update : 'a . var -> 'a -> 'a vmap -> 'a vmap =
  fun x ->
    fun xa ->
      fun vm ->
        let uu___ = vm in match uu___ with | (l, y) -> (((x, xa) :: l), y)
let rec quote_list :
  'a .
    FStar_Tactics_NamedView.term ->
      ('a ->
         (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
        ->
        'a Prims.list ->
          (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun ta ->
           fun quotea ->
             fun xs ->
               match xs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Reflection_V2_Derived.mk_app
                                (FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_FVar
                                      (FStarC_Reflection_V2_Builtins.pack_fv
                                         ["Prims"; "Nil"])))
                                [(ta, FStarC_Reflection_V2_Data.Q_Implicit)])))
               | x::xs' ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = quotea x in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommSemiring.fst"
                                          (Prims.of_int (397))
                                          (Prims.of_int (30))
                                          (Prims.of_int (397))
                                          (Prims.of_int (38)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommSemiring.fst"
                                          (Prims.of_int (397))
                                          (Prims.of_int (29))
                                          (Prims.of_int (397))
                                          (Prims.of_int (51)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 ->
                                         (uu___4,
                                           FStarC_Reflection_V2_Data.Q_Explicit))) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (397))
                                        (Prims.of_int (29))
                                        (Prims.of_int (397))
                                        (Prims.of_int (51)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (396))
                                        (Prims.of_int (29))
                                        (Prims.of_int (398))
                                        (Prims.of_int (68)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun uu___3 ->
                                     let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           quote_list ta quotea xs' in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (398))
                                                    (Prims.of_int (30))
                                                    (Prims.of_int (398))
                                                    (Prims.of_int (54)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (398))
                                                    (Prims.of_int (29))
                                                    (Prims.of_int (398))
                                                    (Prims.of_int (67)))))
                                           (Obj.magic uu___6)
                                           (fun uu___7 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___8 ->
                                                   (uu___7,
                                                     FStarC_Reflection_V2_Data.Q_Explicit))) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                  (Prims.of_int (398))
                                                  (Prims.of_int (29))
                                                  (Prims.of_int (398))
                                                  (Prims.of_int (67)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                  (Prims.of_int (396))
                                                  (Prims.of_int (29))
                                                  (Prims.of_int (398))
                                                  (Prims.of_int (68)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___7 -> [uu___6])) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommSemiring.fst"
                                                   (Prims.of_int (396))
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (398))
                                                   (Prims.of_int (68)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommSemiring.fst"
                                                   (Prims.of_int (396))
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (398))
                                                   (Prims.of_int (68)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___6 -> uu___3 ::
                                                  uu___5)))) uu___3) in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (396))
                                      (Prims.of_int (29))
                                      (Prims.of_int (398))
                                      (Prims.of_int (68)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (396))
                                      (Prims.of_int (29))
                                      (Prims.of_int (398))
                                      (Prims.of_int (68)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     (ta,
                                       FStarC_Reflection_V2_Data.Q_Implicit)
                                     :: uu___2)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (396)) (Prims.of_int (29))
                                    (Prims.of_int (398)) (Prims.of_int (68)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (396)) (Prims.of_int (14))
                                    (Prims.of_int (398)) (Prims.of_int (68)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Reflection_V2_Derived.mk_app
                                     (FStarC_Reflection_V2_Builtins.pack_ln
                                        (FStarC_Reflection_V2_Data.Tv_FVar
                                           (FStarC_Reflection_V2_Builtins.pack_fv
                                              ["Prims"; "Cons"]))) uu___1)))))
          uu___2 uu___1 uu___
let quote_vm :
  'a .
    FStar_Tactics_NamedView.term ->
      ('a ->
         (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
        ->
        'a vmap ->
          (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr
  =
  fun ta ->
    fun quotea ->
      fun vm ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  fun p ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                quotea (FStar_Pervasives_Native.snd p) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommSemiring.fst"
                                         (Prims.of_int (405))
                                         (Prims.of_int (7))
                                         (Prims.of_int (405))
                                         (Prims.of_int (21)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommSemiring.fst"
                                         (Prims.of_int (405))
                                         (Prims.of_int (6))
                                         (Prims.of_int (405))
                                         (Prims.of_int (34)))))
                                (Obj.magic uu___7)
                                (fun uu___8 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___9 ->
                                        (uu___8,
                                          FStarC_Reflection_V2_Data.Q_Explicit))) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommSemiring.fst"
                                       (Prims.of_int (405))
                                       (Prims.of_int (6))
                                       (Prims.of_int (405))
                                       (Prims.of_int (34)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommSemiring.fst"
                                       (Prims.of_int (403))
                                       (Prims.of_int (23))
                                       (Prims.of_int (405))
                                       (Prims.of_int (35)))))
                              (Obj.magic uu___6)
                              (fun uu___7 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___8 -> [uu___7])) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (403)) (Prims.of_int (23))
                                     (Prims.of_int (405)) (Prims.of_int (35)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (403)) (Prims.of_int (23))
                                     (Prims.of_int (405)) (Prims.of_int (35)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___7 ->
                                    ((FStar_Tactics_NamedView.pack
                                        (FStar_Tactics_NamedView.Tv_Const
                                           (FStarC_Reflection_V2_Data.C_Int
                                              (FStar_Pervasives_Native.fst p)))),
                                      FStarC_Reflection_V2_Data.Q_Explicit)
                                    :: uu___6)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CanonCommSemiring.fst"
                                   (Prims.of_int (403)) (Prims.of_int (23))
                                   (Prims.of_int (405)) (Prims.of_int (35)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CanonCommSemiring.fst"
                                   (Prims.of_int (403)) (Prims.of_int (23))
                                   (Prims.of_int (405)) (Prims.of_int (35)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 ->
                                  (ta, FStarC_Reflection_V2_Data.Q_Implicit)
                                  :: uu___5)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommSemiring.fst"
                                 (Prims.of_int (403)) (Prims.of_int (23))
                                 (Prims.of_int (405)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommSemiring.fst"
                                 (Prims.of_int (403)) (Prims.of_int (23))
                                 (Prims.of_int (405)) (Prims.of_int (35)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___5 ->
                                ((FStarC_Reflection_V2_Builtins.pack_ln
                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                       (FStarC_Reflection_V2_Builtins.pack_fv
                                          ["Prims"; "nat"]))),
                                  FStarC_Reflection_V2_Data.Q_Implicit)
                                :: uu___4)) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonCommSemiring.fst"
                               (Prims.of_int (403)) (Prims.of_int (23))
                               (Prims.of_int (405)) (Prims.of_int (35)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonCommSemiring.fst"
                               (Prims.of_int (403)) (Prims.of_int (4))
                               (Prims.of_int (405)) (Prims.of_int (35)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___4 ->
                              FStar_Reflection_V2_Derived.mk_app
                                (FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_FVar
                                      (FStarC_Reflection_V2_Builtins.pack_fv
                                         ["FStar";
                                         "Pervasives";
                                         "Native";
                                         "Mktuple2"]))) uu___3)))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CanonCommSemiring.fst"
                   (Prims.of_int (403)) (Prims.of_int (4))
                   (Prims.of_int (405)) (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CanonCommSemiring.fst"
                   (Prims.of_int (405)) (Prims.of_int (38))
                   (Prims.of_int (410)) (Prims.of_int (73)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun quote_map_entry ->
                let uu___1 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          FStar_Reflection_V2_Derived.mk_e_app
                            (FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_FVar
                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                     ["FStar";
                                     "Pervasives";
                                     "Native";
                                     "tuple2"])))
                            [FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_FVar
                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                     ["Prims"; "nat"]));
                            ta])) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommSemiring.fst"
                              (Prims.of_int (406)) (Prims.of_int (16))
                              (Prims.of_int (406)) (Prims.of_int (47)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommSemiring.fst"
                              (Prims.of_int (406)) (Prims.of_int (50))
                              (Prims.of_int (410)) (Prims.of_int (73)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun tyentry ->
                           let uu___2 =
                             quote_list tyentry quote_map_entry
                               (FStar_Pervasives_Native.fst vm) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommSemiring.fst"
                                         (Prims.of_int (407))
                                         (Prims.of_int (14))
                                         (Prims.of_int (407))
                                         (Prims.of_int (57)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommSemiring.fst"
                                         (Prims.of_int (407))
                                         (Prims.of_int (60))
                                         (Prims.of_int (410))
                                         (Prims.of_int (73)))))
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   (fun tlist ->
                                      let uu___3 =
                                        Obj.magic
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___4 ->
                                                FStar_Reflection_V2_Derived.mk_e_app
                                                  (FStarC_Reflection_V2_Builtins.pack_ln
                                                     (FStarC_Reflection_V2_Data.Tv_FVar
                                                        (FStarC_Reflection_V2_Builtins.pack_fv
                                                           ["Prims"; "list"])))
                                                  [tyentry])) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (408))
                                                    (Prims.of_int (15))
                                                    (Prims.of_int (408))
                                                    (Prims.of_int (41)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                    (Prims.of_int (409))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (410))
                                                    (Prims.of_int (73)))))
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              (fun tylist ->
                                                 let uu___4 =
                                                   let uu___5 =
                                                     let uu___6 =
                                                       let uu___7 =
                                                         let uu___8 =
                                                           let uu___9 =
                                                             quotea
                                                               (FStar_Pervasives_Native.snd
                                                                  vm) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (59)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (72)))))
                                                             (Obj.magic
                                                                uu___9)
                                                             (fun uu___10 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___11
                                                                    ->
                                                                    (uu___10,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (72)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (73)))))
                                                           (Obj.magic uu___8)
                                                           (fun uu___9 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___10
                                                                   ->
                                                                   [uu___9])) in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                                  (Prims.of_int (409))
                                                                  (Prims.of_int (21))
                                                                  (Prims.of_int (410))
                                                                  (Prims.of_int (73)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                                  (Prims.of_int (409))
                                                                  (Prims.of_int (21))
                                                                  (Prims.of_int (410))
                                                                  (Prims.of_int (73)))))
                                                         (Obj.magic uu___7)
                                                         (fun uu___8 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___9 ->
                                                                 (tlist,
                                                                   FStarC_Reflection_V2_Data.Q_Explicit)
                                                                 :: uu___8)) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                                (Prims.of_int (409))
                                                                (Prims.of_int (21))
                                                                (Prims.of_int (410))
                                                                (Prims.of_int (73)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                                (Prims.of_int (409))
                                                                (Prims.of_int (21))
                                                                (Prims.of_int (410))
                                                                (Prims.of_int (73)))))
                                                       (Obj.magic uu___6)
                                                       (fun uu___7 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___8 ->
                                                               (ta,
                                                                 FStarC_Reflection_V2_Data.Q_Implicit)
                                                               :: uu___7)) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (409))
                                                              (Prims.of_int (21))
                                                              (Prims.of_int (410))
                                                              (Prims.of_int (73)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (409))
                                                              (Prims.of_int (21))
                                                              (Prims.of_int (410))
                                                              (Prims.of_int (73)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___7 ->
                                                             (tylist,
                                                               FStarC_Reflection_V2_Data.Q_Implicit)
                                                             :: uu___6)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.CanonCommSemiring.fst"
                                                               (Prims.of_int (409))
                                                               (Prims.of_int (21))
                                                               (Prims.of_int (410))
                                                               (Prims.of_int (73)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.CanonCommSemiring.fst"
                                                               (Prims.of_int (409))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (410))
                                                               (Prims.of_int (73)))))
                                                      (Obj.magic uu___4)
                                                      (fun uu___5 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___6 ->
                                                              FStar_Reflection_V2_Derived.mk_app
                                                                (FStarC_Reflection_V2_Builtins.pack_ln
                                                                   (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                                uu___5))))
                                                uu___4))) uu___3))) uu___2)))
               uu___1)
let interp_var : 'a . 'a vmap -> index -> 'a =
  fun vm ->
    fun i ->
      match FStar_List_Tot_Base.assoc i (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some x -> x
      | uu___ -> FStar_Pervasives_Native.snd vm
let rec ivl_aux : 'a . 'a cr -> 'a vmap -> index -> varlist -> 'a =
  fun r ->
    fun vm ->
      fun x ->
        fun t ->
          let amult =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_mult r) in
          match t with
          | Nil_var -> interp_var vm x
          | Cons_var (x', t') -> amult (interp_var vm x) (ivl_aux r vm x' t')
let interp_vl : 'a . 'a cr -> 'a vmap -> varlist -> 'a =
  fun r ->
    fun vm ->
      fun l ->
        let aone =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_mult r) in
        match l with | Nil_var -> aone | Cons_var (x, t) -> ivl_aux r vm x t
let interp_m : 'a . 'a cr -> 'a vmap -> 'a -> varlist -> 'a =
  fun r ->
    fun vm ->
      fun c ->
        fun l ->
          let amult =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_mult r) in
          match l with
          | Nil_var -> c
          | Cons_var (x, t) -> amult c (ivl_aux r vm x t)
let rec ics_aux : 'a . 'a cr -> 'a vmap -> 'a -> 'a canonical_sum -> 'a =
  fun r ->
    fun vm ->
      fun x ->
        fun s ->
          let aplus =
            FStar_Algebra_CommMonoid.__proj__CM__item__mult
              (__proj__CR__item__cm_add r) in
          match s with
          | Nil_monom -> x
          | Cons_varlist (l, t) ->
              aplus x (ics_aux r vm (interp_vl r vm l) t)
          | Cons_monom (c, l, t) ->
              aplus x (ics_aux r vm (interp_m r vm c l) t)
let interp_cs : 'a . 'a cr -> 'a vmap -> 'a canonical_sum -> 'a =
  fun r ->
    fun vm ->
      fun s ->
        let azero =
          FStar_Algebra_CommMonoid.__proj__CM__item__unit
            (__proj__CR__item__cm_add r) in
        match s with
        | Nil_monom -> azero
        | Cons_varlist (l, t) -> ics_aux r vm (interp_vl r vm l) t
        | Cons_monom (c, l, t) -> ics_aux r vm (interp_m r vm c l) t
let rec interp_sp : 'a . 'a cr -> 'a vmap -> 'a spolynomial -> 'a =
  fun r ->
    fun vm ->
      fun p ->
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
let uu___is_Pvar : 'a . 'a polynomial -> Prims.bool =
  fun projectee -> match projectee with | Pvar _0 -> true | uu___ -> false
let __proj__Pvar__item___0 : 'a . 'a polynomial -> index =
  fun projectee -> match projectee with | Pvar _0 -> _0
let uu___is_Pconst : 'a . 'a polynomial -> Prims.bool =
  fun projectee -> match projectee with | Pconst _0 -> true | uu___ -> false
let __proj__Pconst__item___0 : 'a . 'a polynomial -> 'a =
  fun projectee -> match projectee with | Pconst _0 -> _0
let uu___is_Pplus : 'a . 'a polynomial -> Prims.bool =
  fun projectee ->
    match projectee with | Pplus (_0, _1) -> true | uu___ -> false
let __proj__Pplus__item___0 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Pplus (_0, _1) -> _0
let __proj__Pplus__item___1 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Pplus (_0, _1) -> _1
let uu___is_Pmult : 'a . 'a polynomial -> Prims.bool =
  fun projectee ->
    match projectee with | Pmult (_0, _1) -> true | uu___ -> false
let __proj__Pmult__item___0 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Pmult (_0, _1) -> _0
let __proj__Pmult__item___1 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Pmult (_0, _1) -> _1
let uu___is_Popp : 'a . 'a polynomial -> Prims.bool =
  fun projectee -> match projectee with | Popp _0 -> true | uu___ -> false
let __proj__Popp__item___0 : 'a . 'a polynomial -> 'a polynomial =
  fun projectee -> match projectee with | Popp _0 -> _0
let rec polynomial_normalize :
  'a . 'a cr -> 'a polynomial -> 'a canonical_sum =
  fun r ->
    fun p ->
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
let polynomial_simplify : 'a . 'a cr -> 'a polynomial -> 'a canonical_sum =
  fun r -> fun p -> canonical_sum_simplify r (polynomial_normalize r p)
let rec spolynomial_of : 'a . 'a cr -> 'a polynomial -> 'a spolynomial =
  fun r ->
    fun p ->
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
                      (__proj__CR__item__cm_mult r)))),
              (spolynomial_of r p1))
let rec interp_p : 'a . 'a cr -> 'a vmap -> 'a polynomial -> 'a =
  fun r ->
    fun vm ->
      fun p ->
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
let (ddump : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    let uu___ = FStarC_Tactics_V2_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommSemiring.fst"
               (Prims.of_int (1512)) (Prims.of_int (17))
               (Prims.of_int (1512)) (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommSemiring.fst"
               (Prims.of_int (1512)) (Prims.of_int (14))
               (Prims.of_int (1512)) (Prims.of_int (41))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then Obj.magic (Obj.repr (FStarC_Tactics_V2_Builtins.dump m))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))))
           uu___1)
let rec (find_aux :
  Prims.nat ->
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term Prims.list ->
        (Prims.nat FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun n ->
           fun x ->
             fun xs ->
               match xs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pervasives_Native.None)))
               | x'::xs' ->
                   Obj.magic
                     (Obj.repr
                        (if term_eq x x'
                         then
                           Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> FStar_Pervasives_Native.Some n))
                         else Obj.repr (find_aux (n + Prims.int_one) x xs'))))
          uu___2 uu___1 uu___
let (find :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      (Prims.nat FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  = find_aux Prims.int_zero
let make_fvar :
  'a .
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term ->
         ('a, unit) FStar_Tactics_Effect.tac_repr)
        ->
        FStar_Tactics_NamedView.term Prims.list ->
          'a vmap ->
            (('a polynomial * FStar_Tactics_NamedView.term Prims.list * 'a
               vmap),
              unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    fun unquotea ->
      fun ts ->
        fun vm ->
          let uu___ = find t ts in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.CanonCommSemiring.fst"
                     (Prims.of_int (1527)) (Prims.of_int (8))
                     (Prims.of_int (1527)) (Prims.of_int (17)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.CanonCommSemiring.fst"
                     (Prims.of_int (1527)) (Prims.of_int (2))
                     (Prims.of_int (1532)) (Prims.of_int (47)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  match uu___1 with
                  | FStar_Pervasives_Native.Some v ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> ((Pvar v), ts, vm))))
                  | FStar_Pervasives_Native.None ->
                      Obj.magic
                        (Obj.repr
                           (let uu___2 =
                              Obj.magic
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 ->
                                      FStar_List_Tot_Base.length ts)) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommSemiring.fst"
                                       (Prims.of_int (1530))
                                       (Prims.of_int (17))
                                       (Prims.of_int (1530))
                                       (Prims.of_int (26)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommSemiring.fst"
                                       (Prims.of_int (1530))
                                       (Prims.of_int (29))
                                       (Prims.of_int (1532))
                                       (Prims.of_int (47)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun vfresh ->
                                    let uu___3 = unquotea t in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                  (Prims.of_int (1531))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (1531))
                                                  (Prims.of_int (22)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommSemiring.fst"
                                                  (Prims.of_int (1532))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (1532))
                                                  (Prims.of_int (47)))))
                                         (Obj.magic uu___3)
                                         (fun z ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 ->
                                                 ((Pvar vfresh),
                                                   (FStar_List_Tot_Base.op_At
                                                      ts [t]),
                                                   (update vfresh z vm))))))
                                   uu___3)))) uu___1)
let rec reification_aux :
  'a .
    (FStar_Tactics_NamedView.term -> ('a, unit) FStar_Tactics_Effect.tac_repr)
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
                      unit) FStar_Tactics_Effect.tac_repr
  =
  fun unquotea ->
    fun ts ->
      fun vm ->
        fun add ->
          fun opp ->
            fun mone ->
              fun mult ->
                fun t ->
                  let uu___ =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            FStar_Reflection_V2_Derived_Lemmas.collect_app_ref
                              t)) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.CanonCommSemiring.fst"
                             (Prims.of_int (1537)) (Prims.of_int (15))
                             (Prims.of_int (1537)) (Prims.of_int (32)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.CanonCommSemiring.fst"
                             (Prims.of_int (1535)) (Prims.of_int (157))
                             (Prims.of_int (1559)) (Prims.of_int (38)))))
                    (Obj.magic uu___)
                    (fun uu___1 ->
                       (fun uu___1 ->
                          match uu___1 with
                          | (hd, tl) ->
                              let uu___2 =
                                let uu___3 =
                                  FStar_Tactics_NamedView.inspect hd in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1538))
                                           (Prims.of_int (8))
                                           (Prims.of_int (1538))
                                           (Prims.of_int (18)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommSemiring.fst"
                                           (Prims.of_int (1538))
                                           (Prims.of_int (8))
                                           (Prims.of_int (1538))
                                           (Prims.of_int (33)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___5 ->
                                          (uu___4,
                                            (FStar_List_Tot_Base.list_unref
                                               tl)))) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommSemiring.fst"
                                            (Prims.of_int (1538))
                                            (Prims.of_int (8))
                                            (Prims.of_int (1538))
                                            (Prims.of_int (33)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommSemiring.fst"
                                            (Prims.of_int (1538))
                                            (Prims.of_int (2))
                                            (Prims.of_int (1559))
                                            (Prims.of_int (38)))))
                                   (Obj.magic uu___2)
                                   (fun uu___3 ->
                                      (fun uu___3 ->
                                         match uu___3 with
                                         | (FStar_Tactics_NamedView.Tv_FVar
                                            fv,
                                            (t1, uu___4)::(t2, uu___5)::[])
                                             ->
                                             let uu___6 =
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___7 ->
                                                       fun op ->
                                                         let uu___8 =
                                                           reification_aux
                                                             unquotea ts vm
                                                             add opp mone
                                                             mult t1 in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1544))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1544))
                                                                    (Prims.of_int (76)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1543))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (1546))
                                                                    (Prims.of_int (24)))))
                                                           (Obj.magic uu___8)
                                                           (fun uu___9 ->
                                                              (fun uu___9 ->
                                                                 match uu___9
                                                                 with
                                                                 | (e1, ts1,
                                                                    vm1) ->
                                                                    let uu___10
                                                                    =
                                                                    reification_aux
                                                                    unquotea
                                                                    ts1 vm1
                                                                    add opp
                                                                    mone mult
                                                                    t2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1545))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (1545))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1544))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (1546))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (e2, ts2,
                                                                    vm2) ->
                                                                    ((op e1
                                                                    e2), ts2,
                                                                    vm2)))))
                                                                uu___9))) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1543))
                                                           (Prims.of_int (107))
                                                           (Prims.of_int (1546))
                                                           (Prims.of_int (24)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1548))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (1550))
                                                           (Prims.of_int (30)))))
                                                  (Obj.magic uu___6)
                                                  (fun uu___7 ->
                                                     (fun binop ->
                                                        if
                                                          term_eq
                                                            (FStar_Tactics_NamedView.pack
                                                               (FStar_Tactics_NamedView.Tv_FVar
                                                                  fv)) add
                                                        then
                                                          Obj.magic
                                                            (binop
                                                               (fun uu___7 ->
                                                                  fun uu___8
                                                                    ->
                                                                    Pplus
                                                                    (uu___7,
                                                                    uu___8)))
                                                        else
                                                          if
                                                            term_eq
                                                              (FStar_Tactics_NamedView.pack
                                                                 (FStar_Tactics_NamedView.Tv_FVar
                                                                    fv)) mult
                                                          then
                                                            Obj.magic
                                                              (binop
                                                                 (fun uu___8
                                                                    ->
                                                                    fun
                                                                    uu___9 ->
                                                                    Pmult
                                                                    (uu___8,
                                                                    uu___9)))
                                                          else
                                                            Obj.magic
                                                              (make_fvar t
                                                                 unquotea ts
                                                                 vm)) uu___7))
                                         | (FStar_Tactics_NamedView.Tv_FVar
                                            fv, (t1, uu___4)::[]) ->
                                             let uu___5 =
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___6 ->
                                                       fun op ->
                                                         let uu___7 =
                                                           reification_aux
                                                             unquotea ts vm
                                                             add opp mone
                                                             mult t1 in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1553))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (1553))
                                                                    (Prims.of_int (75)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1552))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (1554))
                                                                    (Prims.of_int (20)))))
                                                           (Obj.magic uu___7)
                                                           (fun uu___8 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___9
                                                                   ->
                                                                   match uu___8
                                                                   with
                                                                   | 
                                                                   (e, ts1,
                                                                    vm1) ->
                                                                    ((op e),
                                                                    ts1, vm1))))) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1552))
                                                           (Prims.of_int (91))
                                                           (Prims.of_int (1554))
                                                           (Prims.of_int (20)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1556))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (1557))
                                                           (Prims.of_int (30)))))
                                                  (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     (fun monop ->
                                                        if
                                                          term_eq
                                                            (FStar_Tactics_NamedView.pack
                                                               (FStar_Tactics_NamedView.Tv_FVar
                                                                  fv)) opp
                                                        then
                                                          Obj.magic
                                                            (monop
                                                               (fun uu___6 ->
                                                                  Popp uu___6))
                                                        else
                                                          Obj.magic
                                                            (make_fvar t
                                                               unquotea ts vm))
                                                       uu___6))
                                         | (FStar_Tactics_NamedView.Tv_Const
                                            uu___4, []) ->
                                             let uu___5 =
                                               let uu___6 = unquotea t in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1558))
                                                          (Prims.of_int (29))
                                                          (Prims.of_int (1558))
                                                          (Prims.of_int (41)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1558))
                                                          (Prims.of_int (22))
                                                          (Prims.of_int (1558))
                                                          (Prims.of_int (41)))))
                                                 (Obj.magic uu___6)
                                                 (fun uu___7 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___8 ->
                                                         Pconst uu___7)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1558))
                                                           (Prims.of_int (22))
                                                           (Prims.of_int (1558))
                                                           (Prims.of_int (41)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1558))
                                                           (Prims.of_int (22))
                                                           (Prims.of_int (1558))
                                                           (Prims.of_int (49)))))
                                                  (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___7 ->
                                                          (uu___6, ts, vm))))
                                         | (uu___4, uu___5) ->
                                             Obj.magic
                                               (make_fvar t unquotea ts vm))
                                        uu___3))) uu___1)
let (steps : FStar_Pervasives.norm_step Prims.list) =
  [FStar_Pervasives.primops;
  FStar_Pervasives.iota;
  FStar_Pervasives.zeta;
  FStar_Pervasives.delta_attr ["FStar.Tactics.CanonCommSemiring.canon_attr"];
  FStar_Pervasives.delta_only
    ["FStar.Mul.op_Star";
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
let (canon_norm : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> FStarC_Tactics_V2_Builtins.norm steps
let reification :
  'a .
    (FStar_Tactics_NamedView.term -> ('a, unit) FStar_Tactics_Effect.tac_repr)
      ->
      ('a ->
         (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
        ->
        FStar_Tactics_NamedView.term ->
          FStar_Tactics_NamedView.term ->
            FStar_Tactics_NamedView.term ->
              FStar_Tactics_NamedView.term ->
                'a ->
                  FStar_Tactics_NamedView.term Prims.list ->
                    (('a polynomial Prims.list * 'a vmap), unit)
                      FStar_Tactics_Effect.tac_repr
  =
  fun unquotea ->
    fun quotea ->
      fun tadd ->
        fun topp ->
          fun tmone ->
            fun tmult ->
              fun munit ->
                fun ts ->
                  let uu___ =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> tadd)) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.CanonCommSemiring.fst"
                             (Prims.of_int (1597)) (Prims.of_int (13))
                             (Prims.of_int (1597)) (Prims.of_int (17)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.CanonCommSemiring.fst"
                             (Prims.of_int (1597)) (Prims.of_int (20))
                             (Prims.of_int (1609)) (Prims.of_int (31)))))
                    (Obj.magic uu___)
                    (fun uu___1 ->
                       (fun add ->
                          let uu___1 =
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> topp)) in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1598))
                                        (Prims.of_int (13))
                                        (Prims.of_int (1598))
                                        (Prims.of_int (17)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1598))
                                        (Prims.of_int (20))
                                        (Prims.of_int (1609))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___1)
                               (fun uu___2 ->
                                  (fun opp ->
                                     let uu___2 =
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___3 -> tmone)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommSemiring.fst"
                                                   (Prims.of_int (1599))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (1599))
                                                   (Prims.of_int (18)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommSemiring.fst"
                                                   (Prims.of_int (1599))
                                                   (Prims.of_int (21))
                                                   (Prims.of_int (1609))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic uu___2)
                                          (fun uu___3 ->
                                             (fun mone ->
                                                let uu___3 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 -> tmult)) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (1600))
                                                              (Prims.of_int (13))
                                                              (Prims.of_int (1600))
                                                              (Prims.of_int (18)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommSemiring.fst"
                                                              (Prims.of_int (1600))
                                                              (Prims.of_int (21))
                                                              (Prims.of_int (1609))
                                                              (Prims.of_int (31)))))
                                                     (Obj.magic uu___3)
                                                     (fun uu___4 ->
                                                        (fun mult ->
                                                           let uu___4 =
                                                             FStar_Tactics_Util.map
                                                               (FStar_Tactics_V2_Derived.norm_term
                                                                  steps) ts in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1601))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (1601))
                                                                    (Prims.of_int (48)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1601))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (1609))
                                                                    (Prims.of_int (31)))))
                                                                (Obj.magic
                                                                   uu___4)
                                                                (fun uu___5
                                                                   ->
                                                                   (fun ts1
                                                                    ->
                                                                    let uu___5
                                                                    =
                                                                    FStar_Tactics_Util.fold_left
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun t ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (es, vs,
                                                                    vm) ->
                                                                    let uu___7
                                                                    =
                                                                    reification_aux
                                                                    unquotea
                                                                    vs vm add
                                                                    opp mone
                                                                    mult t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1606))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (1606))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1605))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (1607))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (e, vs1,
                                                                    vm1) ->
                                                                    ((e ::
                                                                    es), vs1,
                                                                    vm1))))
                                                                    ([], [],
                                                                    ([],
                                                                    munit))
                                                                    ts1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1604))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1608))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1601))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (1609))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (es,
                                                                    uu___8,
                                                                    vm) ->
                                                                    ((FStar_List_Tot_Base.rev
                                                                    es), vm)))))
                                                                    uu___5)))
                                                          uu___4))) uu___3)))
                                    uu___2))) uu___1)
let rec quote_polynomial :
  'a .
    FStar_Tactics_NamedView.term ->
      ('a ->
         (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
        ->
        'a polynomial ->
          (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun ta ->
           fun quotea ->
             fun e ->
               match e with
               | Pconst c ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = quotea c in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommSemiring.fst"
                                          (Prims.of_int (1614))
                                          (Prims.of_int (53))
                                          (Prims.of_int (1614))
                                          (Prims.of_int (61)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommSemiring.fst"
                                          (Prims.of_int (1614))
                                          (Prims.of_int (52))
                                          (Prims.of_int (1614))
                                          (Prims.of_int (74)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 ->
                                         (uu___4,
                                           FStarC_Reflection_V2_Data.Q_Explicit))) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1614))
                                        (Prims.of_int (52))
                                        (Prims.of_int (1614))
                                        (Prims.of_int (74)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommSemiring.fst"
                                        (Prims.of_int (1614))
                                        (Prims.of_int (33))
                                        (Prims.of_int (1614))
                                        (Prims.of_int (75)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___4 -> [uu___3])) in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1614))
                                      (Prims.of_int (33))
                                      (Prims.of_int (1614))
                                      (Prims.of_int (75)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1614))
                                      (Prims.of_int (33))
                                      (Prims.of_int (1614))
                                      (Prims.of_int (75)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     (ta,
                                       FStarC_Reflection_V2_Data.Q_Implicit)
                                     :: uu___2)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1614)) (Prims.of_int (33))
                                    (Prims.of_int (1614)) (Prims.of_int (75)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1614)) (Prims.of_int (16))
                                    (Prims.of_int (1614)) (Prims.of_int (75)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Reflection_V2_Derived.mk_app
                                     (FStarC_Reflection_V2_Builtins.pack_ln
                                        (FStarC_Reflection_V2_Data.Tv_FVar
                                           (FStarC_Reflection_V2_Builtins.pack_fv
                                              ["FStar";
                                              "Tactics";
                                              "CanonCommSemiring";
                                              "Pconst"]))) uu___1))))
               | Pvar x ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Reflection_V2_Derived.mk_e_app
                                (FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_FVar
                                      (FStarC_Reflection_V2_Builtins.pack_fv
                                         ["FStar";
                                         "Tactics";
                                         "CanonCommSemiring";
                                         "Pvar"])))
                                [FStar_Tactics_NamedView.pack
                                   (FStar_Tactics_NamedView.Tv_Const
                                      (FStarC_Reflection_V2_Data.C_Int x))])))
               | Pplus (e1, e2) ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           let uu___1 = quote_polynomial ta quotea e1 in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1617))
                                      (Prims.of_int (23))
                                      (Prims.of_int (1617))
                                      (Prims.of_int (52)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1617))
                                      (Prims.of_int (22))
                                      (Prims.of_int (1617))
                                      (Prims.of_int (84)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   let uu___3 =
                                     let uu___4 =
                                       quote_polynomial ta quotea e2 in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1617))
                                                (Prims.of_int (54))
                                                (Prims.of_int (1617))
                                                (Prims.of_int (83)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1617))
                                                (Prims.of_int (22))
                                                (Prims.of_int (1617))
                                                (Prims.of_int (84)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___6 -> [uu___5])) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (1617))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (1617))
                                                 (Prims.of_int (84)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (1617))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (1617))
                                                 (Prims.of_int (84)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___5 -> uu___2 :: uu___4))))
                                  uu___2) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1617)) (Prims.of_int (22))
                                    (Prims.of_int (1617)) (Prims.of_int (84)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1617)) (Prims.of_int (4))
                                    (Prims.of_int (1617)) (Prims.of_int (84)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Reflection_V2_Derived.mk_e_app
                                     (FStarC_Reflection_V2_Builtins.pack_ln
                                        (FStarC_Reflection_V2_Data.Tv_FVar
                                           (FStarC_Reflection_V2_Builtins.pack_fv
                                              ["FStar";
                                              "Tactics";
                                              "CanonCommSemiring";
                                              "Pplus"]))) uu___1))))
               | Pmult (e1, e2) ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           let uu___1 = quote_polynomial ta quotea e1 in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1619))
                                      (Prims.of_int (23))
                                      (Prims.of_int (1619))
                                      (Prims.of_int (52)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1619))
                                      (Prims.of_int (22))
                                      (Prims.of_int (1619))
                                      (Prims.of_int (84)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   let uu___3 =
                                     let uu___4 =
                                       quote_polynomial ta quotea e2 in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1619))
                                                (Prims.of_int (54))
                                                (Prims.of_int (1619))
                                                (Prims.of_int (83)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1619))
                                                (Prims.of_int (22))
                                                (Prims.of_int (1619))
                                                (Prims.of_int (84)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___6 -> [uu___5])) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (1619))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (1619))
                                                 (Prims.of_int (84)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommSemiring.fst"
                                                 (Prims.of_int (1619))
                                                 (Prims.of_int (22))
                                                 (Prims.of_int (1619))
                                                 (Prims.of_int (84)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___5 -> uu___2 :: uu___4))))
                                  uu___2) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1619)) (Prims.of_int (22))
                                    (Prims.of_int (1619)) (Prims.of_int (84)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1619)) (Prims.of_int (4))
                                    (Prims.of_int (1619)) (Prims.of_int (84)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Reflection_V2_Derived.mk_e_app
                                     (FStarC_Reflection_V2_Builtins.pack_ln
                                        (FStarC_Reflection_V2_Data.Tv_FVar
                                           (FStarC_Reflection_V2_Builtins.pack_fv
                                              ["FStar";
                                              "Tactics";
                                              "CanonCommSemiring";
                                              "Pmult"]))) uu___1))))
               | Popp e1 ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           let uu___1 = quote_polynomial ta quotea e1 in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1620))
                                      (Prims.of_int (32))
                                      (Prims.of_int (1620))
                                      (Prims.of_int (60)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommSemiring.fst"
                                      (Prims.of_int (1620))
                                      (Prims.of_int (31))
                                      (Prims.of_int (1620))
                                      (Prims.of_int (61)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> [uu___2])) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1620)) (Prims.of_int (31))
                                    (Prims.of_int (1620)) (Prims.of_int (61)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1620)) (Prims.of_int (14))
                                    (Prims.of_int (1620)) (Prims.of_int (61)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Reflection_V2_Derived.mk_e_app
                                     (FStarC_Reflection_V2_Builtins.pack_ln
                                        (FStarC_Reflection_V2_Data.Tv_FVar
                                           (FStarC_Reflection_V2_Builtins.pack_fv
                                              ["FStar";
                                              "Tactics";
                                              "CanonCommSemiring";
                                              "Popp"]))) uu___1))))) uu___2
          uu___1 uu___
let canon_semiring_aux :
  'a .
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term ->
         ('a, unit) FStar_Tactics_Effect.tac_repr)
        ->
        ('a ->
           (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
          ->
          FStar_Tactics_NamedView.term ->
            FStar_Tactics_NamedView.term ->
              FStar_Tactics_NamedView.term ->
                FStar_Tactics_NamedView.term ->
                  FStar_Tactics_NamedView.term ->
                    'a -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun ta ->
    fun unquotea ->
      fun quotea ->
        fun tr ->
          fun tadd ->
            fun topp ->
              fun tmone ->
                fun tmult ->
                  fun munit ->
                    FStar_Tactics_V2_Derived.focus
                      (fun uu___ ->
                         let uu___1 = FStarC_Tactics_V2_Builtins.norm [] in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1642)) (Prims.of_int (2))
                                    (Prims.of_int (1642)) (Prims.of_int (9)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1642)) (Prims.of_int (10))
                                    (Prims.of_int (1691)) (Prims.of_int (42)))))
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 let uu___3 =
                                   FStar_Tactics_V2_Derived.cur_goal () in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1643))
                                               (Prims.of_int (10))
                                               (Prims.of_int (1643))
                                               (Prims.of_int (21)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1644))
                                               (Prims.of_int (2))
                                               (Prims.of_int (1691))
                                               (Prims.of_int (42)))))
                                      (Obj.magic uu___3)
                                      (fun uu___4 ->
                                         (fun g ->
                                            let uu___4 =
                                              FStar_Reflection_V2_Formula.term_as_formula
                                                g in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1644))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (1644))
                                                          (Prims.of_int (25)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1644))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (1691))
                                                          (Prims.of_int (42)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    (fun uu___5 ->
                                                       match uu___5 with
                                                       | FStar_Reflection_V2_Formula.Comp
                                                           (FStar_Reflection_V2_Formula.Eq
                                                            (FStar_Pervasives_Native.Some
                                                            t), t1, t2)
                                                           ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (let uu___6 =
                                                                   FStar_Tactics_V2_Derived.tcut
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "squash"]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "eq2"]))),
                                                                    (ta,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit)))),
                                                                    (t1,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (t2,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))) in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1649))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (1649))
                                                                    (Prims.of_int (56)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1652))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1690))
                                                                    (Prims.of_int (7)))))
                                                                   (Obj.magic
                                                                    uu___6)
                                                                   (fun
                                                                    uu___7 ->
                                                                    (fun b ->
                                                                    let uu___7
                                                                    =
                                                                    FStar_Tactics_V2_Derived.try_with
                                                                    (fun
                                                                    uu___8 ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_V2_Derived.exact
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_V2_Derived.smt
                                                                    ()) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1653))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1653))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1656))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1689))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    reification
                                                                    unquotea
                                                                    quotea
                                                                    tadd topp
                                                                    tmone
                                                                    tmult
                                                                    munit
                                                                    [t1; t2] in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1656))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (1656))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1656))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1689))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (e1::e2::[],
                                                                    vm) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    quote_vm
                                                                    ta quotea
                                                                    vm in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1670))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (1670))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1670))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun tvm
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    quote_polynomial
                                                                    ta quotea
                                                                    e1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1671))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (1671))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1671))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun te1
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    quote_polynomial
                                                                    ta quotea
                                                                    e2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1673))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (1673))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun te2
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStar_Tactics_MApply.mapply
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
                                                                    (tvm,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (te1,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (te2,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (t1,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (t2,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1676))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1678))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    canon_norm
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1678))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1678))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStar_Tactics_V2_Derived.later
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1680))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1682))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    canon_norm
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1682))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1682))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1684))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStar_Tactics_V2_Derived.trefl
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1684))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1684))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    canon_norm
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1686))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (1688))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.trefl
                                                                    ()))
                                                                    uu___25)))
                                                                    uu___23)))
                                                                    uu___21)))
                                                                    uu___19)))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    | 
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Unexpected")))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                       | uu___6 ->
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_V2_Derived.fail
                                                                   "Goal should be an equality")))
                                                      uu___5))) uu___4)))
                                uu___2))
let canon_semiring : 'a . 'a cr -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun r ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              (fun uu___1 ->
                 Obj.magic
                   (failwith "Cannot evaluate open quotation at runtime"))
                uu___1)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommSemiring.fst"
               (Prims.of_int (1695)) (Prims.of_int (4)) (Prims.of_int (1695))
               (Prims.of_int (13)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommSemiring.fst"
               (Prims.of_int (1694)) (Prims.of_int (2)) (Prims.of_int (1700))
               (Prims.of_int (17))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___3 ->
                      (fun uu___3 ->
                         Obj.magic
                           (failwith
                              "Cannot evaluate open quotation at runtime"))
                        uu___3)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommSemiring.fst"
                          (Prims.of_int (1695)) (Prims.of_int (50))
                          (Prims.of_int (1695)) (Prims.of_int (59)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommSemiring.fst"
                          (Prims.of_int (1694)) (Prims.of_int (2))
                          (Prims.of_int (1700)) (Prims.of_int (17)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       let uu___4 =
                         let uu___5 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___6 ->
                                   (fun uu___6 ->
                                      Obj.magic
                                        (failwith
                                           "Cannot evaluate open quotation at runtime"))
                                     uu___6)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1696)) (Prims.of_int (21))
                                    (Prims.of_int (1696)) (Prims.of_int (42)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommSemiring.fst"
                                    (Prims.of_int (1696)) (Prims.of_int (4))
                                    (Prims.of_int (1696)) (Prims.of_int (43)))))
                           (Obj.magic uu___5)
                           (fun uu___6 ->
                              (fun uu___6 ->
                                 Obj.magic
                                   (FStar_Tactics_V2_Derived.norm_term steps
                                      uu___6)) uu___6) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (1696)) (Prims.of_int (4))
                                     (Prims.of_int (1696))
                                     (Prims.of_int (43)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommSemiring.fst"
                                     (Prims.of_int (1694)) (Prims.of_int (2))
                                     (Prims.of_int (1700))
                                     (Prims.of_int (17)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___6 =
                                    let uu___7 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___8 ->
                                              (fun uu___8 ->
                                                 Obj.magic
                                                   (failwith
                                                      "Cannot evaluate open quotation at runtime"))
                                                uu___8)) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1697))
                                               (Prims.of_int (21))
                                               (Prims.of_int (1697))
                                               (Prims.of_int (34)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommSemiring.fst"
                                               (Prims.of_int (1697))
                                               (Prims.of_int (4))
                                               (Prims.of_int (1697))
                                               (Prims.of_int (35)))))
                                      (Obj.magic uu___7)
                                      (fun uu___8 ->
                                         (fun uu___8 ->
                                            Obj.magic
                                              (FStar_Tactics_V2_Derived.norm_term
                                                 steps uu___8)) uu___8) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1697))
                                                (Prims.of_int (4))
                                                (Prims.of_int (1697))
                                                (Prims.of_int (35)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommSemiring.fst"
                                                (Prims.of_int (1694))
                                                (Prims.of_int (2))
                                                (Prims.of_int (1700))
                                                (Prims.of_int (17)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun uu___7 ->
                                             let uu___8 =
                                               let uu___9 =
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___10 ->
                                                         (fun uu___10 ->
                                                            Obj.magic
                                                              (failwith
                                                                 "Cannot evaluate open quotation at runtime"))
                                                           uu___10)) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1698))
                                                          (Prims.of_int (21))
                                                          (Prims.of_int (1698))
                                                          (Prims.of_int (51)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommSemiring.fst"
                                                          (Prims.of_int (1698))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (1698))
                                                          (Prims.of_int (52)))))
                                                 (Obj.magic uu___9)
                                                 (fun uu___10 ->
                                                    (fun uu___10 ->
                                                       Obj.magic
                                                         (FStar_Tactics_V2_Derived.norm_term
                                                            steps uu___10))
                                                      uu___10) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1698))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (1698))
                                                           (Prims.of_int (52)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommSemiring.fst"
                                                           (Prims.of_int (1694))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (1700))
                                                           (Prims.of_int (17)))))
                                                  (Obj.magic uu___8)
                                                  (fun uu___9 ->
                                                     (fun uu___9 ->
                                                        let uu___10 =
                                                          let uu___11 =
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___12)) in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1699))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (1699))
                                                                    (Prims.of_int (43)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1699))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1699))
                                                                    (Prims.of_int (44)))))
                                                            (Obj.magic
                                                               uu___11)
                                                            (fun uu___12 ->
                                                               (fun uu___12
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_V2_Derived.norm_term
                                                                    steps
                                                                    uu___12))
                                                                 uu___12) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1699))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (1699))
                                                                    (Prims.of_int (44)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommSemiring.fst"
                                                                    (Prims.of_int (1694))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (1700))
                                                                    (Prims.of_int (17)))))
                                                             (Obj.magic
                                                                uu___10)
                                                             (fun uu___11 ->
                                                                (fun uu___11
                                                                   ->
                                                                   Obj.magic
                                                                    (canon_semiring_aux
                                                                    uu___1
                                                                    FStarC_Tactics_V2_Builtins.unquote
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___12)))
                                                                    uu___12)
                                                                    uu___3
                                                                    uu___5
                                                                    uu___7
                                                                    uu___9
                                                                    uu___11
                                                                    (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                                    (__proj__CR__item__cm_add
                                                                    r))))
                                                                  uu___11)))
                                                       uu___9))) uu___7)))
                                 uu___5))) uu___3))) uu___1)
let (int_cr : Prims.int cr) =
  CR
    (FStar_Algebra_CommMonoid.int_plus_cm,
      FStar_Algebra_CommMonoid.int_multiply_cm, (~-), (), (), ())
let (int_semiring : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> canon_semiring int_cr