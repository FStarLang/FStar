open Fstarcompiler
open Prims
let bv_to_string (bv : FStarC_Reflection_Types.bv) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Reflection_V1_Builtins.inspect_bv bv in
    FStarC_Tactics_Unseal.unseal x.FStarC_Reflection_V1_Data.bv_ppname ps
let rec inspect_unascribe (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_V1_Data.term_view, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.inspect t ps in
    match x with
    | FStarC_Reflection_V1_Data.Tv_AscribedT (t1, uu___, uu___1, uu___2) ->
        inspect_unascribe t1 ps
    | FStarC_Reflection_V1_Data.Tv_AscribedC (t1, uu___, uu___1, uu___2) ->
        inspect_unascribe t1 ps
    | tv -> tv
let rec collect_app' (args : FStarC_Reflection_V1_Data.argv Prims.list)
  (t : FStarC_Reflection_Types.term) :
  ((FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv Prims.list),
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = inspect_unascribe t ps in
    match x with
    | FStarC_Reflection_V1_Data.Tv_App (l, r) ->
        collect_app' (r :: args) l ps
    | uu___ -> (t, args)
let collect_app :
  FStarC_Reflection_Types.term ->
    ((FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr=
  collect_app' []
type comparison =
  | Eq of FStarC_Reflection_Types.typ FStar_Pervasives_Native.option 
  | BoolEq of FStarC_Reflection_Types.typ FStar_Pervasives_Native.option 
  | Lt 
  | Le 
  | Gt 
  | Ge 
let uu___is_Eq (projectee : comparison) : Prims.bool=
  match projectee with | Eq _0 -> true | uu___ -> false
let __proj__Eq__item___0 (projectee : comparison) :
  FStarC_Reflection_Types.typ FStar_Pervasives_Native.option=
  match projectee with | Eq _0 -> _0
let uu___is_BoolEq (projectee : comparison) : Prims.bool=
  match projectee with | BoolEq _0 -> true | uu___ -> false
let __proj__BoolEq__item___0 (projectee : comparison) :
  FStarC_Reflection_Types.typ FStar_Pervasives_Native.option=
  match projectee with | BoolEq _0 -> _0
let uu___is_Lt (projectee : comparison) : Prims.bool=
  match projectee with | Lt -> true | uu___ -> false
let uu___is_Le (projectee : comparison) : Prims.bool=
  match projectee with | Le -> true | uu___ -> false
let uu___is_Gt (projectee : comparison) : Prims.bool=
  match projectee with | Gt -> true | uu___ -> false
let uu___is_Ge (projectee : comparison) : Prims.bool=
  match projectee with | Ge -> true | uu___ -> false
type formula =
  | True_ 
  | False_ 
  | Comp of comparison * FStarC_Reflection_Types.term *
  FStarC_Reflection_Types.term 
  | And of FStarC_Reflection_Types.term * FStarC_Reflection_Types.term 
  | Or of FStarC_Reflection_Types.term * FStarC_Reflection_Types.term 
  | Not of FStarC_Reflection_Types.term 
  | Implies of FStarC_Reflection_Types.term * FStarC_Reflection_Types.term 
  | Iff of FStarC_Reflection_Types.term * FStarC_Reflection_Types.term 
  | Forall of FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ *
  FStarC_Reflection_Types.term 
  | Exists of FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ *
  FStarC_Reflection_Types.term 
  | App of FStarC_Reflection_Types.term * FStarC_Reflection_Types.term 
  | Name of FStarC_Reflection_Types.bv 
  | FV of FStarC_Reflection_Types.fv 
  | IntLit of Prims.int 
  | F_Unknown 
let uu___is_True_ (projectee : formula) : Prims.bool=
  match projectee with | True_ -> true | uu___ -> false
let uu___is_False_ (projectee : formula) : Prims.bool=
  match projectee with | False_ -> true | uu___ -> false
let uu___is_Comp (projectee : formula) : Prims.bool=
  match projectee with | Comp (_0, _1, _2) -> true | uu___ -> false
let __proj__Comp__item___0 (projectee : formula) : comparison=
  match projectee with | Comp (_0, _1, _2) -> _0
let __proj__Comp__item___1 (projectee : formula) :
  FStarC_Reflection_Types.term=
  match projectee with | Comp (_0, _1, _2) -> _1
let __proj__Comp__item___2 (projectee : formula) :
  FStarC_Reflection_Types.term=
  match projectee with | Comp (_0, _1, _2) -> _2
let uu___is_And (projectee : formula) : Prims.bool=
  match projectee with | And (_0, _1) -> true | uu___ -> false
let __proj__And__item___0 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | And (_0, _1) -> _0
let __proj__And__item___1 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | And (_0, _1) -> _1
let uu___is_Or (projectee : formula) : Prims.bool=
  match projectee with | Or (_0, _1) -> true | uu___ -> false
let __proj__Or__item___0 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | Or (_0, _1) -> _0
let __proj__Or__item___1 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | Or (_0, _1) -> _1
let uu___is_Not (projectee : formula) : Prims.bool=
  match projectee with | Not _0 -> true | uu___ -> false
let __proj__Not__item___0 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | Not _0 -> _0
let uu___is_Implies (projectee : formula) : Prims.bool=
  match projectee with | Implies (_0, _1) -> true | uu___ -> false
let __proj__Implies__item___0 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | Implies (_0, _1) -> _0
let __proj__Implies__item___1 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | Implies (_0, _1) -> _1
let uu___is_Iff (projectee : formula) : Prims.bool=
  match projectee with | Iff (_0, _1) -> true | uu___ -> false
let __proj__Iff__item___0 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | Iff (_0, _1) -> _0
let __proj__Iff__item___1 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | Iff (_0, _1) -> _1
let uu___is_Forall (projectee : formula) : Prims.bool=
  match projectee with | Forall (_0, _1, _2) -> true | uu___ -> false
let __proj__Forall__item___0 (projectee : formula) :
  FStarC_Reflection_Types.bv=
  match projectee with | Forall (_0, _1, _2) -> _0
let __proj__Forall__item___1 (projectee : formula) :
  FStarC_Reflection_Types.typ=
  match projectee with | Forall (_0, _1, _2) -> _1
let __proj__Forall__item___2 (projectee : formula) :
  FStarC_Reflection_Types.term=
  match projectee with | Forall (_0, _1, _2) -> _2
let uu___is_Exists (projectee : formula) : Prims.bool=
  match projectee with | Exists (_0, _1, _2) -> true | uu___ -> false
let __proj__Exists__item___0 (projectee : formula) :
  FStarC_Reflection_Types.bv=
  match projectee with | Exists (_0, _1, _2) -> _0
let __proj__Exists__item___1 (projectee : formula) :
  FStarC_Reflection_Types.typ=
  match projectee with | Exists (_0, _1, _2) -> _1
let __proj__Exists__item___2 (projectee : formula) :
  FStarC_Reflection_Types.term=
  match projectee with | Exists (_0, _1, _2) -> _2
let uu___is_App (projectee : formula) : Prims.bool=
  match projectee with | App (_0, _1) -> true | uu___ -> false
let __proj__App__item___0 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | App (_0, _1) -> _0
let __proj__App__item___1 (projectee : formula) :
  FStarC_Reflection_Types.term= match projectee with | App (_0, _1) -> _1
let uu___is_Name (projectee : formula) : Prims.bool=
  match projectee with | Name _0 -> true | uu___ -> false
let __proj__Name__item___0 (projectee : formula) :
  FStarC_Reflection_Types.bv= match projectee with | Name _0 -> _0
let uu___is_FV (projectee : formula) : Prims.bool=
  match projectee with | FV _0 -> true | uu___ -> false
let __proj__FV__item___0 (projectee : formula) : FStarC_Reflection_Types.fv=
  match projectee with | FV _0 -> _0
let uu___is_IntLit (projectee : formula) : Prims.bool=
  match projectee with | IntLit _0 -> true | uu___ -> false
let __proj__IntLit__item___0 (projectee : formula) : Prims.int=
  match projectee with | IntLit _0 -> _0
let uu___is_F_Unknown (projectee : formula) : Prims.bool=
  match projectee with | F_Unknown -> true | uu___ -> false
let mk_Forall (uu___1 : FStarC_Reflection_Types.term)
  (uu___ : FStarC_Reflection_Types.term) :
  (formula, unit) FStar_Tactics_Effect.tac_repr=
  (fun typ pred ->
     Obj.magic
       (fun uu___ ->
          Forall
            ((FStarC_Reflection_V1_Builtins.pack_bv
                {
                  FStarC_Reflection_V1_Data.bv_ppname =
                    (FStarC_Reflection_V1_Data.as_ppname "x");
                  FStarC_Reflection_V1_Data.bv_index = Prims.int_zero
                }), typ,
              (FStarC_Reflection_V1_Builtins.pack_ln
                 (FStarC_Reflection_V1_Data.Tv_App
                    (pred,
                      ((FStarC_Reflection_V1_Builtins.pack_ln
                          (FStarC_Reflection_V1_Data.Tv_BVar
                             (FStarC_Reflection_V1_Builtins.pack_bv
                                {
                                  FStarC_Reflection_V1_Data.bv_ppname =
                                    (FStarC_Reflection_V1_Data.as_ppname "x");
                                  FStarC_Reflection_V1_Data.bv_index =
                                    Prims.int_zero
                                }))), FStarC_Reflection_V1_Data.Q_Explicit)))))))
    uu___1 uu___
let mk_Exists (uu___1 : FStarC_Reflection_Types.term)
  (uu___ : FStarC_Reflection_Types.term) :
  (formula, unit) FStar_Tactics_Effect.tac_repr=
  (fun typ pred ->
     Obj.magic
       (fun uu___ ->
          Exists
            ((FStarC_Reflection_V1_Builtins.pack_bv
                {
                  FStarC_Reflection_V1_Data.bv_ppname =
                    (FStarC_Reflection_V1_Data.as_ppname "x");
                  FStarC_Reflection_V1_Data.bv_index = Prims.int_zero
                }), typ,
              (FStarC_Reflection_V1_Builtins.pack_ln
                 (FStarC_Reflection_V1_Data.Tv_App
                    (pred,
                      ((FStarC_Reflection_V1_Builtins.pack_ln
                          (FStarC_Reflection_V1_Data.Tv_BVar
                             (FStarC_Reflection_V1_Builtins.pack_bv
                                {
                                  FStarC_Reflection_V1_Data.bv_ppname =
                                    (FStarC_Reflection_V1_Data.as_ppname "x");
                                  FStarC_Reflection_V1_Data.bv_index =
                                    Prims.int_zero
                                }))), FStarC_Reflection_V1_Data.Q_Explicit)))))))
    uu___1 uu___
let term_as_formula' (t : FStarC_Reflection_Types.term) :
  (formula, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = inspect_unascribe t ps in
    match x with
    | FStarC_Reflection_V1_Data.Tv_Var n -> Name n
    | FStarC_Reflection_V1_Data.Tv_FVar fv ->
        if
          (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
            FStar_Reflection_Const.true_qn
        then True_
        else
          if
            (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
              FStar_Reflection_Const.false_qn
          then False_
          else FV fv
    | FStarC_Reflection_V1_Data.Tv_UInst (fv, uu___) ->
        if
          (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
            FStar_Reflection_Const.true_qn
        then True_
        else
          if
            (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
              FStar_Reflection_Const.false_qn
          then False_
          else FV fv
    | FStarC_Reflection_V1_Data.Tv_App (h0, t1) ->
        let x1 = collect_app h0 ps in
        (match x1 with
         | (h, ts) ->
             let x2 = FStar_Reflection_V1_Derived.un_uinst h in
             (match ((FStarC_Reflection_V1_Builtins.inspect_ln x2),
                      (FStar_List_Tot_Base.op_At ts [t1]))
              with
              | (FStarC_Reflection_V1_Data.Tv_FVar fv,
                 (a1, FStarC_Reflection_V1_Data.Q_Implicit)::(a2,
                                                              FStarC_Reflection_V1_Data.Q_Explicit)::
                 (a3, FStarC_Reflection_V1_Data.Q_Explicit)::[]) ->
                  if
                    (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                      FStar_Reflection_Const.eq2_qn
                  then Comp ((Eq (FStar_Pervasives_Native.Some a1)), a2, a3)
                  else
                    if
                      (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                        FStar_Reflection_Const.eq1_qn
                    then
                      Comp
                        ((BoolEq (FStar_Pervasives_Native.Some a1)), a2, a3)
                    else
                      if
                        (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                          FStar_Reflection_Const.lt_qn
                      then Comp (Lt, a2, a3)
                      else
                        if
                          (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                            FStar_Reflection_Const.lte_qn
                        then Comp (Le, a2, a3)
                        else
                          if
                            (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                              FStar_Reflection_Const.gt_qn
                          then Comp (Gt, a2, a3)
                          else
                            if
                              (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                                FStar_Reflection_Const.gte_qn
                            then Comp (Ge, a2, a3)
                            else App (h0, (FStar_Pervasives_Native.fst t1))
              | (FStarC_Reflection_V1_Data.Tv_FVar fv,
                 (a1, FStarC_Reflection_V1_Data.Q_Explicit)::(a2,
                                                              FStarC_Reflection_V1_Data.Q_Explicit)::[])
                  ->
                  if
                    (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                      FStar_Reflection_Const.imp_qn
                  then Implies (a1, a2)
                  else
                    if
                      (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                        FStar_Reflection_Const.and_qn
                    then And (a1, a2)
                    else
                      if
                        (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                          FStar_Reflection_Const.iff_qn
                      then Iff (a1, a2)
                      else
                        if
                          (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                            FStar_Reflection_Const.or_qn
                        then Or (a1, a2)
                        else
                          if
                            (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                              FStar_Reflection_Const.eq2_qn
                          then
                            Comp ((Eq FStar_Pervasives_Native.None), a1, a2)
                          else
                            if
                              (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                                FStar_Reflection_Const.eq1_qn
                            then
                              Comp
                                ((BoolEq FStar_Pervasives_Native.None), a1,
                                  a2)
                            else App (h0, (FStar_Pervasives_Native.fst t1))
              | (FStarC_Reflection_V1_Data.Tv_FVar fv,
                 (a1, FStarC_Reflection_V1_Data.Q_Implicit)::(a2,
                                                              FStarC_Reflection_V1_Data.Q_Explicit)::[])
                  ->
                  let x3 = FStarC_Reflection_V1_Builtins.inspect_fv fv in
                  if x3 = FStar_Reflection_Const.forall_qn
                  then mk_Forall a1 a2 ps
                  else
                    if x3 = FStar_Reflection_Const.exists_qn
                    then mk_Exists a1 a2 ps
                    else App (h0, (FStar_Pervasives_Native.fst t1))
              | (FStarC_Reflection_V1_Data.Tv_FVar fv,
                 (a, FStarC_Reflection_V1_Data.Q_Explicit)::[]) ->
                  if
                    (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                      FStar_Reflection_Const.not_qn
                  then Not a
                  else
                    if
                      (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                        FStar_Reflection_Const.b2t_qn
                    then
                      (if
                         FStar_Reflection_TermEq_Simple.term_eq a
                           (FStarC_Reflection_V2_Builtins.pack_ln
                              (FStarC_Reflection_V2_Data.Tv_Const
                                 FStarC_Reflection_V2_Data.C_False))
                       then False_
                       else
                         if
                           FStar_Reflection_TermEq_Simple.term_eq a
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_Const
                                   FStarC_Reflection_V2_Data.C_True))
                         then True_
                         else App (h0, (FStar_Pervasives_Native.fst t1)))
                    else App (h0, (FStar_Pervasives_Native.fst t1))
              | uu___ -> App (h0, (FStar_Pervasives_Native.fst t1))))
    | FStarC_Reflection_V1_Data.Tv_Const (FStarC_Reflection_V1_Data.C_Int i)
        -> IntLit i
    | FStarC_Reflection_V1_Data.Tv_Let
        (uu___, uu___1, uu___2, uu___3, uu___4, uu___5) -> F_Unknown
    | FStarC_Reflection_V1_Data.Tv_Match (uu___, uu___1, uu___2) -> F_Unknown
    | FStarC_Reflection_V1_Data.Tv_Type uu___ -> F_Unknown
    | FStarC_Reflection_V1_Data.Tv_Abs (uu___, uu___1) -> F_Unknown
    | FStarC_Reflection_V1_Data.Tv_Arrow (uu___, uu___1) -> F_Unknown
    | FStarC_Reflection_V1_Data.Tv_Uvar (uu___, uu___1) -> F_Unknown
    | FStarC_Reflection_V1_Data.Tv_Unknown -> F_Unknown
    | FStarC_Reflection_V1_Data.Tv_Unsupp -> F_Unknown
    | FStarC_Reflection_V1_Data.Tv_Refine (uu___, uu___1, uu___2) ->
        F_Unknown
    | FStarC_Reflection_V1_Data.Tv_Const uu___ -> F_Unknown
    | FStarC_Reflection_V1_Data.Tv_BVar uu___ -> F_Unknown
let term_as_formula (uu___ : FStarC_Reflection_Types.term) :
  (formula, unit) FStar_Tactics_Effect.tac_repr=
  (fun t ->
     match FStar_Reflection_V1_Derived.unsquash_term t with
     | FStar_Pervasives_Native.None ->
         Obj.magic (Obj.repr (fun uu___ -> F_Unknown))
     | FStar_Pervasives_Native.Some t1 ->
         Obj.magic (Obj.repr (term_as_formula' t1))) uu___
let term_as_formula_total (t : FStarC_Reflection_Types.term) :
  (formula, unit) FStar_Tactics_Effect.tac_repr=
  term_as_formula' (FStar_Reflection_V1_Derived.maybe_unsquash_term t)
let formula_as_term_view (f : formula) : FStarC_Reflection_V1_Data.term_view=
  let mk_app' tv args =
    FStar_List_Tot_Base.fold_left
      (fun tv1 a ->
         FStarC_Reflection_V1_Data.Tv_App
           ((FStarC_Reflection_V1_Builtins.pack_ln tv1), a)) tv args in
  let e = FStarC_Reflection_V1_Data.Q_Explicit in
  let i = FStarC_Reflection_V1_Data.Q_Implicit in
  match f with
  | True_ ->
      FStarC_Reflection_V1_Data.Tv_FVar
        (FStarC_Reflection_V1_Builtins.pack_fv FStar_Reflection_Const.true_qn)
  | False_ ->
      FStarC_Reflection_V1_Data.Tv_FVar
        (FStarC_Reflection_V1_Builtins.pack_fv
           FStar_Reflection_Const.false_qn)
  | Comp (Eq (FStar_Pervasives_Native.None), l, r) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.eq2_qn)) [(l, e); (r, e)]
  | Comp (Eq (FStar_Pervasives_Native.Some t), l, r) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.eq2_qn)) [(t, i); (l, e); (r, e)]
  | Comp (BoolEq (FStar_Pervasives_Native.None), l, r) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.eq1_qn)) [(l, e); (r, e)]
  | Comp (BoolEq (FStar_Pervasives_Native.Some t), l, r) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.eq1_qn)) [(t, i); (l, e); (r, e)]
  | Comp (Lt, l, r) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.lt_qn)) [(l, e); (r, e)]
  | Comp (Le, l, r) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.lte_qn)) [(l, e); (r, e)]
  | Comp (Gt, l, r) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.gt_qn)) [(l, e); (r, e)]
  | Comp (Ge, l, r) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.gte_qn)) [(l, e); (r, e)]
  | And (p, q) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.and_qn)) [(p, e); (q, e)]
  | Or (p, q) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.or_qn)) [(p, e); (q, e)]
  | Implies (p, q) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.imp_qn)) [(p, e); (q, e)]
  | Not p ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.not_qn)) [(p, e)]
  | Iff (p, q) ->
      mk_app'
        (FStarC_Reflection_V1_Data.Tv_FVar
           (FStarC_Reflection_V1_Builtins.pack_fv
              FStar_Reflection_Const.iff_qn)) [(p, e); (q, e)]
  | Forall (b, sort, t) -> FStarC_Reflection_V1_Data.Tv_Unknown
  | Exists (b, sort, t) -> FStarC_Reflection_V1_Data.Tv_Unknown
  | App (p, q) ->
      FStarC_Reflection_V1_Data.Tv_App
        (p, (q, FStarC_Reflection_V1_Data.Q_Explicit))
  | Name b -> FStarC_Reflection_V1_Data.Tv_Var b
  | FV fv -> FStarC_Reflection_V1_Data.Tv_FVar fv
  | IntLit i1 ->
      FStarC_Reflection_V1_Data.Tv_Const (FStarC_Reflection_V1_Data.C_Int i1)
  | F_Unknown -> FStarC_Reflection_V1_Data.Tv_Unknown
let formula_as_term (f : formula) : FStarC_Reflection_Types.term=
  FStarC_Reflection_V1_Builtins.pack_ln (formula_as_term_view f)
let formula_to_string (uu___ : formula) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  (fun f ->
     match f with
     | True_ -> Obj.magic (Obj.repr (fun uu___ -> "True_"))
     | False_ -> Obj.magic (Obj.repr (fun uu___ -> "False_"))
     | Comp (Eq mt, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (match mt with
                        | FStar_Pervasives_Native.None ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ -> "")))
                        | FStar_Pervasives_Native.Some t ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Obj.magic
                                             (FStarC_Tactics_V1_Builtins.term_to_string
                                                t))
                                          (fun uu___ uu___1 ->
                                             Prims.strcat uu___ ")")))
                                    (fun uu___ uu___1 ->
                                       Prims.strcat " (" uu___))))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          l ps in
                                      let x3 =
                                        let x4 =
                                          let x5 =
                                            FStarC_Tactics_V1_Builtins.term_to_string
                                              r ps in
                                          Prims.strcat x5 ")" in
                                        Prims.strcat ") (" x4 in
                                      Prims.strcat x2 x3 in
                                    Prims.strcat " (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Eq" uu___)))
     | Comp (BoolEq mt, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (match mt with
                        | FStar_Pervasives_Native.None ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ -> "")))
                        | FStar_Pervasives_Native.Some t ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Obj.magic
                                             (FStarC_Tactics_V1_Builtins.term_to_string
                                                t))
                                          (fun uu___ uu___1 ->
                                             Prims.strcat uu___ ")")))
                                    (fun uu___ uu___1 ->
                                       Prims.strcat " (" uu___))))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          l ps in
                                      let x3 =
                                        let x4 =
                                          let x5 =
                                            FStarC_Tactics_V1_Builtins.term_to_string
                                              r ps in
                                          Prims.strcat x5 ")" in
                                        Prims.strcat ") (" x4 in
                                      Prims.strcat x2 x3 in
                                    Prims.strcat " (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "BoolEq" uu___)))
     | Comp (Lt, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string l))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          r ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Lt (" uu___)))
     | Comp (Le, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string l))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          r ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Le (" uu___)))
     | Comp (Gt, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string l))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          r ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Gt (" uu___)))
     | Comp (Ge, l, r) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string l))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          r ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Ge (" uu___)))
     | And (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "And (" uu___)))
     | Or (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Or (" uu___)))
     | Implies (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Implies (" uu___)))
     | Not p ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string p))
                       (fun uu___ uu___1 -> Prims.strcat uu___ ")")))
                 (fun uu___ uu___1 -> Prims.strcat "Not (" uu___)))
     | Iff (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "Iff (" uu___)))
     | Forall (bs, _sort, t) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string t))
                       (fun uu___ uu___1 -> Prims.strcat uu___ ")")))
                 (fun uu___ uu___1 -> Prims.strcat "Forall <bs> (" uu___)))
     | Exists (bs, _sort, t) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string t))
                       (fun uu___ uu___1 -> Prims.strcat uu___ ")")))
                 (fun uu___ uu___1 -> Prims.strcat "Exists <bs> (" uu___)))
     | App (p, q) ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic
                          (FStarC_Tactics_V1_Builtins.term_to_string p))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (fun ps ->
                                  let x =
                                    let x1 =
                                      let x2 =
                                        FStarC_Tactics_V1_Builtins.term_to_string
                                          q ps in
                                      Prims.strcat x2 ")" in
                                    Prims.strcat ") (" x1 in
                                  Prims.strcat uu___ x)) uu___)))
                 (fun uu___ uu___1 -> Prims.strcat "App (" uu___)))
     | Name bv ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Obj.magic (bv_to_string bv))
                       (fun uu___ uu___1 -> Prims.strcat uu___ ")")))
                 (fun uu___ uu___1 -> Prims.strcat "Name (" uu___)))
     | FV fv ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    Prims.strcat "FV ("
                      (Prims.strcat
                         (FStar_Reflection_V1_Derived.flatten_name
                            (FStarC_Reflection_V1_Builtins.inspect_fv fv))
                         ")"))))
     | IntLit i ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ -> Prims.strcat "Int " (Prims.string_of_int i))))
     | F_Unknown -> Obj.magic (Obj.repr (fun uu___ -> "?"))) uu___
