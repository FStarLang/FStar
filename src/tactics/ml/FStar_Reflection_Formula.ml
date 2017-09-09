open Prims
type comparison =
  | Eq
  | BoolEq
  | Lt
  | Le
let uu___is_Eq: comparison -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____7 -> false
let uu___is_BoolEq: comparison -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolEq  -> true | uu____14 -> false
let uu___is_Lt: comparison -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____21 -> false
let uu___is_Le: comparison -> Prims.bool =
  fun projectee  -> match projectee with | Le  -> true | uu____28 -> false
type formula =
  | True_
  | False_
  | Comp of comparison* FStar_Reflection_Types.typ*
  FStar_Reflection_Types.term* FStar_Reflection_Types.term
  | And of FStar_Reflection_Types.term* FStar_Reflection_Types.term
  | Or of FStar_Reflection_Types.term* FStar_Reflection_Types.term
  | Not of FStar_Reflection_Types.term
  | Implies of FStar_Reflection_Types.term* FStar_Reflection_Types.term
  | Iff of FStar_Reflection_Types.term* FStar_Reflection_Types.term
  | Forall of FStar_Reflection_Types.binder* FStar_Reflection_Types.term
  | Exists of FStar_Reflection_Types.binder* FStar_Reflection_Types.term
  | App of FStar_Reflection_Types.term* FStar_Reflection_Types.term
  | Name of FStar_Reflection_Types.binder
  | FV of FStar_Reflection_Types.fv
  | IntLit of Prims.int
  | F_Unknown
let uu___is_True_: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | True_  -> true | uu____123 -> false
let uu___is_False_: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | False_  -> true | uu____130 -> false
let uu___is_Comp: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Comp (_0,_1,_2,_3) -> true | uu____145 -> false
let __proj__Comp__item___0: formula -> comparison =
  fun projectee  -> match projectee with | Comp (_0,_1,_2,_3) -> _0
let __proj__Comp__item___1: formula -> FStar_Reflection_Types.typ =
  fun projectee  -> match projectee with | Comp (_0,_1,_2,_3) -> _1
let __proj__Comp__item___2: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Comp (_0,_1,_2,_3) -> _2
let __proj__Comp__item___3: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Comp (_0,_1,_2,_3) -> _3
let uu___is_And: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | And (_0,_1) -> true | uu____224 -> false
let __proj__And__item___0: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | And (_0,_1) -> _0
let __proj__And__item___1: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | And (_0,_1) -> _1
let uu___is_Or: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Or (_0,_1) -> true | uu____261 -> false
let __proj__Or__item___0: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Or (_0,_1) -> _0
let __proj__Or__item___1: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Or (_0,_1) -> _1
let uu___is_Not: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Not _0 -> true | uu____296 -> false
let __proj__Not__item___0: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Not _0 -> _0
let uu___is_Implies: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Implies (_0,_1) -> true | uu____318 -> false
let __proj__Implies__item___0: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Implies (_0,_1) -> _0
let __proj__Implies__item___1: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Implies (_0,_1) -> _1
let uu___is_Iff: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Iff (_0,_1) -> true | uu____355 -> false
let __proj__Iff__item___0: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Iff (_0,_1) -> _0
let __proj__Iff__item___1: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Iff (_0,_1) -> _1
let uu___is_Forall: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall (_0,_1) -> true | uu____392 -> false
let __proj__Forall__item___0: formula -> FStar_Reflection_Types.binder =
  fun projectee  -> match projectee with | Forall (_0,_1) -> _0
let __proj__Forall__item___1: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Forall (_0,_1) -> _1
let uu___is_Exists: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists (_0,_1) -> true | uu____429 -> false
let __proj__Exists__item___0: formula -> FStar_Reflection_Types.binder =
  fun projectee  -> match projectee with | Exists (_0,_1) -> _0
let __proj__Exists__item___1: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Exists (_0,_1) -> _1
let uu___is_App: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | App (_0,_1) -> true | uu____466 -> false
let __proj__App__item___0: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | App (_0,_1) -> _0
let __proj__App__item___1: formula -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | App (_0,_1) -> _1
let uu___is_Name: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____501 -> false
let __proj__Name__item___0: formula -> FStar_Reflection_Types.binder =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_FV: formula -> Prims.bool =
  fun projectee  -> match projectee with | FV _0 -> true | uu____521 -> false
let __proj__FV__item___0: formula -> FStar_Reflection_Types.fv =
  fun projectee  -> match projectee with | FV _0 -> _0
let uu___is_IntLit: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | IntLit _0 -> true | uu____541 -> false
let __proj__IntLit__item___0: formula -> Prims.int =
  fun projectee  -> match projectee with | IntLit _0 -> _0
let uu___is_F_Unknown: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | F_Unknown  -> true | uu____559 -> false
let mk_Forall:
  FStar_Reflection_Types.term -> FStar_Reflection_Types.term -> formula =
  fun typ  ->
    fun pred  ->
      Forall
        ((FStar_Reflection_Basic.fresh_binder typ),
          (FStar_Reflection_Basic.pack
             (FStar_Reflection_Data.Tv_App
                (pred,
                  ((FStar_Reflection_Basic.pack
                      (FStar_Reflection_Data.Tv_Var
                         (FStar_Reflection_Basic.fresh_binder typ))),
                    FStar_Reflection_Data.Q_Explicit)))))
let mk_Exists:
  FStar_Reflection_Types.term -> FStar_Reflection_Types.term -> formula =
  fun typ  ->
    fun pred  ->
      Exists
        ((FStar_Reflection_Basic.fresh_binder typ),
          (FStar_Reflection_Basic.pack
             (FStar_Reflection_Data.Tv_App
                (pred,
                  ((FStar_Reflection_Basic.pack
                      (FStar_Reflection_Data.Tv_Var
                         (FStar_Reflection_Basic.fresh_binder typ))),
                    FStar_Reflection_Data.Q_Explicit)))))
type ('Af,'At) smaller = Obj.t
let term_as_formula': FStar_Reflection_Types.term -> formula =
  fun t  ->
    match FStar_Reflection_Basic.inspect t with
    | FStar_Reflection_Data.Tv_Var n -> Name n
    | FStar_Reflection_Data.Tv_FVar fv ->
        if
          (FStar_Reflection_Basic.inspect_fv fv) =
            FStar_Reflection_Syntax.true_qn
        then True_
        else
          if
            (FStar_Reflection_Basic.inspect_fv fv) =
              FStar_Reflection_Syntax.false_qn
          then False_
          else FV fv
    | FStar_Reflection_Data.Tv_App (h0,t1) ->
        (match FStar_Reflection_Syntax.collect_app h0 with
         | (h,ts) ->
             (match ((FStar_Reflection_Basic.inspect h),
                      (FStar_List_Tot_Base.append ts [t1]))
              with
              | (FStar_Reflection_Data.Tv_FVar
                 fv,(a1,FStar_Reflection_Data.Q_Implicit )::(a2,FStar_Reflection_Data.Q_Explicit
                                                             )::(a3,FStar_Reflection_Data.Q_Explicit
                                                                 )::[])
                  ->
                  if
                    (FStar_Reflection_Basic.inspect_fv fv) =
                      FStar_Reflection_Syntax.eq2_qn
                  then Comp (Eq, a1, a2, a3)
                  else
                    if
                      (FStar_Reflection_Basic.inspect_fv fv) =
                        FStar_Reflection_Syntax.eq1_qn
                    then Comp (BoolEq, a1, a2, a3)
                    else
                      if
                        (FStar_Reflection_Basic.inspect_fv fv) =
                          FStar_Reflection_Syntax.lt_qn
                      then Comp (Lt, a1, a2, a3)
                      else
                        if
                          (FStar_Reflection_Basic.inspect_fv fv) =
                            FStar_Reflection_Syntax.lte_qn
                        then Comp (Le, a1, a2, a3)
                        else
                          if
                            (FStar_Reflection_Basic.inspect_fv fv) =
                              FStar_Reflection_Syntax.gt_qn
                          then Comp (Lt, a1, a3, a2)
                          else
                            if
                              (FStar_Reflection_Basic.inspect_fv fv) =
                                FStar_Reflection_Syntax.gte_qn
                            then Comp (Le, a1, a3, a2)
                            else App (h0, (FStar_Pervasives_Native.fst t1))
              | (FStar_Reflection_Data.Tv_FVar
                 fv,(a1,FStar_Reflection_Data.Q_Explicit )::(a2,FStar_Reflection_Data.Q_Explicit
                                                             )::[])
                  ->
                  if
                    (FStar_Reflection_Basic.inspect_fv fv) =
                      FStar_Reflection_Syntax.imp_qn
                  then Implies (a1, a2)
                  else
                    if
                      (FStar_Reflection_Basic.inspect_fv fv) =
                        FStar_Reflection_Syntax.and_qn
                    then And (a1, a2)
                    else
                      if
                        (FStar_Reflection_Basic.inspect_fv fv) =
                          FStar_Reflection_Syntax.iff_qn
                      then Iff (a1, a2)
                      else
                        if
                          (FStar_Reflection_Basic.inspect_fv fv) =
                            FStar_Reflection_Syntax.or_qn
                        then Or (a1, a2)
                        else App (h0, (FStar_Pervasives_Native.fst t1))
              | (FStar_Reflection_Data.Tv_FVar
                 fv,(a1,FStar_Reflection_Data.Q_Implicit )::(a2,FStar_Reflection_Data.Q_Explicit
                                                             )::[])
                  ->
                  if
                    (FStar_Reflection_Basic.inspect_fv fv) =
                      FStar_Reflection_Syntax.forall_qn
                  then mk_Forall a1 a2
                  else
                    if
                      (FStar_Reflection_Basic.inspect_fv fv) =
                        FStar_Reflection_Syntax.exists_qn
                    then mk_Exists a1 a2
                    else App (h0, (FStar_Pervasives_Native.fst t1))
              | (FStar_Reflection_Data.Tv_FVar
                 fv,(a,FStar_Reflection_Data.Q_Explicit )::[]) ->
                  if
                    (FStar_Reflection_Basic.inspect_fv fv) =
                      FStar_Reflection_Syntax.not_qn
                  then Not a
                  else App (h0, (FStar_Pervasives_Native.fst t1))
              | uu____847 -> App (h0, (FStar_Pervasives_Native.fst t1))))
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        if FStar_Reflection_Basic.is_free b t1
        then Forall (b, t1)
        else Implies ((FStar_Reflection_Basic.type_of_binder b), t1)
    | FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int i) ->
        IntLit i
    | FStar_Reflection_Data.Tv_Type uu____863 -> F_Unknown
    | FStar_Reflection_Data.Tv_Abs (uu____864,uu____865) -> F_Unknown
    | FStar_Reflection_Data.Tv_Refine (uu____866,uu____867) -> F_Unknown
    | FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Unit ) ->
        F_Unknown
    | uu____868 -> F_Unknown
let rec is_name_imp:
  FStar_Reflection_Types.name -> FStar_Reflection_Types.term -> Prims.bool =
  fun nm  ->
    fun t  ->
      match FStar_Reflection_Basic.inspect t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          if (FStar_Reflection_Basic.inspect_fv fv) = nm then true else false
      | FStar_Reflection_Data.Tv_App
          (l,(uu____887,FStar_Reflection_Data.Q_Implicit )) ->
          is_name_imp nm l
      | uu____888 -> false
let rec unsquash:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option
  =
  fun t  ->
    match FStar_Reflection_Basic.inspect t with
    | FStar_Reflection_Data.Tv_App (l,(r,FStar_Reflection_Data.Q_Explicit ))
        ->
        if is_name_imp FStar_Reflection_Syntax.squash_qn l
        then FStar_Pervasives_Native.Some r
        else FStar_Pervasives_Native.None
    | uu____907 -> FStar_Pervasives_Native.None
let rec term_as_formula: FStar_Reflection_Types.term -> formula =
  fun t  ->
    match unsquash t with
    | FStar_Pervasives_Native.None  -> F_Unknown
    | FStar_Pervasives_Native.Some t1 -> term_as_formula' t1
let formula_as_term_view: formula -> FStar_Reflection_Data.term_view =
  fun f  ->
    match f with
    | True_  ->
        FStar_Reflection_Data.Tv_FVar
          (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.true_qn)
    | False_  ->
        FStar_Reflection_Data.Tv_FVar
          (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.false_qn)
    | Comp (Eq ,t,l,r) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack tv), a))
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.eq2_qn))
          [(t, FStar_Reflection_Data.Q_Implicit);
          (l, FStar_Reflection_Data.Q_Explicit);
          (r, FStar_Reflection_Data.Q_Explicit)]
    | Comp (BoolEq ,t,l,r) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack tv), a))
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.eq1_qn))
          [(t, FStar_Reflection_Data.Q_Implicit);
          (l, FStar_Reflection_Data.Q_Explicit);
          (r, FStar_Reflection_Data.Q_Explicit)]
    | Comp (Lt ,t,l,r) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack tv), a))
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.lt_qn))
          [(t, FStar_Reflection_Data.Q_Implicit);
          (l, FStar_Reflection_Data.Q_Explicit);
          (r, FStar_Reflection_Data.Q_Explicit)]
    | Comp (Le ,t,l,r) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack tv), a))
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.lte_qn))
          [(t, FStar_Reflection_Data.Q_Implicit);
          (l, FStar_Reflection_Data.Q_Explicit);
          (r, FStar_Reflection_Data.Q_Explicit)]
    | And (p,q) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack tv), a))
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.and_qn))
          [(p, FStar_Reflection_Data.Q_Explicit);
          (q, FStar_Reflection_Data.Q_Explicit)]
    | Or (p,q) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack tv), a))
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.or_qn))
          [(p, FStar_Reflection_Data.Q_Explicit);
          (q, FStar_Reflection_Data.Q_Explicit)]
    | Implies (p,q) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack tv), a))
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.imp_qn))
          [(p, FStar_Reflection_Data.Q_Explicit);
          (q, FStar_Reflection_Data.Q_Explicit)]
    | Not p ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack tv), a))
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.not_qn))
          [(p, FStar_Reflection_Data.Q_Explicit)]
    | Iff (p,q) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Basic.pack tv), a))
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Basic.pack_fv FStar_Reflection_Syntax.iff_qn))
          [(p, FStar_Reflection_Data.Q_Explicit);
          (q, FStar_Reflection_Data.Q_Explicit)]
    | Forall (b,t) -> FStar_Reflection_Data.Tv_Unknown
    | Exists (b,t) -> FStar_Reflection_Data.Tv_Unknown
    | App (p,q) ->
        FStar_Reflection_Data.Tv_App
          (p, (q, FStar_Reflection_Data.Q_Explicit))
    | Name b -> FStar_Reflection_Data.Tv_Var b
    | FV fv -> FStar_Reflection_Data.Tv_FVar fv
    | IntLit i ->
        FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int i)
    | F_Unknown  -> FStar_Reflection_Data.Tv_Unknown
let formula_as_term: formula -> FStar_Reflection_Types.term =
  fun f  -> FStar_Reflection_Basic.pack (formula_as_term_view f)
let formula_to_string: formula -> Prims.string =
  fun f  ->
    match f with
    | True_  -> "True_"
    | False_  -> "False_"
    | Comp (Eq ,t,l,r) ->
        Prims.strcat "Eq ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string t)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Basic.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat (FStar_Reflection_Basic.term_to_string r)
                         ")")))))
    | Comp (BoolEq ,t,l,r) ->
        Prims.strcat "BoolEq ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string t)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Basic.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat (FStar_Reflection_Basic.term_to_string r)
                         ")")))))
    | Comp (Lt ,t,l,r) ->
        Prims.strcat "Lt ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string t)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Basic.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat (FStar_Reflection_Basic.term_to_string r)
                         ")")))))
    | Comp (Le ,t,l,r) ->
        Prims.strcat "Le ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string t)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Basic.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat (FStar_Reflection_Basic.term_to_string r)
                         ")")))))
    | And (p,q) ->
        Prims.strcat "And ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Basic.term_to_string q) ")")))
    | Or (p,q) ->
        Prims.strcat "Or ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Basic.term_to_string q) ")")))
    | Implies (p,q) ->
        Prims.strcat "Implies ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Basic.term_to_string q) ")")))
    | Not p ->
        Prims.strcat "Not ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string p) ")")
    | Iff (p,q) ->
        Prims.strcat "Iff ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Basic.term_to_string q) ")")))
    | Forall (bs,t) ->
        Prims.strcat "Forall <bs> ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string t) ")")
    | Exists (bs,t) ->
        Prims.strcat "Exists <bs> ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string t) ")")
    | App (p,q) ->
        Prims.strcat "App ("
          (Prims.strcat (FStar_Reflection_Basic.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Basic.term_to_string q) ")")))
    | Name b ->
        Prims.strcat "Name ("
          (Prims.strcat (FStar_Reflection_Basic.inspect_bv b) ")")
    | FV fv ->
        Prims.strcat "FV ("
          (Prims.strcat
             (FStar_Reflection_Syntax.flatten_name
                (FStar_Reflection_Basic.inspect_fv fv)) ")")
    | IntLit i -> Prims.strcat "Int " (Prims.string_of_int i)
    | F_Unknown  -> "?"