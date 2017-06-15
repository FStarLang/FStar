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
  | Comp of comparison* FStar_Reflection_Syntax.typ*
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
let __proj__Comp__item___1: formula -> FStar_Reflection_Syntax.typ =
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
        ((FStar_Reflection_Syntax.fresh_binder typ),
          (FStar_Reflection_Syntax.pack
             (FStar_Reflection_Syntax.Tv_App
                (pred,
                  (FStar_Reflection_Syntax.pack
                     (FStar_Reflection_Syntax.Tv_Var
                        (FStar_Reflection_Syntax.fresh_binder typ)))))))
type ('Af,'At) smaller = Obj.t
let term_as_formula': FStar_Reflection_Types.term -> formula =
  fun t  ->
    match FStar_Reflection_Syntax.inspect t with
    | FStar_Reflection_Syntax.Tv_Var n -> Name n
    | FStar_Reflection_Syntax.Tv_FVar fv ->
        if
          (FStar_Reflection_Syntax.inspect_fv fv) =
            FStar_Reflection_Syntax.true_qn
        then True_
        else
          if
            (FStar_Reflection_Syntax.inspect_fv fv) =
              FStar_Reflection_Syntax.false_qn
          then False_
          else FV fv
    | FStar_Reflection_Syntax.Tv_App (h0,t1) ->
        (match FStar_Reflection_Syntax.collect_app h0 with
         | (h,ts) ->
             (match ((FStar_Reflection_Syntax.inspect h),
                      (FStar_List_Tot_Base.append ts [t1]))
              with
              | (FStar_Reflection_Syntax.Tv_FVar fv,a1::a2::a3::[]) ->
                  if
                    (FStar_Reflection_Syntax.inspect_fv fv) =
                      FStar_Reflection_Syntax.eq2_qn
                  then Comp (Eq, a1, a2, a3)
                  else
                    if
                      (FStar_Reflection_Syntax.inspect_fv fv) =
                        FStar_Reflection_Syntax.eq1_qn
                    then Comp (BoolEq, a1, a2, a3)
                    else
                      if
                        (FStar_Reflection_Syntax.inspect_fv fv) =
                          FStar_Reflection_Syntax.lt_qn
                      then Comp (Lt, a1, a2, a3)
                      else
                        if
                          (FStar_Reflection_Syntax.inspect_fv fv) =
                            FStar_Reflection_Syntax.lte_qn
                        then Comp (Le, a1, a2, a3)
                        else
                          if
                            (FStar_Reflection_Syntax.inspect_fv fv) =
                              FStar_Reflection_Syntax.gt_qn
                          then Comp (Lt, a1, a3, a2)
                          else
                            if
                              (FStar_Reflection_Syntax.inspect_fv fv) =
                                FStar_Reflection_Syntax.gte_qn
                            then Comp (Le, a1, a3, a2)
                            else App (h0, t1)
              | (FStar_Reflection_Syntax.Tv_FVar fv,a1::a2::[]) ->
                  if
                    (FStar_Reflection_Syntax.inspect_fv fv) =
                      FStar_Reflection_Syntax.imp_qn
                  then Implies (a1, a2)
                  else
                    if
                      (FStar_Reflection_Syntax.inspect_fv fv) =
                        FStar_Reflection_Syntax.and_qn
                    then And (a1, a2)
                    else
                      if
                        (FStar_Reflection_Syntax.inspect_fv fv) =
                          FStar_Reflection_Syntax.or_qn
                      then Or (a1, a2)
                      else
                        if
                          (FStar_Reflection_Syntax.inspect_fv fv) =
                            FStar_Reflection_Syntax.forall_qn
                        then mk_Forall a1 a2
                        else App (h0, t1)
              | (FStar_Reflection_Syntax.Tv_FVar fv,a::[]) ->
                  if
                    (FStar_Reflection_Syntax.inspect_fv fv) =
                      FStar_Reflection_Syntax.not_qn
                  then Not a
                  else App (h0, t1)
              | uu____741 -> App (h0, t1)))
    | FStar_Reflection_Syntax.Tv_Arrow (b,t1) ->
        if FStar_Reflection_Syntax.is_free b t1
        then Forall (b, t1)
        else Implies ((FStar_Reflection_Syntax.type_of_binder b), t1)
    | FStar_Reflection_Syntax.Tv_Const (FStar_Reflection_Syntax.C_Int i) ->
        IntLit i
    | FStar_Reflection_Syntax.Tv_Type uu____750 -> F_Unknown
    | FStar_Reflection_Syntax.Tv_Abs (uu____751,uu____752) -> F_Unknown
    | FStar_Reflection_Syntax.Tv_Refine (uu____753,uu____754) -> F_Unknown
    | FStar_Reflection_Syntax.Tv_Const (FStar_Reflection_Syntax.C_Unit ) ->
        F_Unknown
    | uu____755 -> F_Unknown
let rec term_as_formula: FStar_Reflection_Types.term -> formula =
  fun t  ->
    match FStar_Reflection_Syntax.inspect t with
    | FStar_Reflection_Syntax.Tv_App (l,r) ->
        (match FStar_Reflection_Syntax.inspect l with
         | FStar_Reflection_Syntax.Tv_FVar fv ->
             if
               (FStar_Reflection_Syntax.inspect_fv fv) =
                 FStar_Reflection_Syntax.squash_qn
             then term_as_formula' r
             else F_Unknown
         | uu____781 -> F_Unknown)
    | uu____782 -> F_Unknown
let formula_as_term_view: formula -> FStar_Reflection_Syntax.term_view =
  fun f  ->
    match f with
    | True_  ->
        FStar_Reflection_Syntax.Tv_FVar
          (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.true_qn)
    | False_  ->
        FStar_Reflection_Syntax.Tv_FVar
          (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.false_qn)
    | Comp (Eq ,t,l,r) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Syntax.Tv_App
                 ((FStar_Reflection_Syntax.pack tv), a))
          (FStar_Reflection_Syntax.Tv_FVar
             (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.eq2_qn))
          [t; l; r]
    | Comp (BoolEq ,t,l,r) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Syntax.Tv_App
                 ((FStar_Reflection_Syntax.pack tv), a))
          (FStar_Reflection_Syntax.Tv_FVar
             (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.eq1_qn))
          [t; l; r]
    | Comp (Lt ,t,l,r) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Syntax.Tv_App
                 ((FStar_Reflection_Syntax.pack tv), a))
          (FStar_Reflection_Syntax.Tv_FVar
             (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.lt_qn))
          [t; l; r]
    | Comp (Le ,t,l,r) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Syntax.Tv_App
                 ((FStar_Reflection_Syntax.pack tv), a))
          (FStar_Reflection_Syntax.Tv_FVar
             (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.lte_qn))
          [t; l; r]
    | And (p,q) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Syntax.Tv_App
                 ((FStar_Reflection_Syntax.pack tv), a))
          (FStar_Reflection_Syntax.Tv_FVar
             (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.and_qn))
          [p; q]
    | Or (p,q) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Syntax.Tv_App
                 ((FStar_Reflection_Syntax.pack tv), a))
          (FStar_Reflection_Syntax.Tv_FVar
             (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.or_qn))
          [p; q]
    | Implies (p,q) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Syntax.Tv_App
                 ((FStar_Reflection_Syntax.pack tv), a))
          (FStar_Reflection_Syntax.Tv_FVar
             (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.imp_qn))
          [p; q]
    | Not p ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Syntax.Tv_App
                 ((FStar_Reflection_Syntax.pack tv), a))
          (FStar_Reflection_Syntax.Tv_FVar
             (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.not_qn))
          [p]
    | Iff (p,q) ->
        FStar_List_Tot_Base.fold_left
          (fun tv  ->
             fun a  ->
               FStar_Reflection_Syntax.Tv_App
                 ((FStar_Reflection_Syntax.pack tv), a))
          (FStar_Reflection_Syntax.Tv_FVar
             (FStar_Reflection_Syntax.pack_fv FStar_Reflection_Syntax.iff_qn))
          [p; q]
    | Forall (b,t) -> FStar_Reflection_Syntax.Tv_Unknown
    | Exists (b,t) -> FStar_Reflection_Syntax.Tv_Unknown
    | App (p,q) -> FStar_Reflection_Syntax.Tv_App (p, q)
    | Name b -> FStar_Reflection_Syntax.Tv_Var b
    | FV fv -> FStar_Reflection_Syntax.Tv_FVar fv
    | IntLit i ->
        FStar_Reflection_Syntax.Tv_Const (FStar_Reflection_Syntax.C_Int i)
    | F_Unknown  -> FStar_Reflection_Syntax.Tv_Unknown
let formula_as_term: formula -> FStar_Reflection_Types.term =
  fun f  -> FStar_Reflection_Syntax.pack (formula_as_term_view f)
let formula_to_string: formula -> Prims.string =
  fun f  ->
    match f with
    | True_  -> "True_"
    | False_  -> "False_"
    | Comp (Eq ,t,l,r) ->
        Prims.strcat "Eq ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string t)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Syntax.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat
                         (FStar_Reflection_Syntax.term_to_string r) ")")))))
    | Comp (BoolEq ,t,l,r) ->
        Prims.strcat "BoolEq ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string t)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Syntax.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat
                         (FStar_Reflection_Syntax.term_to_string r) ")")))))
    | Comp (Lt ,t,l,r) ->
        Prims.strcat "Lt ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string t)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Syntax.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat
                         (FStar_Reflection_Syntax.term_to_string r) ")")))))
    | Comp (Le ,t,l,r) ->
        Prims.strcat "Le ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string t)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Syntax.term_to_string l)
                   (Prims.strcat ") ("
                      (Prims.strcat
                         (FStar_Reflection_Syntax.term_to_string r) ")")))))
    | And (p,q) ->
        Prims.strcat "And ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Syntax.term_to_string q) ")")))
    | Or (p,q) ->
        Prims.strcat "Or ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Syntax.term_to_string q) ")")))
    | Implies (p,q) ->
        Prims.strcat "Implies ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Syntax.term_to_string q) ")")))
    | Not p ->
        Prims.strcat "Not ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string p) ")")
    | Iff (p,q) ->
        Prims.strcat "Iff ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Syntax.term_to_string q) ")")))
    | Forall (bs,t) ->
        Prims.strcat "Forall <bs> ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string t) ")")
    | Exists (bs,t) ->
        Prims.strcat "Exists <bs> ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string t) ")")
    | App (p,q) ->
        Prims.strcat "App ("
          (Prims.strcat (FStar_Reflection_Syntax.term_to_string p)
             (Prims.strcat ") ("
                (Prims.strcat (FStar_Reflection_Syntax.term_to_string q) ")")))
    | Name b ->
        Prims.strcat "Name ("
          (Prims.strcat (FStar_Reflection_Syntax.inspect_bv b) ")")
    | FV fv ->
        Prims.strcat "FV ("
          (Prims.strcat
             (FStar_Reflection_Syntax.flatten_name
                (FStar_Reflection_Syntax.inspect_fv fv)) ")")
    | IntLit i -> Prims.strcat "Int " (Prims.string_of_int i)
    | F_Unknown  -> "?"