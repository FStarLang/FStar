open Prims
type var = FStar_Syntax_Syntax.bv
type sort = Prims.int
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStar_BigInt.t 
  | String of (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  
  | Char of FStar_Char.char 
  | Range of FStar_Range.range 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____36 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____43 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____57 -> false 
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____75 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____102 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____119 -> false
  
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee  -> match projectee with | Range _0 -> _0 
type atom =
  | Var of var 
  | Match of
  (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
              FStar_Syntax_Syntax.branch Prims.list)
  FStar_Pervasives_Native.tuple3 
and t =
  | Lam of
  (t Prims.list -> t,(t Prims.list ->
                        (t,FStar_Syntax_Syntax.aqual)
                          FStar_Pervasives_Native.tuple2)
                       Prims.list,Prims.int,(unit -> residual_comp)
                                              FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4 
  | Accu of
  (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
          Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Construct of
  (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple3 
  | FV of
  (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple3 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
  | Arrow of
  (t Prims.list -> comp,(t Prims.list ->
                           (t,FStar_Syntax_Syntax.aqual)
                             FStar_Pervasives_Native.tuple2)
                          Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Refinement of
  (t -> t,unit ->
            (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 
  | Quote of (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
  FStar_Pervasives_Native.tuple2 
  | Lazy of
  ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn,FStar_Syntax_Syntax.emb_typ)
                                   FStar_Pervasives_Native.tuple2)
     FStar_Util.either,t FStar_Common.thunk)
  FStar_Pervasives_Native.tuple2 
  | Rec of
  (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
  t Prims.list,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
                 Prims.list,Prims.int,Prims.bool Prims.list,t Prims.list ->
                                                              FStar_Syntax_Syntax.letbinding
                                                                -> t)
  FStar_Pervasives_Native.tuple7 
and comp =
  | Tot of (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | GTot of (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | Comp of comp_typ 
and comp_typ =
  {
  comp_univs: FStar_Syntax_Syntax.universes ;
  effect_name: FStar_Ident.lident ;
  result_typ: t ;
  effect_args:
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list ;
  flags: cflags Prims.list }
and cflags =
  | TOTAL 
  | MLEFFECT 
  | RETURN 
  | PARTIAL_RETURN 
  | SOMETRIVIAL 
  | TRIVIAL_POSTCONDITION 
  | SHOULD_NOT_INLINE 
  | LEMMA 
  | CPS 
  | DECREASES of t 
and residual_comp =
  {
  residual_effect: FStar_Ident.lident ;
  residual_typ: t FStar_Pervasives_Native.option ;
  residual_flags: cflags Prims.list }
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____488 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____519 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____613 -> false
  
let (__proj__Lam__item___0 :
  t ->
    (t Prims.list -> t,(t Prims.list ->
                          (t,FStar_Syntax_Syntax.aqual)
                            FStar_Pervasives_Native.tuple2)
                         Prims.list,Prims.int,(unit -> residual_comp)
                                                FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____724 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____782 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____852 -> false 
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____908 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____922 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____936 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____949 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____976 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (t Prims.list -> comp,(t Prims.list ->
                             (t,FStar_Syntax_Syntax.aqual)
                               FStar_Pervasives_Native.tuple2)
                            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1064 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1124 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1164 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn,FStar_Syntax_Syntax.emb_typ)
                                     FStar_Pervasives_Native.tuple2)
       FStar_Util.either,t FStar_Common.thunk)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1254 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list,(t,FStar_Syntax_Syntax.aqual)
                     FStar_Pervasives_Native.tuple2 Prims.list,Prims.int,
      Prims.bool Prims.list,t Prims.list ->
                              FStar_Syntax_Syntax.letbinding -> t)
      FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1376 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1414 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1446 -> false
  
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStar_Syntax_Syntax.universes) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__comp_univs
  
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_name
  
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__result_typ
  
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_args
  
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__flags
  
let (uu___is_TOTAL : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | TOTAL  -> true | uu____1565 -> false
  
let (uu___is_MLEFFECT : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1571 -> false
  
let (uu___is_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1577 -> false
  
let (uu___is_PARTIAL_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1583 -> false
  
let (uu___is_SOMETRIVIAL : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1589 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____1595 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____1601 -> false
  
let (uu___is_LEMMA : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1607 -> false
  
let (uu___is_CPS : cflags -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____1613 -> false 
let (uu___is_DECREASES : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1620 -> false
  
let (__proj__DECREASES__item___0 : cflags -> t) =
  fun projectee  -> match projectee with | DECREASES _0 -> _0 
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { residual_effect = __fname__residual_effect;
        residual_typ = __fname__residual_typ;
        residual_flags = __fname__residual_flags;_} ->
        __fname__residual_effect
  
let (__proj__Mkresidual_comp__item__residual_typ :
  residual_comp -> t FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { residual_effect = __fname__residual_effect;
        residual_typ = __fname__residual_typ;
        residual_flags = __fname__residual_flags;_} -> __fname__residual_typ
  
let (__proj__Mkresidual_comp__item__residual_flags :
  residual_comp -> cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { residual_effect = __fname__residual_effect;
        residual_typ = __fname__residual_typ;
        residual_flags = __fname__residual_flags;_} ->
        __fname__residual_flags
  
type arg = (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
type args =
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____1689 -> true | uu____1700 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1706,uu____1707) -> false | uu____1720 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> FV (i, us, ts) 
let (mkAccuVar : var -> t) = fun v1  -> Accu ((Var v1), []) 
let (mkAccuMatch :
  t ->
    (t -> t) ->
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)
        -> t)
  = fun s  -> fun cases  -> fun bs  -> Accu ((Match (s, cases, bs)), []) 
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___227_1849  ->
    if uu___227_1849
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___228_1855  ->
    if uu___228_1855
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.NotEqual
  
let (eq_inj :
  FStar_Syntax_Util.eq_result ->
    FStar_Syntax_Util.eq_result -> FStar_Syntax_Util.eq_result)
  =
  fun r1  ->
    fun r2  ->
      match (r1, r2) with
      | (FStar_Syntax_Util.Equal ,FStar_Syntax_Util.Equal ) ->
          FStar_Syntax_Util.Equal
      | (FStar_Syntax_Util.NotEqual ,uu____1867) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1868,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1869) -> FStar_Syntax_Util.Unknown
      | (uu____1870,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1886 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1902),String (s2,uu____1904)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1912,uu____1913) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1948,Lam uu____1949) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2036 = eq_atom a1 a2  in
          eq_and uu____2036 (fun uu____2038  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2077 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2077
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2088 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2145  ->
                        match uu____2145 with
                        | ((a1,uu____2159),(a2,uu____2161)) ->
                            let uu____2170 = eq_t a1 a2  in
                            eq_inj acc uu____2170) FStar_Syntax_Util.Equal)
                uu____2088))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2210 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2210
          then
            let uu____2211 =
              let uu____2212 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2212  in
            eq_and uu____2211 (fun uu____2214  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2220 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2220
      | (Univ u1,Univ u2) ->
          let uu____2223 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2223
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2269 =
            let uu____2270 =
              let uu____2271 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2271  in
            let uu____2276 =
              let uu____2277 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2277  in
            eq_t uu____2270 uu____2276  in
          eq_and uu____2269
            (fun uu____2285  ->
               let uu____2286 =
                 let uu____2287 = mkAccuVar x  in r1 uu____2287  in
               let uu____2288 =
                 let uu____2289 = mkAccuVar x  in r2 uu____2289  in
               eq_t uu____2286 uu____2288)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2290,uu____2291) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2296,uu____2297) -> FStar_Syntax_Util.Unknown

and (eq_arg : arg -> arg -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      eq_t (FStar_Pervasives_Native.fst a1) (FStar_Pervasives_Native.fst a2)

and (eq_args : args -> args -> FStar_Syntax_Util.eq_result) =
  fun as1  ->
    fun as2  ->
      match (as1, as2) with
      | ([],[]) -> FStar_Syntax_Util.Equal
      | (x::xs,y::ys) ->
          let uu____2378 = eq_arg x y  in
          eq_and uu____2378 (fun uu____2380  -> eq_args xs ys)
      | (uu____2381,uu____2382) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2418) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2420 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2420
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2441) ->
        let uu____2484 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2494 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2484 uu____2494
    | Accu (a,l) ->
        let uu____2509 =
          let uu____2510 = atom_to_string a  in
          let uu____2511 =
            let uu____2512 =
              let uu____2513 =
                let uu____2514 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2514  in
              Prims.strcat uu____2513 ")"  in
            Prims.strcat ") (" uu____2512  in
          Prims.strcat uu____2510 uu____2511  in
        Prims.strcat "Accu (" uu____2509
    | Construct (fv,us,l) ->
        let uu____2546 =
          let uu____2547 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2548 =
            let uu____2549 =
              let uu____2550 =
                let uu____2551 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2551  in
              let uu____2554 =
                let uu____2555 =
                  let uu____2556 =
                    let uu____2557 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2557  in
                  Prims.strcat uu____2556 "]"  in
                Prims.strcat "] [" uu____2555  in
              Prims.strcat uu____2550 uu____2554  in
            Prims.strcat ") [" uu____2549  in
          Prims.strcat uu____2547 uu____2548  in
        Prims.strcat "Construct (" uu____2546
    | FV (fv,us,l) ->
        let uu____2589 =
          let uu____2590 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2591 =
            let uu____2592 =
              let uu____2593 =
                let uu____2594 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2594  in
              let uu____2597 =
                let uu____2598 =
                  let uu____2599 =
                    let uu____2600 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2600  in
                  Prims.strcat uu____2599 "]"  in
                Prims.strcat "] [" uu____2598  in
              Prims.strcat uu____2593 uu____2597  in
            Prims.strcat ") [" uu____2592  in
          Prims.strcat uu____2590 uu____2591  in
        Prims.strcat "FV (" uu____2589
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2615 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2615
    | Type_t u ->
        let uu____2617 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2617
    | Arrow uu____2618 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2663 = t ()  in FStar_Pervasives_Native.fst uu____2663
           in
        let uu____2668 =
          let uu____2669 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2670 =
            let uu____2671 =
              let uu____2672 = t_to_string t1  in
              let uu____2673 =
                let uu____2674 =
                  let uu____2675 =
                    let uu____2676 =
                      let uu____2677 = mkAccuVar x1  in f uu____2677  in
                    t_to_string uu____2676  in
                  Prims.strcat uu____2675 "}"  in
                Prims.strcat "{" uu____2674  in
              Prims.strcat uu____2672 uu____2673  in
            Prims.strcat ":" uu____2671  in
          Prims.strcat uu____2669 uu____2670  in
        Prims.strcat "Refinement " uu____2668
    | Unknown  -> "Unknown"
    | Quote uu____2678 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____2684) ->
        let uu____2701 =
          let uu____2702 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____2702  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____2701
    | Lazy (FStar_Util.Inr (uu____2703,et),uu____2705) ->
        let uu____2722 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____2722
    | Rec
        (uu____2723,uu____2724,l,uu____2726,uu____2727,uu____2728,uu____2729)
        ->
        let uu____2770 =
          let uu____2771 =
            let uu____2772 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2772  in
          Prims.strcat uu____2771 ")"  in
        Prims.strcat "Rec (" uu____2770

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2777 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2777
    | Match (t,uu____2779,uu____2780) ->
        let uu____2803 = t_to_string t  in Prims.strcat "Match " uu____2803

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2805 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2805 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2811 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2811 (FStar_String.concat " ")

type nbe_cbs =
  {
  iapp: t -> args -> t ;
  translate: FStar_Syntax_Syntax.term -> t }
let (__proj__Mknbe_cbs__item__iapp : nbe_cbs -> t -> args -> t) =
  fun projectee  ->
    match projectee with
    | { iapp = __fname__iapp; translate = __fname__translate;_} ->
        __fname__iapp
  
let (__proj__Mknbe_cbs__item__translate :
  nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun projectee  ->
    match projectee with
    | { iapp = __fname__iapp; translate = __fname__translate;_} ->
        __fname__translate
  
let (iapp_cb : nbe_cbs -> t -> args -> t) = fun cbs  -> cbs.iapp 
let (translate_cb : nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun cbs  -> cbs.translate 
type 'a embedding =
  {
  em: nbe_cbs -> 'a -> t ;
  un: nbe_cbs -> t -> 'a FStar_Pervasives_Native.option ;
  typ: t ;
  emb_typ: FStar_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        emb_typ = __fname__emb_typ;_} -> __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        emb_typ = __fname__emb_typ;_} -> __fname__un
  
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        emb_typ = __fname__emb_typ;_} -> __fname__typ
  
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        emb_typ = __fname__emb_typ;_} -> __fname__emb_typ
  
let embed : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun e  -> fun cb  -> fun x  -> e.em cb x 
let unembed :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun e  -> fun cb  -> fun trm  -> e.un cb trm 
let type_of : 'a . 'a embedding -> t = fun e  -> e.typ 
let mk_emb :
  'a .
    (nbe_cbs -> 'a -> t) ->
      (nbe_cbs -> t -> 'a FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  =
  fun em  -> fun un  -> fun typ  -> fun et  -> { em; un; typ; emb_typ = et } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3260 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3260 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3280 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3280 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3318  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3333  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____3375 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____3375
         then
           let uu____3395 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3395
         else ());
        (let uu____3397 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____3397
         then f ()
         else
           (let thunk = FStar_Common.mk_thunk f  in
            let li = let uu____3426 = FStar_Dyn.mkdyn x  in (uu____3426, et)
               in
            Lazy ((FStar_Util.Inr li), thunk)))
  
let lazy_unembed :
  'Auu____3493 'a .
    'Auu____3493 ->
      FStar_Syntax_Syntax.emb_typ ->
        t ->
          (t -> 'a FStar_Pervasives_Native.option) ->
            'a FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun et  ->
      fun x  ->
        fun f  ->
          match x with
          | Lazy (FStar_Util.Inl li,thunk) ->
              let uu____3544 = FStar_Common.force_thunk thunk  in
              f uu____3544
          | Lazy (FStar_Util.Inr (b,et'),thunk) ->
              let uu____3604 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____3604
              then
                let res =
                  let uu____3629 = FStar_Common.force_thunk thunk  in
                  f uu____3629  in
                ((let uu____3671 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____3671
                  then
                    let uu____3691 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____3692 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____3691
                      uu____3692
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____3697 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____3697
                  then
                    let uu____3717 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____3717
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____3719 ->
              let aopt = f x  in
              ((let uu____3724 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____3724
                then
                  let uu____3744 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____3744
                else ());
               aopt)
  
let (mk_any_emb : t -> t embedding) =
  fun ty  ->
    let em _cb a = a  in
    let un _cb t = FStar_Pervasives_Native.Some t  in
    mk_emb em un ty FStar_Syntax_Syntax.ET_abstract
  
let (e_any : t embedding) =
  let em _cb a = a  in
  let un _cb t = FStar_Pervasives_Native.Some t  in
  let uu____3807 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____3807 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____3840 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____3845 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____3840 uu____3845 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____3877 -> FStar_Pervasives_Native.None  in
  let uu____3878 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____3883 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____3878 uu____3883 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____3923 -> FStar_Pervasives_Native.None  in
  let uu____3925 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____3930 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____3925 uu____3930 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____3964)) -> FStar_Pervasives_Native.Some s1
    | uu____3965 -> FStar_Pervasives_Native.None  in
  let uu____3966 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____3971 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____3966 uu____3971 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4003 -> FStar_Pervasives_Native.None  in
  let uu____4004 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4009 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4004 uu____4009 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4029 =
        let uu____4036 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4036, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4029  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4058  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4059 =
                 let uu____4060 =
                   let uu____4065 = type_of ea  in as_iarg uu____4065  in
                 [uu____4060]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4059
           | FStar_Pervasives_Native.Some x ->
               let uu____4075 =
                 let uu____4076 =
                   let uu____4081 = embed ea cb x  in as_arg uu____4081  in
                 let uu____4082 =
                   let uu____4089 =
                     let uu____4094 = type_of ea  in as_iarg uu____4094  in
                   [uu____4089]  in
                 uu____4076 :: uu____4082  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4075)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4161)::uu____4162::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4189 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4189
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4198 -> FStar_Pervasives_Native.None)
       in
    let uu____4201 =
      let uu____4202 =
        let uu____4203 = let uu____4208 = type_of ea  in as_arg uu____4208
           in
        [uu____4203]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4202
       in
    mk_emb em un uu____4201 etyp
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4254 =
          let uu____4261 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4261, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4254  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4289  ->
             let uu____4290 =
               let uu____4291 =
                 let uu____4296 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4296  in
               let uu____4297 =
                 let uu____4304 =
                   let uu____4309 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4309  in
                 let uu____4310 =
                   let uu____4317 =
                     let uu____4322 = type_of eb  in as_iarg uu____4322  in
                   let uu____4323 =
                     let uu____4330 =
                       let uu____4335 = type_of ea  in as_iarg uu____4335  in
                     [uu____4330]  in
                   uu____4317 :: uu____4323  in
                 uu____4304 :: uu____4310  in
               uu____4291 :: uu____4297  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4290)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____4403)::(a,uu____4405)::uu____4406::uu____4407::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____4446 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4446
                   (fun a1  ->
                      let uu____4456 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____4456
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____4469 -> FStar_Pervasives_Native.None)
         in
      let uu____4474 =
        let uu____4475 =
          let uu____4476 = let uu____4481 = type_of eb  in as_arg uu____4481
             in
          let uu____4482 =
            let uu____4489 =
              let uu____4494 = type_of ea  in as_arg uu____4494  in
            [uu____4489]  in
          uu____4476 :: uu____4482  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4475
         in
      mk_emb em un uu____4474 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4546 =
          let uu____4553 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4553, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4546  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____4582  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____4584 =
                   let uu____4585 =
                     let uu____4590 = embed ea cb a  in as_arg uu____4590  in
                   let uu____4591 =
                     let uu____4598 =
                       let uu____4603 = type_of eb  in as_iarg uu____4603  in
                     let uu____4604 =
                       let uu____4611 =
                         let uu____4616 = type_of ea  in as_iarg uu____4616
                          in
                       [uu____4611]  in
                     uu____4598 :: uu____4604  in
                   uu____4585 :: uu____4591  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4584
             | FStar_Util.Inr b ->
                 let uu____4634 =
                   let uu____4635 =
                     let uu____4640 = embed eb cb b  in as_arg uu____4640  in
                   let uu____4641 =
                     let uu____4648 =
                       let uu____4653 = type_of eb  in as_iarg uu____4653  in
                     let uu____4654 =
                       let uu____4661 =
                         let uu____4666 = type_of ea  in as_iarg uu____4666
                          in
                       [uu____4661]  in
                     uu____4648 :: uu____4654  in
                   uu____4635 :: uu____4641  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4634)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____4728)::uu____4729::uu____4730::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____4765 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4765
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____4781)::uu____4782::uu____4783::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____4818 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____4818
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____4831 -> FStar_Pervasives_Native.None)
         in
      let uu____4836 =
        let uu____4837 =
          let uu____4838 = let uu____4843 = type_of eb  in as_arg uu____4843
             in
          let uu____4844 =
            let uu____4851 =
              let uu____4856 = type_of ea  in as_arg uu____4856  in
            [uu____4851]  in
          uu____4838 :: uu____4844  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4837
         in
      mk_emb em un uu____4836 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____4904 -> FStar_Pervasives_Native.None  in
  let uu____4905 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____4910 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____4905 uu____4910 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____4930 =
        let uu____4937 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4937, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4930  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____4961  ->
           let typ = let uu____4963 = type_of ea  in as_iarg uu____4963  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____4984 =
               let uu____4985 = as_arg tl1  in
               let uu____4990 =
                 let uu____4997 =
                   let uu____5002 = embed ea cb hd1  in as_arg uu____5002  in
                 [uu____4997; typ]  in
               uu____4985 :: uu____4990  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____4984
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5050,uu____5051) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5071,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5074,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5075))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5102 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5102
                 (fun hd2  ->
                    let uu____5110 = un cb tl1  in
                    FStar_Util.bind_opt uu____5110
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5126,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5151 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5151
                 (fun hd2  ->
                    let uu____5159 = un cb tl1  in
                    FStar_Util.bind_opt uu____5159
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5174 -> FStar_Pervasives_Native.None)
       in
    let uu____5177 =
      let uu____5178 =
        let uu____5179 = let uu____5184 = type_of ea  in as_arg uu____5184
           in
        [uu____5179]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5178
       in
    mk_emb em un uu____5177 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5253  ->
             Lam
               ((fun tas  ->
                   let uu____5282 =
                     let uu____5285 = FStar_List.hd tas  in
                     unembed ea cb uu____5285  in
                   match uu____5282 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5287 = f a  in embed eb cb uu____5287
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____5299  ->
                     let uu____5302 = type_of eb  in as_arg uu____5302)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____5359 =
                 let uu____5362 =
                   let uu____5363 =
                     let uu____5364 =
                       let uu____5369 = embed ea cb x  in as_arg uu____5369
                        in
                     [uu____5364]  in
                   cb.iapp lam1 uu____5363  in
                 unembed eb cb uu____5362  in
               match uu____5359 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____5382 =
        let uu____5383 = type_of ea  in
        let uu____5384 = let uu____5385 = type_of eb  in as_iarg uu____5385
           in
        make_arrow1 uu____5383 uu____5384  in
      mk_emb em un uu____5382 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5402 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5402 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5407 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5407 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5412 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5412 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5417 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5417 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5422 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5422 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5427 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5427 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5432 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5432 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5437 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5437 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5442 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5442 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5450 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5451 =
          let uu____5452 =
            let uu____5457 =
              let uu____5458 = e_list e_string  in embed uu____5458 cb l  in
            as_arg uu____5457  in
          [uu____5452]  in
        mkFV uu____5450 [] uu____5451
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5476 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5477 =
          let uu____5478 =
            let uu____5483 =
              let uu____5484 = e_list e_string  in embed uu____5484 cb l  in
            as_arg uu____5483  in
          [uu____5478]  in
        mkFV uu____5476 [] uu____5477
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____5516,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____5532,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____5548,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____5564,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____5580,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____5596,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____5612,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____5628,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____5644,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____5660,(l,uu____5662)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____5681 =
          let uu____5686 = e_list e_string  in unembed uu____5686 cb l  in
        FStar_Util.bind_opt uu____5681
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____5702,(l,uu____5704)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____5723 =
          let uu____5728 = e_list e_string  in unembed uu____5728 cb l  in
        FStar_Util.bind_opt uu____5723
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____5743 ->
        ((let uu____5745 =
            let uu____5750 =
              let uu____5751 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____5751
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5750)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5745);
         FStar_Pervasives_Native.None)
     in
  let uu____5752 =
    let uu____5753 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____5753 [] []  in
  let uu____5758 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____5752 uu____5758 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____5766  -> failwith "bogus_cbs translate")
  } 
let (arg_as_int : arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_int bogus_cbs)
  
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_bool bogus_cbs)
  
let (arg_as_char : arg -> FStar_Char.char FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_char bogus_cbs)
  
let (arg_as_string : arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_string bogus_cbs)
  
let arg_as_list :
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e  ->
    fun a  ->
      let uu____5831 =
        let uu____5840 = e_list e  in unembed uu____5840 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5831
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____5861  ->
    match uu____5861 with
    | (a,uu____5869) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____5884)::[]) when
             let uu____5901 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5901 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____5906 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____5948 = let uu____5955 = as_arg c  in [uu____5955]  in
      int_to_t2 uu____5948
  
let lift_unary :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun aopts  ->
      match aopts with
      | (FStar_Pervasives_Native.Some a)::[] ->
          let uu____6008 = f a  in FStar_Pervasives_Native.Some uu____6008
      | uu____6009 -> FStar_Pervasives_Native.None
  
let lift_binary :
  'a 'b .
    ('a -> 'a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun aopts  ->
      match aopts with
      | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
          a1)::[] ->
          let uu____6062 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6062
      | uu____6063 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6106 = FStar_List.map as_a args  in lift_unary f uu____6106
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6160 = FStar_List.map as_a args  in
        lift_binary f uu____6160
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6189 = f x  in embed e_int bogus_cbs uu____6189)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____6215 = f x y  in embed e_int bogus_cbs uu____6215)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6234 = f x  in embed e_bool bogus_cbs uu____6234)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6260 = f x y  in embed e_bool bogus_cbs uu____6260)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____6286 = f x y  in embed e_string bogus_cbs uu____6286)
  
let mixed_binary_op :
  'a 'b 'c .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      (arg -> 'b FStar_Pervasives_Native.option) ->
        ('c -> t) ->
          ('a -> 'b -> 'c) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun as_b  ->
      fun embed_c  ->
        fun f  ->
          fun args  ->
            match args with
            | a::b::[] ->
                let uu____6388 =
                  let uu____6397 = as_a a  in
                  let uu____6400 = as_b b  in (uu____6397, uu____6400)  in
                (match uu____6388 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____6415 =
                       let uu____6416 = f a1 b1  in embed_c uu____6416  in
                     FStar_Pervasives_Native.Some uu____6415
                 | uu____6417 -> FStar_Pervasives_Native.None)
            | uu____6426 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____6432 = e_list e_char  in
    let uu____6439 = FStar_String.list_of_string s  in
    embed uu____6432 bogus_cbs uu____6439
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____6469 =
        let uu____6470 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____6470  in
      embed e_int bogus_cbs uu____6469
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6502 = arg_as_string a1  in
        (match uu____6502 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6508 = arg_as_list e_string a2  in
             (match uu____6508 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6521 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____6521
              | uu____6522 -> FStar_Pervasives_Native.None)
         | uu____6527 -> FStar_Pervasives_Native.None)
    | uu____6530 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____6536 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____6536
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cbs (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cbs true  in
      let fal = embed e_bool bogus_cbs false  in
      match args with
      | (_univ,uu____6562)::(_typ,uu____6564)::(a1,uu____6566)::(a2,uu____6568)::[]
          ->
          let uu____6589 = eq_t a1 a2  in
          (match uu____6589 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____6594 -> FStar_Pervasives_Native.None)
      | uu____6595 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____6608)::(_typ,uu____6610)::(a1,uu____6612)::(a2,uu____6614)::[]
        ->
        let uu____6635 = eq_t a1 a2  in
        (match uu____6635 with
         | FStar_Syntax_Util.Equal  ->
             let uu____6638 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____6638
         | FStar_Syntax_Util.NotEqual  ->
             let uu____6639 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____6639
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____6640 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____6657 =
        let uu____6658 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____6658  in
      failwith uu____6657
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____6671)::[] ->
        let uu____6680 = unembed e_range bogus_cbs a1  in
        (match uu____6680 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6686 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____6686
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6687 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6721 = arg_as_list e_char a1  in
        (match uu____6721 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6737 = arg_as_string a2  in
             (match uu____6737 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____6746 =
                    let uu____6747 = e_list e_string  in
                    embed uu____6747 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____6746
              | uu____6754 -> FStar_Pervasives_Native.None)
         | uu____6757 -> FStar_Pervasives_Native.None)
    | uu____6763 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____6804 =
          let uu____6817 = arg_as_string a1  in
          let uu____6820 = arg_as_int a2  in
          let uu____6823 = arg_as_int a3  in
          (uu____6817, uu____6820, uu____6823)  in
        (match uu____6804 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___230_6850  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____6854 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____6854) ()
              with | uu___229_6856 -> FStar_Pervasives_Native.None)
         | uu____6859 -> FStar_Pervasives_Native.None)
    | uu____6872 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6931 =
          let uu____6952 = arg_as_string fn  in
          let uu____6955 = arg_as_int from_line  in
          let uu____6958 = arg_as_int from_col  in
          let uu____6961 = arg_as_int to_line  in
          let uu____6964 = arg_as_int to_col  in
          (uu____6952, uu____6955, uu____6958, uu____6961, uu____6964)  in
        (match uu____6931 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6995 =
                 let uu____6996 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6997 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6996 uu____6997  in
               let uu____6998 =
                 let uu____6999 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7000 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6999 uu____7000  in
               FStar_Range.mk_range fn1 uu____6995 uu____6998  in
             let uu____7001 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7001
         | uu____7002 -> FStar_Pervasives_Native.None)
    | uu____7023 -> FStar_Pervasives_Native.None
  
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          Prims.int ->
            FStar_Ident.lid ->
              nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun f  ->
        fun n_tvars  ->
          fun _fv_lid  ->
            fun cb  ->
              let f_wrapped args =
                let uu____7110 = FStar_List.splitAt n_tvars args  in
                match uu____7110 with
                | (_tvar_args,rest_args) ->
                    let uu____7159 = FStar_List.hd rest_args  in
                    (match uu____7159 with
                     | (x,uu____7171) ->
                         let uu____7172 = unembed ea cb x  in
                         FStar_Util.map_opt uu____7172
                           (fun x1  ->
                              let uu____7178 = f x1  in
                              embed eb cb uu____7178))
                 in
              f_wrapped
  
let arrow_as_prim_step_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            Prims.int ->
              FStar_Ident.lid ->
                nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun f  ->
          fun n_tvars  ->
            fun _fv_lid  ->
              fun cb  ->
                let f_wrapped args =
                  let uu____7284 = FStar_List.splitAt n_tvars args  in
                  match uu____7284 with
                  | (_tvar_args,rest_args) ->
                      let uu____7333 = FStar_List.hd rest_args  in
                      (match uu____7333 with
                       | (x,uu____7345) ->
                           let uu____7346 =
                             let uu____7351 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7351  in
                           (match uu____7346 with
                            | (y,uu____7369) ->
                                let uu____7370 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____7370
                                  (fun x1  ->
                                     let uu____7376 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____7376
                                       (fun y1  ->
                                          let uu____7382 =
                                            let uu____7383 = f x1 y1  in
                                            embed ec cb uu____7383  in
                                          FStar_Pervasives_Native.Some
                                            uu____7382))))
                   in
                f_wrapped
  
let arrow_as_prim_step_3 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              Prims.int ->
                FStar_Ident.lid ->
                  nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun f  ->
            fun n_tvars  ->
              fun _fv_lid  ->
                fun cb  ->
                  let f_wrapped args =
                    let uu____7508 = FStar_List.splitAt n_tvars args  in
                    match uu____7508 with
                    | (_tvar_args,rest_args) ->
                        let uu____7557 = FStar_List.hd rest_args  in
                        (match uu____7557 with
                         | (x,uu____7569) ->
                             let uu____7570 =
                               let uu____7575 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7575  in
                             (match uu____7570 with
                              | (y,uu____7593) ->
                                  let uu____7594 =
                                    let uu____7599 =
                                      let uu____7606 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7606  in
                                    FStar_List.hd uu____7599  in
                                  (match uu____7594 with
                                   | (z,uu____7628) ->
                                       let uu____7629 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____7629
                                         (fun x1  ->
                                            let uu____7635 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____7635
                                              (fun y1  ->
                                                 let uu____7641 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____7641
                                                   (fun z1  ->
                                                      let uu____7647 =
                                                        let uu____7648 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____7648
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____7647))))))
                     in
                  f_wrapped
  