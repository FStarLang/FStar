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
  | Reflect of t 
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
    match projectee with | Var _0 -> true | uu____496 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____527 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____621 -> false
  
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
    match projectee with | Accu _0 -> true | uu____732 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____790 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____860 -> false 
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
    match projectee with | Constant _0 -> true | uu____916 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____930 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____944 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____957 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____984 -> false
  
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
    match projectee with | Refinement _0 -> true | uu____1072 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1128 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1146 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1186 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn,FStar_Syntax_Syntax.emb_typ)
                                     FStar_Pervasives_Native.tuple2)
       FStar_Util.either,t FStar_Common.thunk)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1276 -> false
  
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
    match projectee with | Tot _0 -> true | uu____1398 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1436 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1468 -> false
  
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
    match projectee with | TOTAL  -> true | uu____1587 -> false
  
let (uu___is_MLEFFECT : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1593 -> false
  
let (uu___is_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1599 -> false
  
let (uu___is_PARTIAL_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1605 -> false
  
let (uu___is_SOMETRIVIAL : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1611 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____1617 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____1623 -> false
  
let (uu___is_LEMMA : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1629 -> false
  
let (uu___is_CPS : cflags -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____1635 -> false 
let (uu___is_DECREASES : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1642 -> false
  
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
  fun trm  -> match trm with | Accu uu____1711 -> true | uu____1722 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1728,uu____1729) -> false | uu____1742 -> true
  
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
  fun uu___229_1871  ->
    if uu___229_1871
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___230_1877  ->
    if uu___230_1877
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
      | (FStar_Syntax_Util.NotEqual ,uu____1889) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1890,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1891) -> FStar_Syntax_Util.Unknown
      | (uu____1892,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1908 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1924),String (s2,uu____1926)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1934,uu____1935) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1970,Lam uu____1971) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2058 = eq_atom a1 a2  in
          eq_and uu____2058 (fun uu____2060  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2099 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2099
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2110 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2167  ->
                        match uu____2167 with
                        | ((a1,uu____2181),(a2,uu____2183)) ->
                            let uu____2192 = eq_t a1 a2  in
                            eq_inj acc uu____2192) FStar_Syntax_Util.Equal)
                uu____2110))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2232 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2232
          then
            let uu____2233 =
              let uu____2234 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2234  in
            eq_and uu____2233 (fun uu____2236  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2242 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2242
      | (Univ u1,Univ u2) ->
          let uu____2245 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2245
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2291 =
            let uu____2292 =
              let uu____2293 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2293  in
            let uu____2298 =
              let uu____2299 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2299  in
            eq_t uu____2292 uu____2298  in
          eq_and uu____2291
            (fun uu____2307  ->
               let uu____2308 =
                 let uu____2309 = mkAccuVar x  in r1 uu____2309  in
               let uu____2310 =
                 let uu____2311 = mkAccuVar x  in r2 uu____2311  in
               eq_t uu____2308 uu____2310)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2312,uu____2313) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2318,uu____2319) -> FStar_Syntax_Util.Unknown

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
          let uu____2400 = eq_arg x y  in
          eq_and uu____2400 (fun uu____2402  -> eq_args xs ys)
      | (uu____2403,uu____2404) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2440) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2442 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2442
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2463) ->
        let uu____2506 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2516 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2506 uu____2516
    | Accu (a,l) ->
        let uu____2531 =
          let uu____2532 = atom_to_string a  in
          let uu____2533 =
            let uu____2534 =
              let uu____2535 =
                let uu____2536 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2536  in
              Prims.strcat uu____2535 ")"  in
            Prims.strcat ") (" uu____2534  in
          Prims.strcat uu____2532 uu____2533  in
        Prims.strcat "Accu (" uu____2531
    | Construct (fv,us,l) ->
        let uu____2568 =
          let uu____2569 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2570 =
            let uu____2571 =
              let uu____2572 =
                let uu____2573 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2573  in
              let uu____2576 =
                let uu____2577 =
                  let uu____2578 =
                    let uu____2579 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2579  in
                  Prims.strcat uu____2578 "]"  in
                Prims.strcat "] [" uu____2577  in
              Prims.strcat uu____2572 uu____2576  in
            Prims.strcat ") [" uu____2571  in
          Prims.strcat uu____2569 uu____2570  in
        Prims.strcat "Construct (" uu____2568
    | FV (fv,us,l) ->
        let uu____2611 =
          let uu____2612 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2613 =
            let uu____2614 =
              let uu____2615 =
                let uu____2616 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2616  in
              let uu____2619 =
                let uu____2620 =
                  let uu____2621 =
                    let uu____2622 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2622  in
                  Prims.strcat uu____2621 "]"  in
                Prims.strcat "] [" uu____2620  in
              Prims.strcat uu____2615 uu____2619  in
            Prims.strcat ") [" uu____2614  in
          Prims.strcat uu____2612 uu____2613  in
        Prims.strcat "FV (" uu____2611
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2637 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2637
    | Type_t u ->
        let uu____2639 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2639
    | Arrow uu____2640 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2685 = t ()  in FStar_Pervasives_Native.fst uu____2685
           in
        let uu____2690 =
          let uu____2691 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2692 =
            let uu____2693 =
              let uu____2694 = t_to_string t1  in
              let uu____2695 =
                let uu____2696 =
                  let uu____2697 =
                    let uu____2698 =
                      let uu____2699 = mkAccuVar x1  in f uu____2699  in
                    t_to_string uu____2698  in
                  Prims.strcat uu____2697 "}"  in
                Prims.strcat "{" uu____2696  in
              Prims.strcat uu____2694 uu____2695  in
            Prims.strcat ":" uu____2693  in
          Prims.strcat uu____2691 uu____2692  in
        Prims.strcat "Refinement " uu____2690
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____2701 = t_to_string t  in Prims.strcat "Reflect " uu____2701
    | Quote uu____2702 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____2708) ->
        let uu____2725 =
          let uu____2726 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____2726  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____2725
    | Lazy (FStar_Util.Inr (uu____2727,et),uu____2729) ->
        let uu____2746 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____2746
    | Rec
        (uu____2747,uu____2748,l,uu____2750,uu____2751,uu____2752,uu____2753)
        ->
        let uu____2794 =
          let uu____2795 =
            let uu____2796 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2796  in
          Prims.strcat uu____2795 ")"  in
        Prims.strcat "Rec (" uu____2794

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2801 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2801
    | Match (t,uu____2803,uu____2804) ->
        let uu____2827 = t_to_string t  in Prims.strcat "Match " uu____2827

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2829 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2829 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2835 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2835 (FStar_String.concat " ")

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
  
let (iapp_cb : nbe_cbs -> t -> args -> t) =
  fun cbs  -> fun h  -> fun a  -> cbs.iapp h a 
let (translate_cb : nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun cbs  -> fun t  -> cbs.translate t 
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
        let uu____3287 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3287 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3307 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3307 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3345  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3360  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____3402 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____3402
         then
           let uu____3422 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3422
         else ());
        (let uu____3424 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____3424
         then f ()
         else
           (let thunk = FStar_Common.mk_thunk f  in
            let li = let uu____3453 = FStar_Dyn.mkdyn x  in (uu____3453, et)
               in
            Lazy ((FStar_Util.Inr li), thunk)))
  
let lazy_unembed :
  'Auu____3520 'a .
    'Auu____3520 ->
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
              let uu____3571 = FStar_Common.force_thunk thunk  in
              f uu____3571
          | Lazy (FStar_Util.Inr (b,et'),thunk) ->
              let uu____3631 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____3631
              then
                let res =
                  let uu____3656 = FStar_Common.force_thunk thunk  in
                  f uu____3656  in
                ((let uu____3698 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____3698
                  then
                    let uu____3718 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____3719 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____3718
                      uu____3719
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____3724 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____3724
                  then
                    let uu____3744 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____3744
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____3746 ->
              let aopt = f x  in
              ((let uu____3751 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____3751
                then
                  let uu____3771 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____3771
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
  let uu____3834 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____3834 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____3867 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____3872 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____3867 uu____3872 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____3904 -> FStar_Pervasives_Native.None  in
  let uu____3905 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____3910 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____3905 uu____3910 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____3950 -> FStar_Pervasives_Native.None  in
  let uu____3952 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____3957 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____3952 uu____3957 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____3991)) -> FStar_Pervasives_Native.Some s1
    | uu____3992 -> FStar_Pervasives_Native.None  in
  let uu____3993 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____3998 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____3993 uu____3998 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4030 -> FStar_Pervasives_Native.None  in
  let uu____4031 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4036 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4031 uu____4036 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4056 =
        let uu____4063 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4063, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4056  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4085  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4086 =
                 let uu____4087 =
                   let uu____4092 = type_of ea  in as_iarg uu____4092  in
                 [uu____4087]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4086
           | FStar_Pervasives_Native.Some x ->
               let uu____4102 =
                 let uu____4103 =
                   let uu____4108 = embed ea cb x  in as_arg uu____4108  in
                 let uu____4109 =
                   let uu____4116 =
                     let uu____4121 = type_of ea  in as_iarg uu____4121  in
                   [uu____4116]  in
                 uu____4103 :: uu____4109  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4102)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4188)::uu____4189::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4216 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4216
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4225 -> FStar_Pervasives_Native.None)
       in
    let uu____4228 =
      let uu____4229 =
        let uu____4230 = let uu____4235 = type_of ea  in as_arg uu____4235
           in
        [uu____4230]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4229
       in
    mk_emb em un uu____4228 etyp
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4281 =
          let uu____4288 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4288, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4281  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4316  ->
             let uu____4317 =
               let uu____4318 =
                 let uu____4323 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4323  in
               let uu____4324 =
                 let uu____4331 =
                   let uu____4336 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4336  in
                 let uu____4337 =
                   let uu____4344 =
                     let uu____4349 = type_of eb  in as_iarg uu____4349  in
                   let uu____4350 =
                     let uu____4357 =
                       let uu____4362 = type_of ea  in as_iarg uu____4362  in
                     [uu____4357]  in
                   uu____4344 :: uu____4350  in
                 uu____4331 :: uu____4337  in
               uu____4318 :: uu____4324  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4317)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____4430)::(a,uu____4432)::uu____4433::uu____4434::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____4473 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4473
                   (fun a1  ->
                      let uu____4483 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____4483
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____4496 -> FStar_Pervasives_Native.None)
         in
      let uu____4501 =
        let uu____4502 =
          let uu____4503 = let uu____4508 = type_of eb  in as_arg uu____4508
             in
          let uu____4509 =
            let uu____4516 =
              let uu____4521 = type_of ea  in as_arg uu____4521  in
            [uu____4516]  in
          uu____4503 :: uu____4509  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4502
         in
      mk_emb em un uu____4501 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4573 =
          let uu____4580 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4580, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4573  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____4609  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____4611 =
                   let uu____4612 =
                     let uu____4617 = embed ea cb a  in as_arg uu____4617  in
                   let uu____4618 =
                     let uu____4625 =
                       let uu____4630 = type_of eb  in as_iarg uu____4630  in
                     let uu____4631 =
                       let uu____4638 =
                         let uu____4643 = type_of ea  in as_iarg uu____4643
                          in
                       [uu____4638]  in
                     uu____4625 :: uu____4631  in
                   uu____4612 :: uu____4618  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4611
             | FStar_Util.Inr b ->
                 let uu____4661 =
                   let uu____4662 =
                     let uu____4667 = embed eb cb b  in as_arg uu____4667  in
                   let uu____4668 =
                     let uu____4675 =
                       let uu____4680 = type_of eb  in as_iarg uu____4680  in
                     let uu____4681 =
                       let uu____4688 =
                         let uu____4693 = type_of ea  in as_iarg uu____4693
                          in
                       [uu____4688]  in
                     uu____4675 :: uu____4681  in
                   uu____4662 :: uu____4668  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4661)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____4755)::uu____4756::uu____4757::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____4792 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4792
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____4808)::uu____4809::uu____4810::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____4845 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____4845
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____4858 -> FStar_Pervasives_Native.None)
         in
      let uu____4863 =
        let uu____4864 =
          let uu____4865 = let uu____4870 = type_of eb  in as_arg uu____4870
             in
          let uu____4871 =
            let uu____4878 =
              let uu____4883 = type_of ea  in as_arg uu____4883  in
            [uu____4878]  in
          uu____4865 :: uu____4871  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4864
         in
      mk_emb em un uu____4863 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____4931 -> FStar_Pervasives_Native.None  in
  let uu____4932 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____4937 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____4932 uu____4937 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____4957 =
        let uu____4964 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4964, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4957  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____4988  ->
           let typ = let uu____4990 = type_of ea  in as_iarg uu____4990  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5011 =
               let uu____5012 = as_arg tl1  in
               let uu____5017 =
                 let uu____5024 =
                   let uu____5029 = embed ea cb hd1  in as_arg uu____5029  in
                 [uu____5024; typ]  in
               uu____5012 :: uu____5017  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5011
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5077,uu____5078) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5098,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5101,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5102))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5129 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5129
                 (fun hd2  ->
                    let uu____5137 = un cb tl1  in
                    FStar_Util.bind_opt uu____5137
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5153,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5178 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5178
                 (fun hd2  ->
                    let uu____5186 = un cb tl1  in
                    FStar_Util.bind_opt uu____5186
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5201 -> FStar_Pervasives_Native.None)
       in
    let uu____5204 =
      let uu____5205 =
        let uu____5206 = let uu____5211 = type_of ea  in as_arg uu____5211
           in
        [uu____5206]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5205
       in
    mk_emb em un uu____5204 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5280  ->
             Lam
               ((fun tas  ->
                   let uu____5309 =
                     let uu____5312 = FStar_List.hd tas  in
                     unembed ea cb uu____5312  in
                   match uu____5309 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5314 = f a  in embed eb cb uu____5314
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____5326  ->
                     let uu____5329 = type_of eb  in as_arg uu____5329)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____5386 =
                 let uu____5389 =
                   let uu____5390 =
                     let uu____5391 =
                       let uu____5396 = embed ea cb x  in as_arg uu____5396
                        in
                     [uu____5391]  in
                   cb.iapp lam1 uu____5390  in
                 unembed eb cb uu____5389  in
               match uu____5386 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____5409 =
        let uu____5410 = type_of ea  in
        let uu____5411 = let uu____5412 = type_of eb  in as_iarg uu____5412
           in
        make_arrow1 uu____5410 uu____5411  in
      mk_emb em un uu____5409 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5429 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5429 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5434 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5434 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5439 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5439 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5444 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5444 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5449 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5449 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5454 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5454 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5459 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5459 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5464 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5464 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5469 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5469 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5477 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5478 =
          let uu____5479 =
            let uu____5484 =
              let uu____5485 = e_list e_string  in embed uu____5485 cb l  in
            as_arg uu____5484  in
          [uu____5479]  in
        mkFV uu____5477 [] uu____5478
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5503 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5504 =
          let uu____5505 =
            let uu____5510 =
              let uu____5511 = e_list e_string  in embed uu____5511 cb l  in
            as_arg uu____5510  in
          [uu____5505]  in
        mkFV uu____5503 [] uu____5504
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____5529 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5530 =
          let uu____5531 =
            let uu____5536 =
              let uu____5537 = e_list e_string  in embed uu____5537 cb l  in
            as_arg uu____5536  in
          [uu____5531]  in
        mkFV uu____5529 [] uu____5530
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____5568,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____5584,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____5600,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____5616,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____5632,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____5648,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____5664,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____5680,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____5696,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____5712,(l,uu____5714)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____5733 =
          let uu____5738 = e_list e_string  in unembed uu____5738 cb l  in
        FStar_Util.bind_opt uu____5733
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____5754,(l,uu____5756)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____5775 =
          let uu____5780 = e_list e_string  in unembed uu____5780 cb l  in
        FStar_Util.bind_opt uu____5775
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____5796,(l,uu____5798)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____5817 =
          let uu____5822 = e_list e_string  in unembed uu____5822 cb l  in
        FStar_Util.bind_opt uu____5817
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____5837 ->
        ((let uu____5839 =
            let uu____5844 =
              let uu____5845 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____5845
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5844)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5839);
         FStar_Pervasives_Native.None)
     in
  let uu____5846 =
    let uu____5847 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____5847 [] []  in
  let uu____5852 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____5846 uu____5852 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____5860  -> failwith "bogus_cbs translate")
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
      let uu____5925 =
        let uu____5934 = e_list e  in unembed uu____5934 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5925
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____5955  ->
    match uu____5955 with
    | (a,uu____5963) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____5978)::[]) when
             let uu____5995 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5995 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6000 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6042 = let uu____6049 = as_arg c  in [uu____6049]  in
      int_to_t2 uu____6042
  
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
          let uu____6102 = f a  in FStar_Pervasives_Native.Some uu____6102
      | uu____6103 -> FStar_Pervasives_Native.None
  
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
          let uu____6156 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6156
      | uu____6157 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6200 = FStar_List.map as_a args  in lift_unary f uu____6200
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6254 = FStar_List.map as_a args  in
        lift_binary f uu____6254
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6283 = f x  in embed e_int bogus_cbs uu____6283)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____6309 = f x y  in embed e_int bogus_cbs uu____6309)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6328 = f x  in embed e_bool bogus_cbs uu____6328)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6354 = f x y  in embed e_bool bogus_cbs uu____6354)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____6380 = f x y  in embed e_string bogus_cbs uu____6380)
  
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
                let uu____6482 =
                  let uu____6491 = as_a a  in
                  let uu____6494 = as_b b  in (uu____6491, uu____6494)  in
                (match uu____6482 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____6509 =
                       let uu____6510 = f a1 b1  in embed_c uu____6510  in
                     FStar_Pervasives_Native.Some uu____6509
                 | uu____6511 -> FStar_Pervasives_Native.None)
            | uu____6520 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____6526 = e_list e_char  in
    let uu____6533 = FStar_String.list_of_string s  in
    embed uu____6526 bogus_cbs uu____6533
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____6563 =
        let uu____6564 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____6564  in
      embed e_int bogus_cbs uu____6563
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6596 = arg_as_string a1  in
        (match uu____6596 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6602 = arg_as_list e_string a2  in
             (match uu____6602 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6615 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____6615
              | uu____6616 -> FStar_Pervasives_Native.None)
         | uu____6621 -> FStar_Pervasives_Native.None)
    | uu____6624 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____6630 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____6630
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cbs (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cbs true  in
      let fal = embed e_bool bogus_cbs false  in
      match args with
      | (_univ,uu____6656)::(_typ,uu____6658)::(a1,uu____6660)::(a2,uu____6662)::[]
          ->
          let uu____6683 = eq_t a1 a2  in
          (match uu____6683 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____6688 -> FStar_Pervasives_Native.None)
      | uu____6689 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____6702)::(_typ,uu____6704)::(a1,uu____6706)::(a2,uu____6708)::[]
        ->
        let uu____6729 = eq_t a1 a2  in
        (match uu____6729 with
         | FStar_Syntax_Util.Equal  ->
             let uu____6732 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____6732
         | FStar_Syntax_Util.NotEqual  ->
             let uu____6733 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____6733
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____6734 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____6751 =
        let uu____6752 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____6752  in
      failwith uu____6751
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____6765)::[] ->
        let uu____6774 = unembed e_range bogus_cbs a1  in
        (match uu____6774 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6780 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____6780
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6781 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6815 = arg_as_list e_char a1  in
        (match uu____6815 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6831 = arg_as_string a2  in
             (match uu____6831 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____6840 =
                    let uu____6841 = e_list e_string  in
                    embed uu____6841 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____6840
              | uu____6848 -> FStar_Pervasives_Native.None)
         | uu____6851 -> FStar_Pervasives_Native.None)
    | uu____6857 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____6898 =
          let uu____6911 = arg_as_string a1  in
          let uu____6914 = arg_as_int a2  in
          let uu____6917 = arg_as_int a3  in
          (uu____6911, uu____6914, uu____6917)  in
        (match uu____6898 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___232_6944  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____6948 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____6948) ()
              with | uu___231_6950 -> FStar_Pervasives_Native.None)
         | uu____6953 -> FStar_Pervasives_Native.None)
    | uu____6966 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7025 =
          let uu____7046 = arg_as_string fn  in
          let uu____7049 = arg_as_int from_line  in
          let uu____7052 = arg_as_int from_col  in
          let uu____7055 = arg_as_int to_line  in
          let uu____7058 = arg_as_int to_col  in
          (uu____7046, uu____7049, uu____7052, uu____7055, uu____7058)  in
        (match uu____7025 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7089 =
                 let uu____7090 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7091 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7090 uu____7091  in
               let uu____7092 =
                 let uu____7093 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7094 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7093 uu____7094  in
               FStar_Range.mk_range fn1 uu____7089 uu____7092  in
             let uu____7095 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7095
         | uu____7096 -> FStar_Pervasives_Native.None)
    | uu____7117 -> FStar_Pervasives_Native.None
  
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
                let uu____7204 = FStar_List.splitAt n_tvars args  in
                match uu____7204 with
                | (_tvar_args,rest_args) ->
                    let uu____7253 = FStar_List.hd rest_args  in
                    (match uu____7253 with
                     | (x,uu____7265) ->
                         let uu____7266 = unembed ea cb x  in
                         FStar_Util.map_opt uu____7266
                           (fun x1  ->
                              let uu____7272 = f x1  in
                              embed eb cb uu____7272))
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
                  let uu____7378 = FStar_List.splitAt n_tvars args  in
                  match uu____7378 with
                  | (_tvar_args,rest_args) ->
                      let uu____7427 = FStar_List.hd rest_args  in
                      (match uu____7427 with
                       | (x,uu____7439) ->
                           let uu____7440 =
                             let uu____7445 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7445  in
                           (match uu____7440 with
                            | (y,uu____7463) ->
                                let uu____7464 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____7464
                                  (fun x1  ->
                                     let uu____7470 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____7470
                                       (fun y1  ->
                                          let uu____7476 =
                                            let uu____7477 = f x1 y1  in
                                            embed ec cb uu____7477  in
                                          FStar_Pervasives_Native.Some
                                            uu____7476))))
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
                    let uu____7602 = FStar_List.splitAt n_tvars args  in
                    match uu____7602 with
                    | (_tvar_args,rest_args) ->
                        let uu____7651 = FStar_List.hd rest_args  in
                        (match uu____7651 with
                         | (x,uu____7663) ->
                             let uu____7664 =
                               let uu____7669 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7669  in
                             (match uu____7664 with
                              | (y,uu____7687) ->
                                  let uu____7688 =
                                    let uu____7693 =
                                      let uu____7700 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7700  in
                                    FStar_List.hd uu____7693  in
                                  (match uu____7688 with
                                   | (z,uu____7722) ->
                                       let uu____7723 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____7723
                                         (fun x1  ->
                                            let uu____7729 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____7729
                                              (fun y1  ->
                                                 let uu____7735 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____7735
                                                   (fun z1  ->
                                                      let uu____7741 =
                                                        let uu____7742 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____7742
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____7741))))))
                     in
                  f_wrapped
  