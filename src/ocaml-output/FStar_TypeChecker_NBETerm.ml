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
  (FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn,FStar_Syntax_Syntax.emb_typ,
                                  t FStar_Common.thunk)
                                  FStar_Pervasives_Native.tuple3)
  FStar_Util.either 
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
    match projectee with | Var _0 -> true | uu____486 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____517 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____611 -> false
  
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
    match projectee with | Accu _0 -> true | uu____722 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____780 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____850 -> false 
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
    match projectee with | Constant _0 -> true | uu____906 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____920 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____934 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____947 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____974 -> false
  
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
    match projectee with | Refinement _0 -> true | uu____1062 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1122 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1160 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    (FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn,FStar_Syntax_Syntax.emb_typ,
                                    t FStar_Common.thunk)
                                    FStar_Pervasives_Native.tuple3)
      FStar_Util.either)
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1244 -> false
  
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
    match projectee with | Tot _0 -> true | uu____1366 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1404 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1436 -> false
  
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
    match projectee with | TOTAL  -> true | uu____1555 -> false
  
let (uu___is_MLEFFECT : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1561 -> false
  
let (uu___is_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1567 -> false
  
let (uu___is_PARTIAL_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1573 -> false
  
let (uu___is_SOMETRIVIAL : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1579 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____1585 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____1591 -> false
  
let (uu___is_LEMMA : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1597 -> false
  
let (uu___is_CPS : cflags -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____1603 -> false 
let (uu___is_DECREASES : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1610 -> false
  
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
  fun trm  -> match trm with | Accu uu____1679 -> true | uu____1690 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1696,uu____1697) -> false | uu____1710 -> true
  
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
  fun uu___227_1839  ->
    if uu___227_1839
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___228_1845  ->
    if uu___228_1845
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
      | (FStar_Syntax_Util.NotEqual ,uu____1857) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1858,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1859) -> FStar_Syntax_Util.Unknown
      | (uu____1860,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1876 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1892),String (s2,uu____1894)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1902,uu____1903) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1938,Lam uu____1939) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2026 = eq_atom a1 a2  in
          eq_and uu____2026 (fun uu____2028  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2067 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2067
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2078 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2135  ->
                        match uu____2135 with
                        | ((a1,uu____2149),(a2,uu____2151)) ->
                            let uu____2160 = eq_t a1 a2  in
                            eq_inj acc uu____2160) FStar_Syntax_Util.Equal)
                uu____2078))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2200 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2200
          then
            let uu____2201 =
              let uu____2202 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2202  in
            eq_and uu____2201 (fun uu____2204  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2210 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2210
      | (Univ u1,Univ u2) ->
          let uu____2213 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2213
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2259 =
            let uu____2260 =
              let uu____2261 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2261  in
            let uu____2266 =
              let uu____2267 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2267  in
            eq_t uu____2260 uu____2266  in
          eq_and uu____2259
            (fun uu____2275  ->
               let uu____2276 =
                 let uu____2277 = mkAccuVar x  in r1 uu____2277  in
               let uu____2278 =
                 let uu____2279 = mkAccuVar x  in r2 uu____2279  in
               eq_t uu____2276 uu____2278)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2280,uu____2281) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2286,uu____2287) -> FStar_Syntax_Util.Unknown

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
          let uu____2368 = eq_arg x y  in
          eq_and uu____2368 (fun uu____2370  -> eq_args xs ys)
      | (uu____2371,uu____2372) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2408) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2410 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2410
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2431) ->
        let uu____2474 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2484 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2474 uu____2484
    | Accu (a,l) ->
        let uu____2499 =
          let uu____2500 = atom_to_string a  in
          let uu____2501 =
            let uu____2502 =
              let uu____2503 =
                let uu____2504 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2504  in
              Prims.strcat uu____2503 ")"  in
            Prims.strcat ") (" uu____2502  in
          Prims.strcat uu____2500 uu____2501  in
        Prims.strcat "Accu (" uu____2499
    | Construct (fv,us,l) ->
        let uu____2536 =
          let uu____2537 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2538 =
            let uu____2539 =
              let uu____2540 =
                let uu____2541 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2541  in
              let uu____2544 =
                let uu____2545 =
                  let uu____2546 =
                    let uu____2547 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2547  in
                  Prims.strcat uu____2546 "]"  in
                Prims.strcat "] [" uu____2545  in
              Prims.strcat uu____2540 uu____2544  in
            Prims.strcat ") [" uu____2539  in
          Prims.strcat uu____2537 uu____2538  in
        Prims.strcat "Construct (" uu____2536
    | FV (fv,us,l) ->
        let uu____2579 =
          let uu____2580 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2581 =
            let uu____2582 =
              let uu____2583 =
                let uu____2584 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2584  in
              let uu____2587 =
                let uu____2588 =
                  let uu____2589 =
                    let uu____2590 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2590  in
                  Prims.strcat uu____2589 "]"  in
                Prims.strcat "] [" uu____2588  in
              Prims.strcat uu____2583 uu____2587  in
            Prims.strcat ") [" uu____2582  in
          Prims.strcat uu____2580 uu____2581  in
        Prims.strcat "FV (" uu____2579
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2605 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2605
    | Type_t u ->
        let uu____2607 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2607
    | Arrow uu____2608 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2653 = t ()  in FStar_Pervasives_Native.fst uu____2653
           in
        let uu____2658 =
          let uu____2659 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2660 =
            let uu____2661 =
              let uu____2662 = t_to_string t1  in
              let uu____2663 =
                let uu____2664 =
                  let uu____2665 =
                    let uu____2666 =
                      let uu____2667 = mkAccuVar x1  in f uu____2667  in
                    t_to_string uu____2666  in
                  Prims.strcat uu____2665 "}"  in
                Prims.strcat "{" uu____2664  in
              Prims.strcat uu____2662 uu____2663  in
            Prims.strcat ":" uu____2661  in
          Prims.strcat uu____2659 uu____2660  in
        Prims.strcat "Refinement " uu____2658
    | Unknown  -> "Unknown"
    | Quote uu____2668 -> "Quote _"
    | Lazy uu____2673 -> "Lazy _"
    | Rec
        (uu____2686,uu____2687,l,uu____2689,uu____2690,uu____2691,uu____2692)
        ->
        let uu____2733 =
          let uu____2734 =
            let uu____2735 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2735  in
          Prims.strcat uu____2734 ")"  in
        Prims.strcat "Rec (" uu____2733

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2740 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2740
    | Match (t,uu____2742,uu____2743) ->
        let uu____2766 = t_to_string t  in Prims.strcat "Match " uu____2766

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2768 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2768 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2774 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2774 (FStar_String.concat " ")

type iapp_cb = t -> args -> t
type 'a embedding =
  {
  em: iapp_cb -> 'a -> t ;
  un: iapp_cb -> t -> 'a FStar_Pervasives_Native.option ;
  typ: t ;
  emb_typ: FStar_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> iapp_cb -> 'a -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;
        emb_typ = __fname__emb_typ;_} -> __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> iapp_cb -> t -> 'a FStar_Pervasives_Native.option =
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
  
let embed : 'a . 'a embedding -> iapp_cb -> 'a -> t =
  fun e  -> fun cb  -> fun x  -> e.em cb x 
let unembed :
  'a . 'a embedding -> iapp_cb -> t -> 'a FStar_Pervasives_Native.option =
  fun e  -> fun cb  -> fun trm  -> e.un cb trm 
let type_of : 'a . 'a embedding -> t = fun e  -> e.typ 
let mk_emb :
  'a .
    (iapp_cb -> 'a -> t) ->
      (iapp_cb -> t -> 'a FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  =
  fun em  -> fun un  -> fun typ  -> fun et  -> { em; un; typ; emb_typ = et } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3221 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3221 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3241 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3241 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3279  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3294  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____3336 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____3336
         then
           let uu____3356 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3356
         else ());
        (let uu____3358 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____3358
         then f ()
         else
           (let thunk = FStar_Common.mk_thunk f  in
            let li =
              let uu____3391 = FStar_Dyn.mkdyn x  in (uu____3391, et, thunk)
               in
            Lazy (FStar_Util.Inr li)))
  
let lazy_unembed :
  'a .
    FStar_Syntax_Syntax.emb_typ ->
      t ->
        (t -> 'a FStar_Pervasives_Native.option) ->
          'a FStar_Pervasives_Native.option
  =
  fun et  ->
    fun x  ->
      fun f  ->
        match x with
        | Lazy (FStar_Util.Inr (b,et',thunk)) ->
            let uu____3492 =
              (et <> et') || (FStar_ST.op_Bang FStar_Options.eager_embedding)
               in
            if uu____3492
            then
              let res =
                let uu____3517 = FStar_Common.force_thunk thunk  in
                f uu____3517  in
              ((let uu____3559 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____3559
                then
                  let uu____3579 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  let uu____3580 = FStar_Syntax_Print.emb_typ_to_string et'
                     in
                  FStar_Util.print2
                    "Unembed cancellation failed\n\t%s <> %s\n" uu____3579
                    uu____3580
                else ());
               res)
            else
              (let a = FStar_Dyn.undyn b  in
               (let uu____3585 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____3585
                then
                  let uu____3605 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembed cancelled for %s\n" uu____3605
                else ());
               FStar_Pervasives_Native.Some a)
        | uu____3607 ->
            let aopt = f x  in
            ((let uu____3612 = FStar_ST.op_Bang FStar_Options.debug_embedding
                 in
              if uu____3612
              then
                let uu____3632 = FStar_Syntax_Print.emb_typ_to_string et  in
                FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____3632
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
  let uu____3735 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____3735 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____3788 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____3793 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____3788 uu____3793 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____3845 -> FStar_Pervasives_Native.None  in
  let uu____3846 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____3851 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____3846 uu____3851 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____3911 -> FStar_Pervasives_Native.None  in
  let uu____3913 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____3918 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____3913 uu____3918 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____3972)) -> FStar_Pervasives_Native.Some s1
    | uu____3973 -> FStar_Pervasives_Native.None  in
  let uu____3974 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____3979 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____3974 uu____3979 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4031 -> FStar_Pervasives_Native.None  in
  let uu____4032 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4037 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4032 uu____4037 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4057 =
        let uu____4064 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4064, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4057  in
    let em cb o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____4092 =
            let uu____4093 =
              let uu____4098 = type_of ea  in as_iarg uu____4098  in
            [uu____4093]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____4092
      | FStar_Pervasives_Native.Some x ->
          let uu____4108 =
            let uu____4109 =
              let uu____4114 = embed ea cb x  in as_arg uu____4114  in
            let uu____4119 =
              let uu____4126 =
                let uu____4131 = type_of ea  in as_iarg uu____4131  in
              [uu____4126]  in
            uu____4109 :: uu____4119  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____4108
       in
    let un cb trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,(a,uu____4197)::uu____4198::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____4225 = unembed ea cb a  in
          FStar_Util.bind_opt uu____4225
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____4238 -> FStar_Pervasives_Native.None  in
    let uu____4241 =
      let uu____4242 =
        let uu____4243 = let uu____4248 = type_of ea  in as_arg uu____4248
           in
        [uu____4243]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4242
       in
    mk_emb em un uu____4241 etyp
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4294 =
          let uu____4301 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4301, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4294  in
      let em cb x =
        let uu____4333 =
          let uu____4334 =
            let uu____4339 = embed eb cb (FStar_Pervasives_Native.snd x)  in
            as_arg uu____4339  in
          let uu____4344 =
            let uu____4351 =
              let uu____4356 = embed ea cb (FStar_Pervasives_Native.fst x)
                 in
              as_arg uu____4356  in
            let uu____4361 =
              let uu____4368 =
                let uu____4373 = type_of eb  in as_iarg uu____4373  in
              let uu____4374 =
                let uu____4381 =
                  let uu____4386 = type_of ea  in as_iarg uu____4386  in
                [uu____4381]  in
              uu____4368 :: uu____4374  in
            uu____4351 :: uu____4361  in
          uu____4334 :: uu____4344  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4333
         in
      let un cb trm =
        match trm with
        | Construct
            (fvar1,us,(b,uu____4443)::(a,uu____4445)::uu____4446::uu____4447::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____4486 = unembed ea cb a  in
            FStar_Util.bind_opt uu____4486
              (fun a1  ->
                 let uu____4500 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____4500
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____4517 -> FStar_Pervasives_Native.None  in
      let uu____4522 =
        let uu____4523 =
          let uu____4524 = let uu____4529 = type_of eb  in as_arg uu____4529
             in
          let uu____4530 =
            let uu____4537 =
              let uu____4542 = type_of ea  in as_arg uu____4542  in
            [uu____4537]  in
          uu____4524 :: uu____4530  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4523
         in
      mk_emb em un uu____4522 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4594 =
          let uu____4601 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4601, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4594  in
      let em cb s =
        match s with
        | FStar_Util.Inl a ->
            let uu____4634 =
              let uu____4635 =
                let uu____4640 = embed ea cb a  in as_arg uu____4640  in
              let uu____4645 =
                let uu____4652 =
                  let uu____4657 = type_of eb  in as_iarg uu____4657  in
                let uu____4658 =
                  let uu____4665 =
                    let uu____4670 = type_of ea  in as_iarg uu____4670  in
                  [uu____4665]  in
                uu____4652 :: uu____4658  in
              uu____4635 :: uu____4645  in
            lid_as_constr FStar_Parser_Const.inl_lid
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
              uu____4634
        | FStar_Util.Inr b ->
            let uu____4688 =
              let uu____4689 =
                let uu____4694 = embed eb cb b  in as_arg uu____4694  in
              let uu____4699 =
                let uu____4706 =
                  let uu____4711 = type_of eb  in as_iarg uu____4711  in
                let uu____4712 =
                  let uu____4719 =
                    let uu____4724 = type_of ea  in as_iarg uu____4724  in
                  [uu____4719]  in
                uu____4706 :: uu____4712  in
              uu____4689 :: uu____4699  in
            lid_as_constr FStar_Parser_Const.inr_lid
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
              uu____4688
         in
      let un cb trm =
        match trm with
        | Construct (fvar1,us,(a,uu____4777)::uu____4778::uu____4779::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inl_lid ->
            let uu____4814 = unembed ea cb a  in
            FStar_Util.bind_opt uu____4814
              (fun a1  -> FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
        | Construct (fvar1,us,(b,uu____4834)::uu____4835::uu____4836::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inr_lid ->
            let uu____4871 = unembed eb cb b  in
            FStar_Util.bind_opt uu____4871
              (fun b1  -> FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
        | uu____4888 -> FStar_Pervasives_Native.None  in
      let uu____4893 =
        let uu____4894 =
          let uu____4895 = let uu____4900 = type_of eb  in as_arg uu____4900
             in
          let uu____4901 =
            let uu____4908 =
              let uu____4913 = type_of ea  in as_arg uu____4913  in
            [uu____4908]  in
          uu____4895 :: uu____4901  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4894
         in
      mk_emb em un uu____4893 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____4981 -> FStar_Pervasives_Native.None  in
  let uu____4982 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____4987 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____4982 uu____4987 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5007 =
        let uu____5014 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5014, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5007  in
    let em cb l =
      let typ = let uu____5043 = type_of ea  in as_iarg uu____5043  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____5064 =
          let uu____5065 = as_arg tl1  in
          let uu____5070 =
            let uu____5077 =
              let uu____5082 = embed ea cb hd1  in as_arg uu____5082  in
            [uu____5077; typ]  in
          uu____5065 :: uu____5070  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____5064
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un cb trm =
      match trm with
      | Construct (fv,uu____5133,uu____5134) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____5154,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                               )::(uu____5157,FStar_Pervasives_Native.Some
                                                                   (FStar_Syntax_Syntax.Implicit
                                                                   uu____5158))::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____5185 = unembed ea cb hd1  in
          FStar_Util.bind_opt uu____5185
            (fun hd2  ->
               let uu____5197 = un cb tl1  in
               FStar_Util.bind_opt uu____5197
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____5219,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____5244 = unembed ea cb hd1  in
          FStar_Util.bind_opt uu____5244
            (fun hd2  ->
               let uu____5256 = un cb tl1  in
               FStar_Util.bind_opt uu____5256
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____5277 -> FStar_Pervasives_Native.None  in
    let uu____5280 =
      let uu____5281 =
        let uu____5282 = let uu____5287 = type_of ea  in as_arg uu____5287
           in
        [uu____5282]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5281
       in
    mk_emb em un uu____5280 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        Lam
          ((fun tas  ->
              let uu____5390 =
                let uu____5393 = FStar_List.hd tas  in
                unembed ea cb uu____5393  in
              match uu____5390 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____5399 = f a  in embed eb cb uu____5399
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____5415  ->
                let uu____5418 = type_of eb  in as_arg uu____5418)],
            (Prims.parse_int "1"), FStar_Pervasives_Native.None)
         in
      let un cb lam =
        match lam with
        | Lam (ft,uu____5468,uu____5469,uu____5470) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____5520 =
                    let uu____5523 =
                      let uu____5524 =
                        let uu____5527 = embed ea cb x  in [uu____5527]  in
                      ft uu____5524  in
                    unembed eb cb uu____5523  in
                  match uu____5520 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____5537 -> FStar_Pervasives_Native.None  in
      let uu____5541 =
        let uu____5542 = type_of ea  in
        let uu____5543 = let uu____5544 = type_of eb  in as_iarg uu____5544
           in
        make_arrow1 uu____5542 uu____5543  in
      mk_emb em un uu____5541 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5571 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5571 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5576 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5576 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5581 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5581 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5586 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5586 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5591 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5591 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5596 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5596 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5601 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5601 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5606 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5606 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5611 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5611 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5619 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5620 =
          let uu____5621 =
            let uu____5626 =
              let uu____5627 = e_list e_string  in embed uu____5627 cb l  in
            as_arg uu____5626  in
          [uu____5621]  in
        mkFV uu____5619 [] uu____5620
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5649 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5650 =
          let uu____5651 =
            let uu____5656 =
              let uu____5657 = e_list e_string  in embed uu____5657 cb l  in
            as_arg uu____5656  in
          [uu____5651]  in
        mkFV uu____5649 [] uu____5650
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____5703,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____5719,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____5735,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____5751,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____5767,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____5783,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____5799,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____5815,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____5831,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____5847,(l,uu____5849)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____5868 =
          let uu____5873 = e_list e_string  in unembed uu____5873 cb l  in
        FStar_Util.bind_opt uu____5868
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____5893,(l,uu____5895)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____5914 =
          let uu____5919 = e_list e_string  in unembed uu____5919 cb l  in
        FStar_Util.bind_opt uu____5914
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____5938 ->
        ((let uu____5940 =
            let uu____5945 =
              let uu____5946 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____5946
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5945)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5940);
         FStar_Pervasives_Native.None)
     in
  let uu____5947 =
    let uu____5948 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____5948 [] []  in
  let uu____5953 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____5947 uu____5953 
let bogus_cb :
  'Auu____5962 'Auu____5963 . 'Auu____5962 -> 'Auu____5963 -> 'Auu____5962 =
  fun h  -> fun _args  -> h 
let (arg_as_int : arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_int bogus_cb)
  
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_bool bogus_cb)
  
let (arg_as_char : arg -> FStar_Char.char FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_char bogus_cb)
  
let (arg_as_string : arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_string bogus_cb)
  
let arg_as_list :
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e  ->
    fun a  ->
      let uu____6038 =
        let uu____6047 = e_list e  in unembed uu____6047 bogus_cb  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6038
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____6068  ->
    match uu____6068 with
    | (a,uu____6076) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6091)::[]) when
             let uu____6108 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6108 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6113 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cb n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6155 = let uu____6162 = as_arg c  in [uu____6162]  in
      int_to_t2 uu____6155
  
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
          let uu____6215 = f a  in FStar_Pervasives_Native.Some uu____6215
      | uu____6216 -> FStar_Pervasives_Native.None
  
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
          let uu____6269 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6269
      | uu____6270 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6313 = FStar_List.map as_a args  in lift_unary f uu____6313
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6367 = FStar_List.map as_a args  in
        lift_binary f uu____6367
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6396 = f x  in embed e_int bogus_cb uu____6396)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  -> let uu____6422 = f x y  in embed e_int bogus_cb uu____6422)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6441 = f x  in embed e_bool bogus_cb uu____6441)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6467 = f x y  in embed e_bool bogus_cb uu____6467)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____6493 = f x y  in embed e_string bogus_cb uu____6493)
  
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
                let uu____6595 =
                  let uu____6604 = as_a a  in
                  let uu____6607 = as_b b  in (uu____6604, uu____6607)  in
                (match uu____6595 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____6622 =
                       let uu____6623 = f a1 b1  in embed_c uu____6623  in
                     FStar_Pervasives_Native.Some uu____6622
                 | uu____6624 -> FStar_Pervasives_Native.None)
            | uu____6633 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____6639 = e_list e_char  in
    let uu____6646 = FStar_String.list_of_string s  in
    embed uu____6639 bogus_cb uu____6646
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____6676 =
        let uu____6677 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____6677  in
      embed e_int bogus_cb uu____6676
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6709 = arg_as_string a1  in
        (match uu____6709 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6715 = arg_as_list e_string a2  in
             (match uu____6715 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6728 = embed e_string bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____6728
              | uu____6729 -> FStar_Pervasives_Native.None)
         | uu____6734 -> FStar_Pervasives_Native.None)
    | uu____6737 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____6743 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cb uu____6743
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cb (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cb true  in
      let fal = embed e_bool bogus_cb false  in
      match args with
      | (_univ,uu____6769)::(_typ,uu____6771)::(a1,uu____6773)::(a2,uu____6775)::[]
          ->
          let uu____6796 = eq_t a1 a2  in
          (match uu____6796 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____6801 -> FStar_Pervasives_Native.None)
      | uu____6802 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____6815)::(_typ,uu____6817)::(a1,uu____6819)::(a2,uu____6821)::[]
        ->
        let uu____6842 = eq_t a1 a2  in
        (match uu____6842 with
         | FStar_Syntax_Util.Equal  ->
             let uu____6845 = embed e_bool bogus_cb true  in
             FStar_Pervasives_Native.Some uu____6845
         | FStar_Syntax_Util.NotEqual  ->
             let uu____6846 = embed e_bool bogus_cb false  in
             FStar_Pervasives_Native.Some uu____6846
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____6847 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____6864 =
        let uu____6865 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____6865  in
      failwith uu____6864
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____6878)::[] ->
        let uu____6887 = unembed e_range bogus_cb a1  in
        (match uu____6887 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6893 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____6893
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6894 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6928 = arg_as_list e_char a1  in
        (match uu____6928 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6944 = arg_as_string a2  in
             (match uu____6944 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____6953 =
                    let uu____6954 = e_list e_string  in
                    embed uu____6954 bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____6953
              | uu____6961 -> FStar_Pervasives_Native.None)
         | uu____6964 -> FStar_Pervasives_Native.None)
    | uu____6970 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____7011 =
          let uu____7024 = arg_as_string a1  in
          let uu____7027 = arg_as_int a2  in
          let uu____7030 = arg_as_int a3  in
          (uu____7024, uu____7027, uu____7030)  in
        (match uu____7011 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___230_7057  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____7061 = embed e_string bogus_cb r  in
                       FStar_Pervasives_Native.Some uu____7061) ()
              with | uu___229_7063 -> FStar_Pervasives_Native.None)
         | uu____7066 -> FStar_Pervasives_Native.None)
    | uu____7079 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7138 =
          let uu____7159 = arg_as_string fn  in
          let uu____7162 = arg_as_int from_line  in
          let uu____7165 = arg_as_int from_col  in
          let uu____7168 = arg_as_int to_line  in
          let uu____7171 = arg_as_int to_col  in
          (uu____7159, uu____7162, uu____7165, uu____7168, uu____7171)  in
        (match uu____7138 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7202 =
                 let uu____7203 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7204 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7203 uu____7204  in
               let uu____7205 =
                 let uu____7206 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7207 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7206 uu____7207  in
               FStar_Range.mk_range fn1 uu____7202 uu____7205  in
             let uu____7208 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____7208
         | uu____7209 -> FStar_Pervasives_Native.None)
    | uu____7230 -> FStar_Pervasives_Native.None
  
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          Prims.int ->
            FStar_Ident.lid ->
              iapp_cb -> args -> t FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun f  ->
        fun n_tvars  ->
          fun _fv_lid  ->
            fun cb  ->
              let f_wrapped args =
                let uu____7325 = FStar_List.splitAt n_tvars args  in
                match uu____7325 with
                | (_tvar_args,rest_args) ->
                    let uu____7374 = FStar_List.hd rest_args  in
                    (match uu____7374 with
                     | (x,uu____7386) ->
                         let uu____7387 = unembed ea cb x  in
                         FStar_Util.map_opt uu____7387
                           (fun x1  ->
                              let uu____7397 = f x1  in
                              embed eb cb uu____7397))
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
                iapp_cb -> args -> t FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun f  ->
          fun n_tvars  ->
            fun _fv_lid  ->
              fun cb  ->
                let f_wrapped args =
                  let uu____7515 = FStar_List.splitAt n_tvars args  in
                  match uu____7515 with
                  | (_tvar_args,rest_args) ->
                      let uu____7564 = FStar_List.hd rest_args  in
                      (match uu____7564 with
                       | (x,uu____7576) ->
                           let uu____7577 =
                             let uu____7582 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7582  in
                           (match uu____7577 with
                            | (y,uu____7600) ->
                                let uu____7601 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____7601
                                  (fun x1  ->
                                     let uu____7611 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____7611
                                       (fun y1  ->
                                          let uu____7621 =
                                            let uu____7622 = f x1 y1  in
                                            embed ec cb uu____7622  in
                                          FStar_Pervasives_Native.Some
                                            uu____7621))))
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
                  iapp_cb -> args -> t FStar_Pervasives_Native.option
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
                    let uu____7759 = FStar_List.splitAt n_tvars args  in
                    match uu____7759 with
                    | (_tvar_args,rest_args) ->
                        let uu____7808 = FStar_List.hd rest_args  in
                        (match uu____7808 with
                         | (x,uu____7820) ->
                             let uu____7821 =
                               let uu____7826 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7826  in
                             (match uu____7821 with
                              | (y,uu____7844) ->
                                  let uu____7845 =
                                    let uu____7850 =
                                      let uu____7857 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7857  in
                                    FStar_List.hd uu____7850  in
                                  (match uu____7845 with
                                   | (z,uu____7879) ->
                                       let uu____7880 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____7880
                                         (fun x1  ->
                                            let uu____7890 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____7890
                                              (fun y1  ->
                                                 let uu____7900 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____7900
                                                   (fun z1  ->
                                                      let uu____7910 =
                                                        let uu____7911 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____7911
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____7910))))))
                     in
                  f_wrapped
  