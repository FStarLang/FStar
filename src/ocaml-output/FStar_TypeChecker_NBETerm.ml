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
      lazy_embed etyp o
        (fun uu____4096  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4097 =
                 let uu____4098 =
                   let uu____4103 = type_of ea  in as_iarg uu____4103  in
                 [uu____4098]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4097
           | FStar_Pervasives_Native.Some x ->
               let uu____4113 =
                 let uu____4114 =
                   let uu____4119 = embed ea cb x  in as_arg uu____4119  in
                 let uu____4124 =
                   let uu____4131 =
                     let uu____4136 = type_of ea  in as_iarg uu____4136  in
                   [uu____4131]  in
                 uu____4114 :: uu____4124  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4113)
       in
    let un cb trm =
      lazy_unembed etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4213)::uu____4214::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4241 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4241
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4254 -> FStar_Pervasives_Native.None)
       in
    let uu____4257 =
      let uu____4258 =
        let uu____4259 = let uu____4264 = type_of ea  in as_arg uu____4264
           in
        [uu____4259]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4258
       in
    mk_emb em un uu____4257 etyp
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4310 =
          let uu____4317 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4317, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4310  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4355  ->
             let uu____4356 =
               let uu____4357 =
                 let uu____4362 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4362  in
               let uu____4367 =
                 let uu____4374 =
                   let uu____4379 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4379  in
                 let uu____4384 =
                   let uu____4391 =
                     let uu____4396 = type_of eb  in as_iarg uu____4396  in
                   let uu____4397 =
                     let uu____4404 =
                       let uu____4409 = type_of ea  in as_iarg uu____4409  in
                     [uu____4404]  in
                   uu____4391 :: uu____4397  in
                 uu____4374 :: uu____4384  in
               uu____4357 :: uu____4367  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4356)
         in
      let un cb trm =
        lazy_unembed etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____4487)::(a,uu____4489)::uu____4490::uu____4491::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____4530 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4530
                   (fun a1  ->
                      let uu____4544 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____4544
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____4561 -> FStar_Pervasives_Native.None)
         in
      let uu____4566 =
        let uu____4567 =
          let uu____4568 = let uu____4573 = type_of eb  in as_arg uu____4573
             in
          let uu____4574 =
            let uu____4581 =
              let uu____4586 = type_of ea  in as_arg uu____4586  in
            [uu____4581]  in
          uu____4568 :: uu____4574  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4567
         in
      mk_emb em un uu____4566 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4638 =
          let uu____4645 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4645, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4638  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____4684  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____4686 =
                   let uu____4687 =
                     let uu____4692 = embed ea cb a  in as_arg uu____4692  in
                   let uu____4697 =
                     let uu____4704 =
                       let uu____4709 = type_of eb  in as_iarg uu____4709  in
                     let uu____4710 =
                       let uu____4717 =
                         let uu____4722 = type_of ea  in as_iarg uu____4722
                          in
                       [uu____4717]  in
                     uu____4704 :: uu____4710  in
                   uu____4687 :: uu____4697  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4686
             | FStar_Util.Inr b ->
                 let uu____4740 =
                   let uu____4741 =
                     let uu____4746 = embed eb cb b  in as_arg uu____4746  in
                   let uu____4751 =
                     let uu____4758 =
                       let uu____4763 = type_of eb  in as_iarg uu____4763  in
                     let uu____4764 =
                       let uu____4771 =
                         let uu____4776 = type_of ea  in as_iarg uu____4776
                          in
                       [uu____4771]  in
                     uu____4758 :: uu____4764  in
                   uu____4741 :: uu____4751  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4740)
         in
      let un cb trm =
        lazy_unembed etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____4848)::uu____4849::uu____4850::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____4885 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4885
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____4905)::uu____4906::uu____4907::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____4942 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____4942
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____4959 -> FStar_Pervasives_Native.None)
         in
      let uu____4964 =
        let uu____4965 =
          let uu____4966 = let uu____4971 = type_of eb  in as_arg uu____4971
             in
          let uu____4972 =
            let uu____4979 =
              let uu____4984 = type_of ea  in as_arg uu____4984  in
            [uu____4979]  in
          uu____4966 :: uu____4972  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4965
         in
      mk_emb em un uu____4964 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5052 -> FStar_Pervasives_Native.None  in
  let uu____5053 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5058 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5053 uu____5058 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5078 =
        let uu____5085 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5085, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5078  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5119  ->
           let typ = let uu____5121 = type_of ea  in as_iarg uu____5121  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5142 =
               let uu____5143 = as_arg tl1  in
               let uu____5148 =
                 let uu____5155 =
                   let uu____5160 = embed ea cb hd1  in as_arg uu____5160  in
                 [uu____5155; typ]  in
               uu____5143 :: uu____5148  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5142
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5222,uu____5223) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5243,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5246,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5247))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5274 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5274
                 (fun hd2  ->
                    let uu____5286 = un cb tl1  in
                    FStar_Util.bind_opt uu____5286
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5308,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5333 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5333
                 (fun hd2  ->
                    let uu____5345 = un cb tl1  in
                    FStar_Util.bind_opt uu____5345
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5366 -> FStar_Pervasives_Native.None)
       in
    let uu____5369 =
      let uu____5370 =
        let uu____5371 = let uu____5376 = type_of ea  in as_arg uu____5376
           in
        [uu____5371]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5370
       in
    mk_emb em un uu____5369 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5455  ->
             Lam
               ((fun tas  ->
                   let uu____5484 =
                     let uu____5487 = FStar_List.hd tas  in
                     unembed ea cb uu____5487  in
                   match uu____5484 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5493 = f a  in embed eb cb uu____5493
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____5509  ->
                     let uu____5512 = type_of eb  in as_arg uu____5512)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          match lam1 with
          | Lam (ft,uu____5578,uu____5579,uu____5580) ->
              FStar_Pervasives_Native.Some
                ((fun x  ->
                    let uu____5630 =
                      let uu____5633 =
                        let uu____5634 =
                          let uu____5637 = embed ea cb x  in [uu____5637]  in
                        ft uu____5634  in
                      unembed eb cb uu____5633  in
                    match uu____5630 with
                    | FStar_Pervasives_Native.Some x1 -> x1
                    | FStar_Pervasives_Native.None  ->
                        failwith "cannot unembed function result"))
          | uu____5647 -> FStar_Pervasives_Native.None  in
        lazy_unembed etyp lam k  in
      let uu____5654 =
        let uu____5655 = type_of ea  in
        let uu____5656 = let uu____5657 = type_of eb  in as_iarg uu____5657
           in
        make_arrow1 uu____5655 uu____5656  in
      mk_emb em un uu____5654 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5684 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5684 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5689 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5689 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5694 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5694 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5699 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5699 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5704 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5704 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5709 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5709 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5714 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5714 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5719 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5719 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5724 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5724 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5732 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5733 =
          let uu____5734 =
            let uu____5739 =
              let uu____5740 = e_list e_string  in embed uu____5740 cb l  in
            as_arg uu____5739  in
          [uu____5734]  in
        mkFV uu____5732 [] uu____5733
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5762 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5763 =
          let uu____5764 =
            let uu____5769 =
              let uu____5770 = e_list e_string  in embed uu____5770 cb l  in
            as_arg uu____5769  in
          [uu____5764]  in
        mkFV uu____5762 [] uu____5763
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____5816,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____5832,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____5848,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____5864,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____5880,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____5896,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____5912,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____5928,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____5944,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____5960,(l,uu____5962)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____5981 =
          let uu____5986 = e_list e_string  in unembed uu____5986 cb l  in
        FStar_Util.bind_opt uu____5981
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6006,(l,uu____6008)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6027 =
          let uu____6032 = e_list e_string  in unembed uu____6032 cb l  in
        FStar_Util.bind_opt uu____6027
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____6051 ->
        ((let uu____6053 =
            let uu____6058 =
              let uu____6059 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6059
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6058)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6053);
         FStar_Pervasives_Native.None)
     in
  let uu____6060 =
    let uu____6061 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6061 [] []  in
  let uu____6066 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6060 uu____6066 
let bogus_cb :
  'Auu____6075 'Auu____6076 . 'Auu____6075 -> 'Auu____6076 -> 'Auu____6075 =
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
      let uu____6151 =
        let uu____6160 = e_list e  in unembed uu____6160 bogus_cb  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6151
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____6181  ->
    match uu____6181 with
    | (a,uu____6189) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6204)::[]) when
             let uu____6221 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6221 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6226 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cb n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6268 = let uu____6275 = as_arg c  in [uu____6275]  in
      int_to_t2 uu____6268
  
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
          let uu____6328 = f a  in FStar_Pervasives_Native.Some uu____6328
      | uu____6329 -> FStar_Pervasives_Native.None
  
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
          let uu____6382 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6382
      | uu____6383 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6426 = FStar_List.map as_a args  in lift_unary f uu____6426
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6480 = FStar_List.map as_a args  in
        lift_binary f uu____6480
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6509 = f x  in embed e_int bogus_cb uu____6509)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  -> let uu____6535 = f x y  in embed e_int bogus_cb uu____6535)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6554 = f x  in embed e_bool bogus_cb uu____6554)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6580 = f x y  in embed e_bool bogus_cb uu____6580)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____6606 = f x y  in embed e_string bogus_cb uu____6606)
  
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
                let uu____6708 =
                  let uu____6717 = as_a a  in
                  let uu____6720 = as_b b  in (uu____6717, uu____6720)  in
                (match uu____6708 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____6735 =
                       let uu____6736 = f a1 b1  in embed_c uu____6736  in
                     FStar_Pervasives_Native.Some uu____6735
                 | uu____6737 -> FStar_Pervasives_Native.None)
            | uu____6746 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____6752 = e_list e_char  in
    let uu____6759 = FStar_String.list_of_string s  in
    embed uu____6752 bogus_cb uu____6759
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____6789 =
        let uu____6790 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____6790  in
      embed e_int bogus_cb uu____6789
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6822 = arg_as_string a1  in
        (match uu____6822 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6828 = arg_as_list e_string a2  in
             (match uu____6828 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6841 = embed e_string bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____6841
              | uu____6842 -> FStar_Pervasives_Native.None)
         | uu____6847 -> FStar_Pervasives_Native.None)
    | uu____6850 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____6856 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cb uu____6856
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cb (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cb true  in
      let fal = embed e_bool bogus_cb false  in
      match args with
      | (_univ,uu____6882)::(_typ,uu____6884)::(a1,uu____6886)::(a2,uu____6888)::[]
          ->
          let uu____6909 = eq_t a1 a2  in
          (match uu____6909 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____6914 -> FStar_Pervasives_Native.None)
      | uu____6915 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____6928)::(_typ,uu____6930)::(a1,uu____6932)::(a2,uu____6934)::[]
        ->
        let uu____6955 = eq_t a1 a2  in
        (match uu____6955 with
         | FStar_Syntax_Util.Equal  ->
             let uu____6958 = embed e_bool bogus_cb true  in
             FStar_Pervasives_Native.Some uu____6958
         | FStar_Syntax_Util.NotEqual  ->
             let uu____6959 = embed e_bool bogus_cb false  in
             FStar_Pervasives_Native.Some uu____6959
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____6960 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____6977 =
        let uu____6978 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____6978  in
      failwith uu____6977
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____6991)::[] ->
        let uu____7000 = unembed e_range bogus_cb a1  in
        (match uu____7000 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7006 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____7006
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7007 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7041 = arg_as_list e_char a1  in
        (match uu____7041 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7057 = arg_as_string a2  in
             (match uu____7057 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____7066 =
                    let uu____7067 = e_list e_string  in
                    embed uu____7067 bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____7066
              | uu____7074 -> FStar_Pervasives_Native.None)
         | uu____7077 -> FStar_Pervasives_Native.None)
    | uu____7083 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____7124 =
          let uu____7137 = arg_as_string a1  in
          let uu____7140 = arg_as_int a2  in
          let uu____7143 = arg_as_int a3  in
          (uu____7137, uu____7140, uu____7143)  in
        (match uu____7124 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___230_7170  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____7174 = embed e_string bogus_cb r  in
                       FStar_Pervasives_Native.Some uu____7174) ()
              with | uu___229_7176 -> FStar_Pervasives_Native.None)
         | uu____7179 -> FStar_Pervasives_Native.None)
    | uu____7192 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7251 =
          let uu____7272 = arg_as_string fn  in
          let uu____7275 = arg_as_int from_line  in
          let uu____7278 = arg_as_int from_col  in
          let uu____7281 = arg_as_int to_line  in
          let uu____7284 = arg_as_int to_col  in
          (uu____7272, uu____7275, uu____7278, uu____7281, uu____7284)  in
        (match uu____7251 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7315 =
                 let uu____7316 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7317 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7316 uu____7317  in
               let uu____7318 =
                 let uu____7319 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7320 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7319 uu____7320  in
               FStar_Range.mk_range fn1 uu____7315 uu____7318  in
             let uu____7321 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____7321
         | uu____7322 -> FStar_Pervasives_Native.None)
    | uu____7343 -> FStar_Pervasives_Native.None
  
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
                let uu____7438 = FStar_List.splitAt n_tvars args  in
                match uu____7438 with
                | (_tvar_args,rest_args) ->
                    let uu____7487 = FStar_List.hd rest_args  in
                    (match uu____7487 with
                     | (x,uu____7499) ->
                         let uu____7500 = unembed ea cb x  in
                         FStar_Util.map_opt uu____7500
                           (fun x1  ->
                              let uu____7510 = f x1  in
                              embed eb cb uu____7510))
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
                  let uu____7628 = FStar_List.splitAt n_tvars args  in
                  match uu____7628 with
                  | (_tvar_args,rest_args) ->
                      let uu____7677 = FStar_List.hd rest_args  in
                      (match uu____7677 with
                       | (x,uu____7689) ->
                           let uu____7690 =
                             let uu____7695 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7695  in
                           (match uu____7690 with
                            | (y,uu____7713) ->
                                let uu____7714 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____7714
                                  (fun x1  ->
                                     let uu____7724 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____7724
                                       (fun y1  ->
                                          let uu____7734 =
                                            let uu____7735 = f x1 y1  in
                                            embed ec cb uu____7735  in
                                          FStar_Pervasives_Native.Some
                                            uu____7734))))
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
                    let uu____7872 = FStar_List.splitAt n_tvars args  in
                    match uu____7872 with
                    | (_tvar_args,rest_args) ->
                        let uu____7921 = FStar_List.hd rest_args  in
                        (match uu____7921 with
                         | (x,uu____7933) ->
                             let uu____7934 =
                               let uu____7939 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7939  in
                             (match uu____7934 with
                              | (y,uu____7957) ->
                                  let uu____7958 =
                                    let uu____7963 =
                                      let uu____7970 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7970  in
                                    FStar_List.hd uu____7963  in
                                  (match uu____7958 with
                                   | (z,uu____7992) ->
                                       let uu____7993 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____7993
                                         (fun x1  ->
                                            let uu____8003 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____8003
                                              (fun y1  ->
                                                 let uu____8013 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____8013
                                                   (fun z1  ->
                                                      let uu____8023 =
                                                        let uu____8024 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____8024
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____8023))))))
                     in
                  f_wrapped
  