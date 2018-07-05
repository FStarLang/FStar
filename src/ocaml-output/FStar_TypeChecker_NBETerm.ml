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
  | Lazy of FStar_Syntax_Syntax.lazyinfo 
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
    match projectee with | Var _0 -> true | uu____455 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____486 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____580 -> false
  
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
    match projectee with | Accu _0 -> true | uu____691 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____749 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____819 -> false 
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
    match projectee with | Constant _0 -> true | uu____875 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____889 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____903 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____916 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____943 -> false
  
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
    match projectee with | Refinement _0 -> true | uu____1031 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1091 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1117 -> false
  
let (__proj__Lazy__item___0 : t -> FStar_Syntax_Syntax.lazyinfo) =
  fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1165 -> false
  
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
    match projectee with | Tot _0 -> true | uu____1287 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1325 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1357 -> false
  
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
    match projectee with | TOTAL  -> true | uu____1476 -> false
  
let (uu___is_MLEFFECT : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1482 -> false
  
let (uu___is_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1488 -> false
  
let (uu___is_PARTIAL_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1494 -> false
  
let (uu___is_SOMETRIVIAL : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1500 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____1506 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____1512 -> false
  
let (uu___is_LEMMA : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1518 -> false
  
let (uu___is_CPS : cflags -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____1524 -> false 
let (uu___is_DECREASES : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1531 -> false
  
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
  fun trm  -> match trm with | Accu uu____1600 -> true | uu____1611 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1617,uu____1618) -> false | uu____1631 -> true
  
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
  fun uu___227_1760  ->
    if uu___227_1760
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___228_1766  ->
    if uu___228_1766
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
      | (FStar_Syntax_Util.NotEqual ,uu____1778) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1779,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1780) -> FStar_Syntax_Util.Unknown
      | (uu____1781,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1797 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1813),String (s2,uu____1815)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1823,uu____1824) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1859,Lam uu____1860) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1947 = eq_atom a1 a2  in
          eq_and uu____1947 (fun uu____1949  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1988 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1988
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____1999 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2056  ->
                        match uu____2056 with
                        | ((a1,uu____2070),(a2,uu____2072)) ->
                            let uu____2081 = eq_t a1 a2  in
                            eq_inj acc uu____2081) FStar_Syntax_Util.Equal)
                uu____1999))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2121 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2121
          then
            let uu____2122 =
              let uu____2123 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2123  in
            eq_and uu____2122 (fun uu____2125  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2131 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2131
      | (Univ u1,Univ u2) ->
          let uu____2134 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2134
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2180 =
            let uu____2181 =
              let uu____2182 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2182  in
            let uu____2187 =
              let uu____2188 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2188  in
            eq_t uu____2181 uu____2187  in
          eq_and uu____2180
            (fun uu____2196  ->
               let uu____2197 =
                 let uu____2198 = mkAccuVar x  in r1 uu____2198  in
               let uu____2199 =
                 let uu____2200 = mkAccuVar x  in r2 uu____2200  in
               eq_t uu____2197 uu____2199)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2201,uu____2202) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2207,uu____2208) -> FStar_Syntax_Util.Unknown

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
          let uu____2289 = eq_arg x y  in
          eq_and uu____2289 (fun uu____2291  -> eq_args xs ys)
      | (uu____2292,uu____2293) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2329) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2331 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2331
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2352) ->
        let uu____2395 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2405 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2395 uu____2405
    | Accu (a,l) ->
        let uu____2420 =
          let uu____2421 = atom_to_string a  in
          let uu____2422 =
            let uu____2423 =
              let uu____2424 =
                let uu____2425 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2425  in
              Prims.strcat uu____2424 ")"  in
            Prims.strcat ") (" uu____2423  in
          Prims.strcat uu____2421 uu____2422  in
        Prims.strcat "Accu (" uu____2420
    | Construct (fv,us,l) ->
        let uu____2457 =
          let uu____2458 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2459 =
            let uu____2460 =
              let uu____2461 =
                let uu____2462 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2462  in
              let uu____2465 =
                let uu____2466 =
                  let uu____2467 =
                    let uu____2468 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2468  in
                  Prims.strcat uu____2467 "]"  in
                Prims.strcat "] [" uu____2466  in
              Prims.strcat uu____2461 uu____2465  in
            Prims.strcat ") [" uu____2460  in
          Prims.strcat uu____2458 uu____2459  in
        Prims.strcat "Construct (" uu____2457
    | FV (fv,us,l) ->
        let uu____2500 =
          let uu____2501 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2502 =
            let uu____2503 =
              let uu____2504 =
                let uu____2505 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2505  in
              let uu____2508 =
                let uu____2509 =
                  let uu____2510 =
                    let uu____2511 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2511  in
                  Prims.strcat uu____2510 "]"  in
                Prims.strcat "] [" uu____2509  in
              Prims.strcat uu____2504 uu____2508  in
            Prims.strcat ") [" uu____2503  in
          Prims.strcat uu____2501 uu____2502  in
        Prims.strcat "FV (" uu____2500
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2526 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2526
    | Type_t u ->
        let uu____2528 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2528
    | Arrow uu____2529 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2574 = t ()  in FStar_Pervasives_Native.fst uu____2574
           in
        let uu____2579 =
          let uu____2580 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2581 =
            let uu____2582 =
              let uu____2583 = t_to_string t1  in
              let uu____2584 =
                let uu____2585 =
                  let uu____2586 =
                    let uu____2587 =
                      let uu____2588 = mkAccuVar x1  in f uu____2588  in
                    t_to_string uu____2587  in
                  Prims.strcat uu____2586 "}"  in
                Prims.strcat "{" uu____2585  in
              Prims.strcat uu____2583 uu____2584  in
            Prims.strcat ":" uu____2582  in
          Prims.strcat uu____2580 uu____2581  in
        Prims.strcat "Refinement " uu____2579
    | Unknown  -> "Unknown"
    | Quote uu____2589 -> "Quote _"
    | Lazy uu____2594 -> "Lazy _"
    | Rec
        (uu____2595,uu____2596,l,uu____2598,uu____2599,uu____2600,uu____2601)
        ->
        let uu____2642 =
          let uu____2643 =
            let uu____2644 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2644  in
          Prims.strcat uu____2643 ")"  in
        Prims.strcat "Rec (" uu____2642

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2649 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2649
    | Match (t,uu____2651,uu____2652) ->
        let uu____2675 = t_to_string t  in Prims.strcat "Match " uu____2675

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2677 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2677 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2683 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2683 (FStar_String.concat " ")

type iapp_cb = t -> args -> t
type 'a embedding =
  {
  em: iapp_cb -> 'a -> t ;
  un: iapp_cb -> t -> 'a FStar_Pervasives_Native.option ;
  typ: t }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> iapp_cb -> 'a -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> iapp_cb -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__un
  
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__typ
  
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
        t -> 'a embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3075 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3075 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3095 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3095 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3133  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3148  -> a)])
  
let (e_any : t embedding) =
  let em _cb a = a  in
  let un _cb t = FStar_Pervasives_Native.Some t  in
  let uu____3208 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____3208 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____3261 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____3261 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____3317 -> FStar_Pervasives_Native.None  in
  let uu____3318 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____3318 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____3382 -> FStar_Pervasives_Native.None  in
  let uu____3384 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____3384 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____3441)) -> FStar_Pervasives_Native.Some s1
    | uu____3442 -> FStar_Pervasives_Native.None  in
  let uu____3443 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____3443 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____3499 -> FStar_Pervasives_Native.None  in
  let uu____3500 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____3500 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em cb o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____3548 =
            let uu____3549 =
              let uu____3554 = type_of ea  in as_iarg uu____3554  in
            [uu____3549]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____3548
      | FStar_Pervasives_Native.Some x ->
          let uu____3564 =
            let uu____3565 =
              let uu____3570 = embed ea cb x  in as_arg uu____3570  in
            let uu____3575 =
              let uu____3582 =
                let uu____3587 = type_of ea  in as_iarg uu____3587  in
              [uu____3582]  in
            uu____3565 :: uu____3575  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____3564
       in
    let un cb trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,(a,uu____3653)::uu____3654::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____3681 = unembed ea cb a  in
          FStar_Util.bind_opt uu____3681
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____3694 -> FStar_Pervasives_Native.None  in
    let uu____3697 =
      let uu____3698 =
        let uu____3699 = let uu____3704 = type_of ea  in as_arg uu____3704
           in
        [uu____3699]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____3698
       in
    mk_emb em un uu____3697
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em cb x =
        let uu____3778 =
          let uu____3779 =
            let uu____3784 = embed eb cb (FStar_Pervasives_Native.snd x)  in
            as_arg uu____3784  in
          let uu____3789 =
            let uu____3796 =
              let uu____3801 = embed ea cb (FStar_Pervasives_Native.fst x)
                 in
              as_arg uu____3801  in
            let uu____3806 =
              let uu____3813 =
                let uu____3818 = type_of eb  in as_iarg uu____3818  in
              let uu____3819 =
                let uu____3826 =
                  let uu____3831 = type_of ea  in as_iarg uu____3831  in
                [uu____3826]  in
              uu____3813 :: uu____3819  in
            uu____3796 :: uu____3806  in
          uu____3779 :: uu____3789  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3778
         in
      let un cb trm =
        match trm with
        | Construct
            (fvar1,us,(b,uu____3888)::(a,uu____3890)::uu____3891::uu____3892::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3931 = unembed ea cb a  in
            FStar_Util.bind_opt uu____3931
              (fun a1  ->
                 let uu____3945 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____3945
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3962 -> FStar_Pervasives_Native.None  in
      let uu____3967 =
        let uu____3968 =
          let uu____3969 = let uu____3974 = type_of eb  in as_arg uu____3974
             in
          let uu____3975 =
            let uu____3982 =
              let uu____3987 = type_of ea  in as_arg uu____3987  in
            [uu____3982]  in
          uu____3969 :: uu____3975  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3968
         in
      mk_emb em un uu____3967
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let em cb s =
        match s with
        | FStar_Util.Inl a ->
            let uu____4068 =
              let uu____4069 =
                let uu____4074 = embed ea cb a  in as_arg uu____4074  in
              let uu____4079 =
                let uu____4086 =
                  let uu____4091 = type_of eb  in as_iarg uu____4091  in
                let uu____4092 =
                  let uu____4099 =
                    let uu____4104 = type_of ea  in as_iarg uu____4104  in
                  [uu____4099]  in
                uu____4086 :: uu____4092  in
              uu____4069 :: uu____4079  in
            lid_as_constr FStar_Parser_Const.inl_lid
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
              uu____4068
        | FStar_Util.Inr b ->
            let uu____4122 =
              let uu____4123 =
                let uu____4128 = embed eb cb b  in as_arg uu____4128  in
              let uu____4133 =
                let uu____4140 =
                  let uu____4145 = type_of eb  in as_iarg uu____4145  in
                let uu____4146 =
                  let uu____4153 =
                    let uu____4158 = type_of ea  in as_iarg uu____4158  in
                  [uu____4153]  in
                uu____4140 :: uu____4146  in
              uu____4123 :: uu____4133  in
            lid_as_constr FStar_Parser_Const.inr_lid
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
              uu____4122
         in
      let un cb trm =
        match trm with
        | Construct (fvar1,us,(a,uu____4211)::uu____4212::uu____4213::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inl_lid ->
            let uu____4248 = unembed ea cb a  in
            FStar_Util.bind_opt uu____4248
              (fun a1  -> FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
        | Construct (fvar1,us,(b,uu____4268)::uu____4269::uu____4270::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inr_lid ->
            let uu____4305 = unembed eb cb b  in
            FStar_Util.bind_opt uu____4305
              (fun b1  -> FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
        | uu____4322 -> FStar_Pervasives_Native.None  in
      let uu____4327 =
        let uu____4328 =
          let uu____4329 = let uu____4334 = type_of eb  in as_arg uu____4334
             in
          let uu____4335 =
            let uu____4342 =
              let uu____4347 = type_of ea  in as_arg uu____4347  in
            [uu____4342]  in
          uu____4329 :: uu____4335  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4328
         in
      mk_emb em un uu____4327
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____4415 -> FStar_Pervasives_Native.None  in
  let uu____4416 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____4416 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em cb l =
      let typ = let uu____4465 = type_of ea  in as_iarg uu____4465  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____4486 =
          let uu____4487 = as_arg tl1  in
          let uu____4492 =
            let uu____4499 =
              let uu____4504 = embed ea cb hd1  in as_arg uu____4504  in
            [uu____4499; typ]  in
          uu____4487 :: uu____4492  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____4486
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un cb trm =
      match trm with
      | Construct (fv,uu____4555,uu____4556) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____4576,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                               )::(uu____4579,FStar_Pervasives_Native.Some
                                                                   (FStar_Syntax_Syntax.Implicit
                                                                   uu____4580))::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____4607 = unembed ea cb hd1  in
          FStar_Util.bind_opt uu____4607
            (fun hd2  ->
               let uu____4619 = un cb tl1  in
               FStar_Util.bind_opt uu____4619
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____4641,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____4666 = unembed ea cb hd1  in
          FStar_Util.bind_opt uu____4666
            (fun hd2  ->
               let uu____4678 = un cb tl1  in
               FStar_Util.bind_opt uu____4678
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____4699 -> FStar_Pervasives_Native.None  in
    let uu____4702 =
      let uu____4703 =
        let uu____4704 = let uu____4709 = type_of ea  in as_arg uu____4709
           in
        [uu____4704]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____4703
       in
    mk_emb em un uu____4702
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em cb f =
        Lam
          ((fun tas  ->
              let uu____4811 =
                let uu____4814 = FStar_List.hd tas  in
                unembed ea cb uu____4814  in
              match uu____4811 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____4820 = f a  in embed eb cb uu____4820
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____4836  ->
                let uu____4839 = type_of eb  in as_arg uu____4839)],
            (Prims.parse_int "1"), FStar_Pervasives_Native.None)
         in
      let un cb lam =
        match lam with
        | Lam (ft,uu____4889,uu____4890,uu____4891) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____4941 =
                    let uu____4944 =
                      let uu____4945 =
                        let uu____4948 = embed ea cb x  in [uu____4948]  in
                      ft uu____4945  in
                    unembed eb cb uu____4944  in
                  match uu____4941 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____4958 -> FStar_Pervasives_Native.None  in
      let uu____4962 =
        let uu____4963 = type_of ea  in
        let uu____4964 = let uu____4965 = type_of eb  in as_iarg uu____4965
           in
        make_arrow1 uu____4963 uu____4964  in
      mk_emb em un uu____4962
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____4992 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4992 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____4997 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4997 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5002 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5002 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5007 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5007 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5012 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5012 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5017 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5017 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5022 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5022 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5027 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5027 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5032 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5032 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5040 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5041 =
          let uu____5042 =
            let uu____5047 =
              let uu____5048 = e_list e_string  in embed uu____5048 cb l  in
            as_arg uu____5047  in
          [uu____5042]  in
        mkFV uu____5040 [] uu____5041
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5070 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5071 =
          let uu____5072 =
            let uu____5077 =
              let uu____5078 = e_list e_string  in embed uu____5078 cb l  in
            as_arg uu____5077  in
          [uu____5072]  in
        mkFV uu____5070 [] uu____5071
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____5124,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____5140,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____5156,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____5172,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____5188,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____5204,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____5220,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____5236,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____5252,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____5268,(l,uu____5270)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____5289 =
          let uu____5294 = e_list e_string  in unembed uu____5294 cb l  in
        FStar_Util.bind_opt uu____5289
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____5314,(l,uu____5316)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____5335 =
          let uu____5340 = e_list e_string  in unembed uu____5340 cb l  in
        FStar_Util.bind_opt uu____5335
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____5359 ->
        ((let uu____5361 =
            let uu____5366 =
              let uu____5367 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____5367
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5366)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5361);
         FStar_Pervasives_Native.None)
     in
  let uu____5368 =
    let uu____5369 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____5369 [] []  in
  mk_emb em un uu____5368 
let bogus_cb :
  'Auu____5382 'Auu____5383 . 'Auu____5382 -> 'Auu____5383 -> 'Auu____5382 =
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
      let uu____5458 =
        let uu____5467 = e_list e  in unembed uu____5467 bogus_cb  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5458
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____5488  ->
    match uu____5488 with
    | (a,uu____5496) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____5511)::[]) when
             let uu____5528 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5528 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____5533 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cb n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____5575 = let uu____5582 = as_arg c  in [uu____5582]  in
      int_to_t2 uu____5575
  
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
          let uu____5635 = f a  in FStar_Pervasives_Native.Some uu____5635
      | uu____5636 -> FStar_Pervasives_Native.None
  
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
          let uu____5689 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____5689
      | uu____5690 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____5733 = FStar_List.map as_a args  in lift_unary f uu____5733
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____5787 = FStar_List.map as_a args  in
        lift_binary f uu____5787
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____5816 = f x  in embed e_int bogus_cb uu____5816)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  -> let uu____5842 = f x y  in embed e_int bogus_cb uu____5842)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____5861 = f x  in embed e_bool bogus_cb uu____5861)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____5887 = f x y  in embed e_bool bogus_cb uu____5887)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____5913 = f x y  in embed e_string bogus_cb uu____5913)
  
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
                let uu____6015 =
                  let uu____6024 = as_a a  in
                  let uu____6027 = as_b b  in (uu____6024, uu____6027)  in
                (match uu____6015 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____6042 =
                       let uu____6043 = f a1 b1  in embed_c uu____6043  in
                     FStar_Pervasives_Native.Some uu____6042
                 | uu____6044 -> FStar_Pervasives_Native.None)
            | uu____6053 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____6059 = e_list e_char  in
    let uu____6066 = FStar_String.list_of_string s  in
    embed uu____6059 bogus_cb uu____6066
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____6096 =
        let uu____6097 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____6097  in
      embed e_int bogus_cb uu____6096
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6129 = arg_as_string a1  in
        (match uu____6129 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6135 = arg_as_list e_string a2  in
             (match uu____6135 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6148 = embed e_string bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____6148
              | uu____6149 -> FStar_Pervasives_Native.None)
         | uu____6154 -> FStar_Pervasives_Native.None)
    | uu____6157 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____6163 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cb uu____6163
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cb (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cb true  in
      let fal = embed e_bool bogus_cb false  in
      match args with
      | (_univ,uu____6189)::(_typ,uu____6191)::(a1,uu____6193)::(a2,uu____6195)::[]
          ->
          let uu____6216 = eq_t a1 a2  in
          (match uu____6216 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____6221 -> FStar_Pervasives_Native.None)
      | uu____6222 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____6235)::(_typ,uu____6237)::(a1,uu____6239)::(a2,uu____6241)::[]
        ->
        let uu____6262 = eq_t a1 a2  in
        (match uu____6262 with
         | FStar_Syntax_Util.Equal  ->
             let uu____6265 = embed e_bool bogus_cb true  in
             FStar_Pervasives_Native.Some uu____6265
         | FStar_Syntax_Util.NotEqual  ->
             let uu____6266 = embed e_bool bogus_cb false  in
             FStar_Pervasives_Native.Some uu____6266
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____6267 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____6284 =
        let uu____6285 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____6285  in
      failwith uu____6284
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____6298)::[] ->
        let uu____6307 = unembed e_range bogus_cb a1  in
        (match uu____6307 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6313 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____6313
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6314 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6348 = arg_as_list e_char a1  in
        (match uu____6348 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6364 = arg_as_string a2  in
             (match uu____6364 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____6373 =
                    let uu____6374 = e_list e_string  in
                    embed uu____6374 bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____6373
              | uu____6381 -> FStar_Pervasives_Native.None)
         | uu____6384 -> FStar_Pervasives_Native.None)
    | uu____6390 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____6431 =
          let uu____6444 = arg_as_string a1  in
          let uu____6447 = arg_as_int a2  in
          let uu____6450 = arg_as_int a3  in
          (uu____6444, uu____6447, uu____6450)  in
        (match uu____6431 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___230_6477  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____6481 = embed e_string bogus_cb r  in
                       FStar_Pervasives_Native.Some uu____6481) ()
              with | uu___229_6483 -> FStar_Pervasives_Native.None)
         | uu____6486 -> FStar_Pervasives_Native.None)
    | uu____6499 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6558 =
          let uu____6579 = arg_as_string fn  in
          let uu____6582 = arg_as_int from_line  in
          let uu____6585 = arg_as_int from_col  in
          let uu____6588 = arg_as_int to_line  in
          let uu____6591 = arg_as_int to_col  in
          (uu____6579, uu____6582, uu____6585, uu____6588, uu____6591)  in
        (match uu____6558 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6622 =
                 let uu____6623 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6624 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6623 uu____6624  in
               let uu____6625 =
                 let uu____6626 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6627 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6626 uu____6627  in
               FStar_Range.mk_range fn1 uu____6622 uu____6625  in
             let uu____6628 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____6628
         | uu____6629 -> FStar_Pervasives_Native.None)
    | uu____6650 -> FStar_Pervasives_Native.None
  