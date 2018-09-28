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
    match projectee with | Var _0 -> true | uu____493 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____524 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____618 -> false
  
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
    match projectee with | Accu _0 -> true | uu____729 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____787 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____857 -> false 
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
    match projectee with | Constant _0 -> true | uu____913 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____927 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____941 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____954 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____981 -> false
  
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
    match projectee with | Refinement _0 -> true | uu____1069 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1125 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1143 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1183 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn,FStar_Syntax_Syntax.emb_typ)
                                     FStar_Pervasives_Native.tuple2)
       FStar_Util.either,t FStar_Common.thunk)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1273 -> false
  
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
    match projectee with | Tot _0 -> true | uu____1395 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1433 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1465 -> false
  
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStar_Syntax_Syntax.universes) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> comp_univs
  
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> effect_name
  
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> result_typ
  
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> effect_args
  
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> flags1
  
let (uu___is_TOTAL : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | TOTAL  -> true | uu____1584 -> false
  
let (uu___is_MLEFFECT : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1590 -> false
  
let (uu___is_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1596 -> false
  
let (uu___is_PARTIAL_RETURN : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1602 -> false
  
let (uu___is_SOMETRIVIAL : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1608 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____1614 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____1620 -> false
  
let (uu___is_LEMMA : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1626 -> false
  
let (uu___is_CPS : cflags -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____1632 -> false 
let (uu___is_DECREASES : cflags -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1639 -> false
  
let (__proj__DECREASES__item___0 : cflags -> t) =
  fun projectee  -> match projectee with | DECREASES _0 -> _0 
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_effect
  
let (__proj__Mkresidual_comp__item__residual_typ :
  residual_comp -> t FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_typ
  
let (__proj__Mkresidual_comp__item__residual_flags :
  residual_comp -> cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_flags
  
type arg = (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
type args =
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____1708 -> true | uu____1719 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1725,uu____1726) -> false | uu____1739 -> true
  
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
  fun uu___237_1868  ->
    if uu___237_1868
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___238_1874  ->
    if uu___238_1874
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
      | (FStar_Syntax_Util.NotEqual ,uu____1886) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1887,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1888) -> FStar_Syntax_Util.Unknown
      | (uu____1889,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1905 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1921),String (s2,uu____1923)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1931,uu____1932) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1967,Lam uu____1968) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2055 = eq_atom a1 a2  in
          eq_and uu____2055 (fun uu____2057  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2096 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2096
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2107 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2164  ->
                        match uu____2164 with
                        | ((a1,uu____2178),(a2,uu____2180)) ->
                            let uu____2189 = eq_t a1 a2  in
                            eq_inj acc uu____2189) FStar_Syntax_Util.Equal)
                uu____2107))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2229 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2229
          then
            let uu____2230 =
              let uu____2231 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2231  in
            eq_and uu____2230 (fun uu____2233  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2239 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2239
      | (Univ u1,Univ u2) ->
          let uu____2242 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2242
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2288 =
            let uu____2289 =
              let uu____2290 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2290  in
            let uu____2295 =
              let uu____2296 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2296  in
            eq_t uu____2289 uu____2295  in
          eq_and uu____2288
            (fun uu____2304  ->
               let uu____2305 =
                 let uu____2306 = mkAccuVar x  in r1 uu____2306  in
               let uu____2307 =
                 let uu____2308 = mkAccuVar x  in r2 uu____2308  in
               eq_t uu____2305 uu____2307)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2309,uu____2310) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2315,uu____2316) -> FStar_Syntax_Util.Unknown

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
          let uu____2397 = eq_arg x y  in
          eq_and uu____2397 (fun uu____2399  -> eq_args xs ys)
      | (uu____2400,uu____2401) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2437) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2439 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2439
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2460) ->
        let uu____2503 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2513 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2503 uu____2513
    | Accu (a,l) ->
        let uu____2528 =
          let uu____2529 = atom_to_string a  in
          let uu____2530 =
            let uu____2531 =
              let uu____2532 =
                let uu____2533 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2533  in
              Prims.strcat uu____2532 ")"  in
            Prims.strcat ") (" uu____2531  in
          Prims.strcat uu____2529 uu____2530  in
        Prims.strcat "Accu (" uu____2528
    | Construct (fv,us,l) ->
        let uu____2565 =
          let uu____2566 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2567 =
            let uu____2568 =
              let uu____2569 =
                let uu____2570 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2570  in
              let uu____2573 =
                let uu____2574 =
                  let uu____2575 =
                    let uu____2576 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2576  in
                  Prims.strcat uu____2575 "]"  in
                Prims.strcat "] [" uu____2574  in
              Prims.strcat uu____2569 uu____2573  in
            Prims.strcat ") [" uu____2568  in
          Prims.strcat uu____2566 uu____2567  in
        Prims.strcat "Construct (" uu____2565
    | FV (fv,us,l) ->
        let uu____2608 =
          let uu____2609 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2610 =
            let uu____2611 =
              let uu____2612 =
                let uu____2613 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2613  in
              let uu____2616 =
                let uu____2617 =
                  let uu____2618 =
                    let uu____2619 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2619  in
                  Prims.strcat uu____2618 "]"  in
                Prims.strcat "] [" uu____2617  in
              Prims.strcat uu____2612 uu____2616  in
            Prims.strcat ") [" uu____2611  in
          Prims.strcat uu____2609 uu____2610  in
        Prims.strcat "FV (" uu____2608
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2634 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2634
    | Type_t u ->
        let uu____2636 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2636
    | Arrow uu____2637 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2682 = t ()  in FStar_Pervasives_Native.fst uu____2682
           in
        let uu____2687 =
          let uu____2688 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2689 =
            let uu____2690 =
              let uu____2691 = t_to_string t1  in
              let uu____2692 =
                let uu____2693 =
                  let uu____2694 =
                    let uu____2695 =
                      let uu____2696 = mkAccuVar x1  in f uu____2696  in
                    t_to_string uu____2695  in
                  Prims.strcat uu____2694 "}"  in
                Prims.strcat "{" uu____2693  in
              Prims.strcat uu____2691 uu____2692  in
            Prims.strcat ":" uu____2690  in
          Prims.strcat uu____2688 uu____2689  in
        Prims.strcat "Refinement " uu____2687
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____2698 = t_to_string t  in Prims.strcat "Reflect " uu____2698
    | Quote uu____2699 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____2705) ->
        let uu____2722 =
          let uu____2723 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____2723  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____2722
    | Lazy (FStar_Util.Inr (uu____2724,et),uu____2726) ->
        let uu____2743 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____2743
    | Rec
        (uu____2744,uu____2745,l,uu____2747,uu____2748,uu____2749,uu____2750)
        ->
        let uu____2791 =
          let uu____2792 =
            let uu____2793 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2793  in
          Prims.strcat uu____2792 ")"  in
        Prims.strcat "Rec (" uu____2791

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2798 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2798
    | Match (t,uu____2800,uu____2801) ->
        let uu____2824 = t_to_string t  in Prims.strcat "Match " uu____2824

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2826 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2826 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2832 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2832 (FStar_String.concat " ")

type nbe_cbs =
  {
  iapp: t -> args -> t ;
  translate: FStar_Syntax_Syntax.term -> t }
let (__proj__Mknbe_cbs__item__iapp : nbe_cbs -> t -> args -> t) =
  fun projectee  -> match projectee with | { iapp; translate;_} -> iapp 
let (__proj__Mknbe_cbs__item__translate :
  nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun projectee  -> match projectee with | { iapp; translate;_} -> translate 
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
  fun projectee  -> match projectee with | { em; un; typ; emb_typ;_} -> em 
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee  -> match projectee with | { em; un; typ; emb_typ;_} -> un 
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee  -> match projectee with | { em; un; typ; emb_typ;_} -> typ 
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee  ->
    match projectee with | { em; un; typ; emb_typ;_} -> emb_typ
  
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
        let uu____3284 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3284 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3304 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3304 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3342  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3357  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____3399 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____3399
         then
           let uu____3419 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3419
         else ());
        (let uu____3421 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____3421
         then f ()
         else
           (let thunk = FStar_Common.mk_thunk f  in
            let li = let uu____3450 = FStar_Dyn.mkdyn x  in (uu____3450, et)
               in
            Lazy ((FStar_Util.Inr li), thunk)))
  
let lazy_unembed :
  'Auu____3517 'a .
    'Auu____3517 ->
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
              let uu____3568 = FStar_Common.force_thunk thunk  in
              f uu____3568
          | Lazy (FStar_Util.Inr (b,et'),thunk) ->
              let uu____3628 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____3628
              then
                let res =
                  let uu____3653 = FStar_Common.force_thunk thunk  in
                  f uu____3653  in
                ((let uu____3695 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____3695
                  then
                    let uu____3715 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____3716 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____3715
                      uu____3716
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____3721 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____3721
                  then
                    let uu____3741 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____3741
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____3743 ->
              let aopt = f x  in
              ((let uu____3748 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____3748
                then
                  let uu____3768 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____3768
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
  let uu____3831 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____3831 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____3864 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____3869 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____3864 uu____3869 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____3901 -> FStar_Pervasives_Native.None  in
  let uu____3902 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____3907 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____3902 uu____3907 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____3947 -> FStar_Pervasives_Native.None  in
  let uu____3949 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____3954 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____3949 uu____3954 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____3988)) -> FStar_Pervasives_Native.Some s1
    | uu____3989 -> FStar_Pervasives_Native.None  in
  let uu____3990 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____3995 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____3990 uu____3995 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4027 -> FStar_Pervasives_Native.None  in
  let uu____4028 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4033 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4028 uu____4033 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4053 =
        let uu____4060 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4060, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4053  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4082  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4083 =
                 let uu____4084 =
                   let uu____4089 = type_of ea  in as_iarg uu____4089  in
                 [uu____4084]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4083
           | FStar_Pervasives_Native.Some x ->
               let uu____4099 =
                 let uu____4100 =
                   let uu____4105 = embed ea cb x  in as_arg uu____4105  in
                 let uu____4106 =
                   let uu____4113 =
                     let uu____4118 = type_of ea  in as_iarg uu____4118  in
                   [uu____4113]  in
                 uu____4100 :: uu____4106  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4099)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4185)::uu____4186::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4213 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4213
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4222 -> FStar_Pervasives_Native.None)
       in
    let uu____4225 =
      let uu____4226 =
        let uu____4227 = let uu____4232 = type_of ea  in as_arg uu____4232
           in
        [uu____4227]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4226
       in
    mk_emb em un uu____4225 etyp
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4278 =
          let uu____4285 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4285, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4278  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4313  ->
             let uu____4314 =
               let uu____4315 =
                 let uu____4320 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4320  in
               let uu____4321 =
                 let uu____4328 =
                   let uu____4333 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4333  in
                 let uu____4334 =
                   let uu____4341 =
                     let uu____4346 = type_of eb  in as_iarg uu____4346  in
                   let uu____4347 =
                     let uu____4354 =
                       let uu____4359 = type_of ea  in as_iarg uu____4359  in
                     [uu____4354]  in
                   uu____4341 :: uu____4347  in
                 uu____4328 :: uu____4334  in
               uu____4315 :: uu____4321  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4314)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____4427)::(a,uu____4429)::uu____4430::uu____4431::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____4470 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4470
                   (fun a1  ->
                      let uu____4480 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____4480
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____4493 -> FStar_Pervasives_Native.None)
         in
      let uu____4498 =
        let uu____4499 =
          let uu____4500 = let uu____4505 = type_of eb  in as_arg uu____4505
             in
          let uu____4506 =
            let uu____4513 =
              let uu____4518 = type_of ea  in as_arg uu____4518  in
            [uu____4513]  in
          uu____4500 :: uu____4506  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4499
         in
      mk_emb em un uu____4498 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4570 =
          let uu____4577 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4577, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4570  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____4606  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____4608 =
                   let uu____4609 =
                     let uu____4614 = embed ea cb a  in as_arg uu____4614  in
                   let uu____4615 =
                     let uu____4622 =
                       let uu____4627 = type_of eb  in as_iarg uu____4627  in
                     let uu____4628 =
                       let uu____4635 =
                         let uu____4640 = type_of ea  in as_iarg uu____4640
                          in
                       [uu____4635]  in
                     uu____4622 :: uu____4628  in
                   uu____4609 :: uu____4615  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4608
             | FStar_Util.Inr b ->
                 let uu____4658 =
                   let uu____4659 =
                     let uu____4664 = embed eb cb b  in as_arg uu____4664  in
                   let uu____4665 =
                     let uu____4672 =
                       let uu____4677 = type_of eb  in as_iarg uu____4677  in
                     let uu____4678 =
                       let uu____4685 =
                         let uu____4690 = type_of ea  in as_iarg uu____4690
                          in
                       [uu____4685]  in
                     uu____4672 :: uu____4678  in
                   uu____4659 :: uu____4665  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4658)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____4752)::uu____4753::uu____4754::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____4789 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4789
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____4805)::uu____4806::uu____4807::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____4842 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____4842
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____4855 -> FStar_Pervasives_Native.None)
         in
      let uu____4860 =
        let uu____4861 =
          let uu____4862 = let uu____4867 = type_of eb  in as_arg uu____4867
             in
          let uu____4868 =
            let uu____4875 =
              let uu____4880 = type_of ea  in as_arg uu____4880  in
            [uu____4875]  in
          uu____4862 :: uu____4868  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4861
         in
      mk_emb em un uu____4860 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____4928 -> FStar_Pervasives_Native.None  in
  let uu____4929 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____4934 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____4929 uu____4934 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____4954 =
        let uu____4961 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____4961, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4954  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____4985  ->
           let typ = let uu____4987 = type_of ea  in as_iarg uu____4987  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5008 =
               let uu____5009 = as_arg tl1  in
               let uu____5014 =
                 let uu____5021 =
                   let uu____5026 = embed ea cb hd1  in as_arg uu____5026  in
                 [uu____5021; typ]  in
               uu____5009 :: uu____5014  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5008
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5074,uu____5075) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5095,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5098,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5099))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5126 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5126
                 (fun hd2  ->
                    let uu____5134 = un cb tl1  in
                    FStar_Util.bind_opt uu____5134
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5150,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5175 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5175
                 (fun hd2  ->
                    let uu____5183 = un cb tl1  in
                    FStar_Util.bind_opt uu____5183
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5198 -> FStar_Pervasives_Native.None)
       in
    let uu____5201 =
      let uu____5202 =
        let uu____5203 = let uu____5208 = type_of ea  in as_arg uu____5208
           in
        [uu____5203]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5202
       in
    mk_emb em un uu____5201 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5277  ->
             Lam
               ((fun tas  ->
                   let uu____5306 =
                     let uu____5309 = FStar_List.hd tas  in
                     unembed ea cb uu____5309  in
                   match uu____5306 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5311 = f a  in embed eb cb uu____5311
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____5323  ->
                     let uu____5326 = type_of eb  in as_arg uu____5326)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____5383 =
                 let uu____5386 =
                   let uu____5387 =
                     let uu____5388 =
                       let uu____5393 = embed ea cb x  in as_arg uu____5393
                        in
                     [uu____5388]  in
                   cb.iapp lam1 uu____5387  in
                 unembed eb cb uu____5386  in
               match uu____5383 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____5406 =
        let uu____5407 = type_of ea  in
        let uu____5408 = let uu____5409 = type_of eb  in as_iarg uu____5409
           in
        make_arrow1 uu____5407 uu____5408  in
      mk_emb em un uu____5406 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5426 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5426 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5431 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5431 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5436 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5436 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5441 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5441 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5446 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5446 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5451 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5451 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5456 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5456 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5461 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5461 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5466 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5466 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5474 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5475 =
          let uu____5476 =
            let uu____5481 =
              let uu____5482 = e_list e_string  in embed uu____5482 cb l  in
            as_arg uu____5481  in
          [uu____5476]  in
        mkFV uu____5474 [] uu____5475
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5500 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5501 =
          let uu____5502 =
            let uu____5507 =
              let uu____5508 = e_list e_string  in embed uu____5508 cb l  in
            as_arg uu____5507  in
          [uu____5502]  in
        mkFV uu____5500 [] uu____5501
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____5526 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5527 =
          let uu____5528 =
            let uu____5533 =
              let uu____5534 = e_list e_string  in embed uu____5534 cb l  in
            as_arg uu____5533  in
          [uu____5528]  in
        mkFV uu____5526 [] uu____5527
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____5565,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____5581,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____5597,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____5613,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____5629,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____5645,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____5661,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____5677,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____5693,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____5709,(l,uu____5711)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____5730 =
          let uu____5735 = e_list e_string  in unembed uu____5735 cb l  in
        FStar_Util.bind_opt uu____5730
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____5751,(l,uu____5753)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____5772 =
          let uu____5777 = e_list e_string  in unembed uu____5777 cb l  in
        FStar_Util.bind_opt uu____5772
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____5793,(l,uu____5795)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____5814 =
          let uu____5819 = e_list e_string  in unembed uu____5819 cb l  in
        FStar_Util.bind_opt uu____5814
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_3  -> FStar_Pervasives_Native.Some _0_3)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____5834 ->
        ((let uu____5836 =
            let uu____5841 =
              let uu____5842 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____5842
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5841)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5836);
         FStar_Pervasives_Native.None)
     in
  let uu____5843 =
    let uu____5844 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____5844 [] []  in
  let uu____5849 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____5843 uu____5849 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____5857  -> failwith "bogus_cbs translate")
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
      let uu____5922 =
        let uu____5931 = e_list e  in unembed uu____5931 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5922
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____5952  ->
    match uu____5952 with
    | (a,uu____5960) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____5975)::[]) when
             let uu____5992 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5992 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____5997 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6039 = let uu____6046 = as_arg c  in [uu____6046]  in
      int_to_t2 uu____6039
  
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
          let uu____6099 = f a  in FStar_Pervasives_Native.Some uu____6099
      | uu____6100 -> FStar_Pervasives_Native.None
  
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
          let uu____6153 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6153
      | uu____6154 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6197 = FStar_List.map as_a args  in lift_unary f uu____6197
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6251 = FStar_List.map as_a args  in
        lift_binary f uu____6251
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6280 = f x  in embed e_int bogus_cbs uu____6280)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____6306 = f x y  in embed e_int bogus_cbs uu____6306)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6325 = f x  in embed e_bool bogus_cbs uu____6325)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6351 = f x y  in embed e_bool bogus_cbs uu____6351)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____6377 = f x y  in embed e_string bogus_cbs uu____6377)
  
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
                let uu____6479 =
                  let uu____6488 = as_a a  in
                  let uu____6491 = as_b b  in (uu____6488, uu____6491)  in
                (match uu____6479 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____6506 =
                       let uu____6507 = f a1 b1  in embed_c uu____6507  in
                     FStar_Pervasives_Native.Some uu____6506
                 | uu____6508 -> FStar_Pervasives_Native.None)
            | uu____6517 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____6523 = e_list e_char  in
    let uu____6530 = FStar_String.list_of_string s  in
    embed uu____6523 bogus_cbs uu____6530
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____6560 =
        let uu____6561 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____6561  in
      embed e_int bogus_cbs uu____6560
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6593 = arg_as_string a1  in
        (match uu____6593 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6599 = arg_as_list e_string a2  in
             (match uu____6599 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6612 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____6612
              | uu____6613 -> FStar_Pervasives_Native.None)
         | uu____6618 -> FStar_Pervasives_Native.None)
    | uu____6621 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____6627 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____6627
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cbs (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cbs true  in
      let fal = embed e_bool bogus_cbs false  in
      match args with
      | (_typ,uu____6653)::(a1,uu____6655)::(a2,uu____6657)::[] ->
          let uu____6674 = eq_t a1 a2  in
          (match uu____6674 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____6679 -> FStar_Pervasives_Native.None)
      | uu____6680 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____6693)::(_typ,uu____6695)::(a1,uu____6697)::(a2,uu____6699)::[]
        ->
        let uu____6720 = eq_t a1 a2  in
        (match uu____6720 with
         | FStar_Syntax_Util.Equal  ->
             let uu____6723 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____6723
         | FStar_Syntax_Util.NotEqual  ->
             let uu____6724 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____6724
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____6725 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____6738)::(_v,uu____6740)::(t1,uu____6742)::(t2,uu____6744)::
        (a1,uu____6746)::(a2,uu____6748)::[] ->
        let uu____6777 =
          let uu____6778 = eq_t t1 t2  in
          let uu____6779 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____6778 uu____6779  in
        (match uu____6777 with
         | FStar_Syntax_Util.Equal  ->
             let uu____6782 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____6782
         | FStar_Syntax_Util.NotEqual  ->
             let uu____6783 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____6783
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____6784 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____6801 =
        let uu____6802 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____6802  in
      failwith uu____6801
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____6815)::[] ->
        let uu____6824 = unembed e_range bogus_cbs a1  in
        (match uu____6824 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6830 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____6830
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6831 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6865 = arg_as_list e_char a1  in
        (match uu____6865 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6881 = arg_as_string a2  in
             (match uu____6881 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____6890 =
                    let uu____6891 = e_list e_string  in
                    embed uu____6891 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____6890
              | uu____6898 -> FStar_Pervasives_Native.None)
         | uu____6901 -> FStar_Pervasives_Native.None)
    | uu____6907 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____6948 =
          let uu____6961 = arg_as_string a1  in
          let uu____6964 = arg_as_int a2  in
          let uu____6967 = arg_as_int a3  in
          (uu____6961, uu____6964, uu____6967)  in
        (match uu____6948 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___240_6994  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____6998 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____6998) ()
              with | uu___239_7000 -> FStar_Pervasives_Native.None)
         | uu____7003 -> FStar_Pervasives_Native.None)
    | uu____7016 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7075 =
          let uu____7096 = arg_as_string fn  in
          let uu____7099 = arg_as_int from_line  in
          let uu____7102 = arg_as_int from_col  in
          let uu____7105 = arg_as_int to_line  in
          let uu____7108 = arg_as_int to_col  in
          (uu____7096, uu____7099, uu____7102, uu____7105, uu____7108)  in
        (match uu____7075 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7139 =
                 let uu____7140 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7141 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7140 uu____7141  in
               let uu____7142 =
                 let uu____7143 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7144 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7143 uu____7144  in
               FStar_Range.mk_range fn1 uu____7139 uu____7142  in
             let uu____7145 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7145
         | uu____7146 -> FStar_Pervasives_Native.None)
    | uu____7167 -> FStar_Pervasives_Native.None
  
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
                let uu____7254 = FStar_List.splitAt n_tvars args  in
                match uu____7254 with
                | (_tvar_args,rest_args) ->
                    let uu____7303 = FStar_List.hd rest_args  in
                    (match uu____7303 with
                     | (x,uu____7315) ->
                         let uu____7316 = unembed ea cb x  in
                         FStar_Util.map_opt uu____7316
                           (fun x1  ->
                              let uu____7322 = f x1  in
                              embed eb cb uu____7322))
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
                  let uu____7428 = FStar_List.splitAt n_tvars args  in
                  match uu____7428 with
                  | (_tvar_args,rest_args) ->
                      let uu____7477 = FStar_List.hd rest_args  in
                      (match uu____7477 with
                       | (x,uu____7489) ->
                           let uu____7490 =
                             let uu____7495 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____7495  in
                           (match uu____7490 with
                            | (y,uu____7513) ->
                                let uu____7514 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____7514
                                  (fun x1  ->
                                     let uu____7520 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____7520
                                       (fun y1  ->
                                          let uu____7526 =
                                            let uu____7527 = f x1 y1  in
                                            embed ec cb uu____7527  in
                                          FStar_Pervasives_Native.Some
                                            uu____7526))))
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
                    let uu____7652 = FStar_List.splitAt n_tvars args  in
                    match uu____7652 with
                    | (_tvar_args,rest_args) ->
                        let uu____7701 = FStar_List.hd rest_args  in
                        (match uu____7701 with
                         | (x,uu____7713) ->
                             let uu____7714 =
                               let uu____7719 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____7719  in
                             (match uu____7714 with
                              | (y,uu____7737) ->
                                  let uu____7738 =
                                    let uu____7743 =
                                      let uu____7750 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____7750  in
                                    FStar_List.hd uu____7743  in
                                  (match uu____7738 with
                                   | (z,uu____7772) ->
                                       let uu____7773 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____7773
                                         (fun x1  ->
                                            let uu____7779 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____7779
                                              (fun y1  ->
                                                 let uu____7785 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____7785
                                                   (fun z1  ->
                                                      let uu____7791 =
                                                        let uu____7792 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____7792
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____7791))))))
                     in
                  f_wrapped
  