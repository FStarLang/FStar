open Prims
type var = FStar_Syntax_Syntax.bv
type sort = Prims.int
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStar_BigInt.t 
  | String of (Prims.string * FStar_Range.range) 
  | Char of FStar_Char.char 
  | Range of FStar_Range.range 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____57 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____70 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____92 -> false 
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____116 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____151 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____173 -> false
  
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee  -> match projectee with | Range _0 -> _0 
type atom =
  | Var of var 
  | Match of (t * (unit -> FStar_Syntax_Syntax.branch Prims.list)) 
  | UnreducedLet of (var * t FStar_Thunk.t * t FStar_Thunk.t * t
  FStar_Thunk.t * FStar_Syntax_Syntax.letbinding) 
  | UnreducedLetRec of ((var * t * t) Prims.list * t *
  FStar_Syntax_Syntax.letbinding Prims.list) 
and t =
  | Lam of ((t Prims.list -> t) *
  (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list * Prims.int *
  (t Prims.list -> residual_comp) FStar_Pervasives_Native.option) 
  | Accu of (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Construct of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | FV of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list *
  (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
  | Arrow of ((t Prims.list -> comp) *
  (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list) 
  | Refinement of ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual))) 
  | Reflect of t 
  | Quote of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo) 
  | Lazy of
  ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                   FStar_Syntax_Syntax.emb_typ))
  FStar_Util.either * t FStar_Thunk.t) 
  | TopLevelLet of (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
  FStar_Syntax_Syntax.aqual) Prims.list) 
  | TopLevelRec of (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | LocalLetRec of (Prims.int * FStar_Syntax_Syntax.letbinding *
  FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
  FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool Prims.list) 
and comp =
  | Tot of (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  
  | GTot of (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  
  | Comp of comp_typ 
and comp_typ =
  {
  comp_univs: FStar_Syntax_Syntax.universes ;
  effect_name: FStar_Ident.lident ;
  result_typ: t ;
  effect_args: (t * FStar_Syntax_Syntax.aqual) Prims.list ;
  flags: cflag Prims.list }
and cflag =
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
  residual_flags: cflag Prims.list }
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____678 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____706 -> false
  
let (__proj__Match__item___0 :
  atom -> (t * (unit -> FStar_Syntax_Syntax.branch Prims.list))) =
  fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLet _0 -> true | uu____768 -> false
  
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStar_Thunk.t * t FStar_Thunk.t * t FStar_Thunk.t *
      FStar_Syntax_Syntax.letbinding))
  = fun projectee  -> match projectee with | UnreducedLet _0 -> _0 
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLetRec _0 -> true | uu____851 -> false
  
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee  -> match projectee with | UnreducedLetRec _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____950 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (t Prims.list -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____1075 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____1138 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____1213 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1274 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1293 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1312 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1330 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1362 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1455 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1516 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1539 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1584 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_TopLevelLet : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____1658 -> false
  
let (__proj__TopLevelLet__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_TopLevelRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelRec _0 -> true | uu____1734 -> false
  
let (__proj__TopLevelRec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelRec _0 -> _0 
let (uu___is_LocalLetRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalLetRec _0 -> true | uu____1836 -> false
  
let (__proj__LocalLetRec__item___0 :
  t ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee  -> match projectee with | LocalLetRec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1948 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1991 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____2028 -> false
  
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStar_Syntax_Syntax.universes) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        comp_univs
  
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_name
  
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        result_typ
  
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ -> (t * FStar_Syntax_Syntax.aqual) Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_args
  
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} -> flags
  
let (uu___is_TOTAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | TOTAL  -> true | uu____2157 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____2168 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____2179 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____2190 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____2201 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____2212 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____2223 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____2234 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____2245 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____2257 -> false
  
let (__proj__DECREASES__item___0 : cflag -> t) =
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
  residual_comp -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_flags
  
type arg = (t * FStar_Syntax_Syntax.aqual)
type args = (t * FStar_Syntax_Syntax.aqual) Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____2333 -> true | uu____2345 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____2355,uu____2356) -> false | uu____2370 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> FV (i, us, ts) 
let (mkAccuVar : var -> t) = fun v1  -> Accu ((Var v1), []) 
let (mkAccuMatch : t -> (unit -> FStar_Syntax_Syntax.branch Prims.list) -> t)
  = fun s  -> fun bs  -> Accu ((Match (s, bs)), []) 
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___0_2485  ->
    if uu___0_2485
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2496  ->
    if uu___1_2496
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
      | (FStar_Syntax_Util.NotEqual ,uu____2512) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2513,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2514) -> FStar_Syntax_Util.Unknown
      | (uu____2515,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2532 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2552),String (s2,uu____2554)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2567,uu____2568) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2604,Lam uu____2605) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2698 = eq_atom a1 a2  in
          eq_and uu____2698 (fun uu____2700  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2739 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2739
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2755 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2812  ->
                        match uu____2812 with
                        | ((a1,uu____2826),(a2,uu____2828)) ->
                            let uu____2837 = eq_t a1 a2  in
                            eq_inj acc uu____2837) FStar_Syntax_Util.Equal)
                uu____2755))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2878 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2878
          then
            let uu____2881 =
              let uu____2882 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2882  in
            eq_and uu____2881 (fun uu____2885  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2892 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2892
      | (Univ u1,Univ u2) ->
          let uu____2896 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2896
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2943 =
            let uu____2944 =
              let uu____2945 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2945  in
            let uu____2950 =
              let uu____2951 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2951  in
            eq_t uu____2944 uu____2950  in
          eq_and uu____2943
            (fun uu____2959  ->
               let uu____2960 =
                 let uu____2961 = mkAccuVar x  in r1 uu____2961  in
               let uu____2962 =
                 let uu____2963 = mkAccuVar x  in r2 uu____2963  in
               eq_t uu____2960 uu____2962)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2964,uu____2965) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2970,uu____2971) -> FStar_Syntax_Util.Unknown

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
          let uu____3052 = eq_arg x y  in
          eq_and uu____3052 (fun uu____3054  -> eq_args xs ys)
      | (uu____3055,uu____3056) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____3103) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____3108 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____3108
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____3127) ->
        let uu____3176 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____3187 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____3176 uu____3187
    | Accu (a,l) ->
        let uu____3204 =
          let uu____3206 = atom_to_string a  in
          let uu____3208 =
            let uu____3210 =
              let uu____3212 =
                let uu____3214 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____3214  in
              FStar_String.op_Hat uu____3212 ")"  in
            FStar_String.op_Hat ") (" uu____3210  in
          FStar_String.op_Hat uu____3206 uu____3208  in
        FStar_String.op_Hat "Accu (" uu____3204
    | Construct (fv,us,l) ->
        let uu____3252 =
          let uu____3254 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3256 =
            let uu____3258 =
              let uu____3260 =
                let uu____3262 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3262  in
              let uu____3268 =
                let uu____3270 =
                  let uu____3272 =
                    let uu____3274 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3274  in
                  FStar_String.op_Hat uu____3272 "]"  in
                FStar_String.op_Hat "] [" uu____3270  in
              FStar_String.op_Hat uu____3260 uu____3268  in
            FStar_String.op_Hat ") [" uu____3258  in
          FStar_String.op_Hat uu____3254 uu____3256  in
        FStar_String.op_Hat "Construct (" uu____3252
    | FV (fv,us,l) ->
        let uu____3313 =
          let uu____3315 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3317 =
            let uu____3319 =
              let uu____3321 =
                let uu____3323 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3323  in
              let uu____3329 =
                let uu____3331 =
                  let uu____3333 =
                    let uu____3335 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3335  in
                  FStar_String.op_Hat uu____3333 "]"  in
                FStar_String.op_Hat "] [" uu____3331  in
              FStar_String.op_Hat uu____3321 uu____3329  in
            FStar_String.op_Hat ") [" uu____3319  in
          FStar_String.op_Hat uu____3315 uu____3317  in
        FStar_String.op_Hat "FV (" uu____3313
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3357 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3357
    | Type_t u ->
        let uu____3361 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3361
    | Arrow uu____3364 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3410 = t ()  in FStar_Pervasives_Native.fst uu____3410
           in
        let uu____3415 =
          let uu____3417 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3419 =
            let uu____3421 =
              let uu____3423 = t_to_string t1  in
              let uu____3425 =
                let uu____3427 =
                  let uu____3429 =
                    let uu____3431 =
                      let uu____3432 = mkAccuVar x1  in f uu____3432  in
                    t_to_string uu____3431  in
                  FStar_String.op_Hat uu____3429 "}"  in
                FStar_String.op_Hat "{" uu____3427  in
              FStar_String.op_Hat uu____3423 uu____3425  in
            FStar_String.op_Hat ":" uu____3421  in
          FStar_String.op_Hat uu____3417 uu____3419  in
        FStar_String.op_Hat "Refinement " uu____3415
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____3439 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____3439
    | Quote uu____3442 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3449) ->
        let uu____3466 =
          let uu____3468 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3468  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3466
    | Lazy (FStar_Util.Inr (uu____3470,et),uu____3472) ->
        let uu____3489 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3489
    | LocalLetRec
        (uu____3492,l,uu____3494,uu____3495,uu____3496,uu____3497,uu____3498)
        ->
        let uu____3529 =
          let uu____3531 = FStar_Syntax_Print.lbs_to_string [] (true, [l])
             in
          FStar_String.op_Hat uu____3531 ")"  in
        FStar_String.op_Hat "LocalLetRec (" uu____3529
    | TopLevelLet (lb,uu____3540,uu____3541) ->
        let uu____3556 =
          let uu____3558 =
            let uu____3560 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3560  in
          FStar_String.op_Hat uu____3558 ")"  in
        FStar_String.op_Hat "TopLevelLet (" uu____3556
    | TopLevelRec (lb,uu____3564,uu____3565,uu____3566) ->
        let uu____3587 =
          let uu____3589 =
            let uu____3591 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3591  in
          FStar_String.op_Hat uu____3589 ")"  in
        FStar_String.op_Hat "TopLevelRec (" uu____3587

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3597 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3597
    | Match (t,uu____3601) ->
        let uu____3612 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3612
    | UnreducedLet (var,typ,def,body,lb) ->
        let uu____3632 =
          let uu____3634 = FStar_Syntax_Print.lbs_to_string [] (false, [lb])
             in
          FStar_String.op_Hat uu____3634 " in ...)"  in
        FStar_String.op_Hat "UnreducedLet(" uu____3632
    | UnreducedLetRec (uu____3642,body,lbs) ->
        let uu____3665 =
          let uu____3667 = FStar_Syntax_Print.lbs_to_string [] (true, lbs)
             in
          let uu____3673 =
            let uu____3675 =
              let uu____3677 = t_to_string body  in
              FStar_String.op_Hat uu____3677 ")"  in
            FStar_String.op_Hat " in " uu____3675  in
          FStar_String.op_Hat uu____3667 uu____3673  in
        FStar_String.op_Hat "UnreducedLetRec(" uu____3665

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3689 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3689 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3702 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3702 (FStar_String.concat " ")
  
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
        let uu____4173 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____4173 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____4194 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____4194 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____4235  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____4250  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____4293 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____4293
         then
           let uu____4317 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4317
         else ());
        (let uu____4322 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4322
         then f ()
         else
           (let thunk1 = FStar_Thunk.mk f  in
            let li = let uu____4356 = FStar_Dyn.mkdyn x  in (uu____4356, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____4384 'a .
    'Auu____4384 ->
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
          | Lazy (FStar_Util.Inl li,thunk1) ->
              let uu____4435 = FStar_Thunk.force thunk1  in f uu____4435
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____4455 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4455
              then
                let res =
                  let uu____4484 = FStar_Thunk.force thunk1  in f uu____4484
                   in
                ((let uu____4486 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4486
                  then
                    let uu____4510 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4512 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4510
                      uu____4512
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____4521 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4521
                  then
                    let uu____4545 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4545
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____4550 ->
              let aopt = f x  in
              ((let uu____4555 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4555
                then
                  let uu____4579 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4579
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
  let uu____4647 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4647 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____4681 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4686 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4681 uu____4686 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4727 -> FStar_Pervasives_Native.None  in
  let uu____4729 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____4734 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4729 uu____4734 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4776 -> FStar_Pervasives_Native.None  in
  let uu____4778 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____4783 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____4778 uu____4783 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____4825)) -> FStar_Pervasives_Native.Some s1
    | uu____4829 -> FStar_Pervasives_Native.None  in
  let uu____4831 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____4836 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____4831 uu____4836 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4871 -> FStar_Pervasives_Native.None  in
  let uu____4872 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4877 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4872 uu____4877 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4898 =
        let uu____4906 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4906, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4898  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4931  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4932 =
                 let uu____4933 =
                   let uu____4938 = type_of ea  in as_iarg uu____4938  in
                 [uu____4933]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4932
           | FStar_Pervasives_Native.Some x ->
               let uu____4948 =
                 let uu____4949 =
                   let uu____4954 = embed ea cb x  in as_arg uu____4954  in
                 let uu____4955 =
                   let uu____4962 =
                     let uu____4967 = type_of ea  in as_iarg uu____4967  in
                   [uu____4962]  in
                 uu____4949 :: uu____4955  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4948)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____5034)::uu____5035::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____5062 = unembed ea cb a  in
               FStar_Util.bind_opt uu____5062
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____5071 -> FStar_Pervasives_Native.None)
       in
    let uu____5074 =
      let uu____5075 =
        let uu____5076 = let uu____5081 = type_of ea  in as_arg uu____5081
           in
        [uu____5076]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____5075
       in
    mk_emb em un uu____5074 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5128 =
          let uu____5136 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____5136, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5128  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____5167  ->
             let uu____5168 =
               let uu____5169 =
                 let uu____5174 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____5174  in
               let uu____5175 =
                 let uu____5182 =
                   let uu____5187 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____5187  in
                 let uu____5188 =
                   let uu____5195 =
                     let uu____5200 = type_of eb  in as_iarg uu____5200  in
                   let uu____5201 =
                     let uu____5208 =
                       let uu____5213 = type_of ea  in as_iarg uu____5213  in
                     [uu____5208]  in
                   uu____5195 :: uu____5201  in
                 uu____5182 :: uu____5188  in
               uu____5169 :: uu____5175  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____5168)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____5281)::(a,uu____5283)::uu____5284::uu____5285::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5324 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5324
                   (fun a1  ->
                      let uu____5334 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____5334
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____5347 -> FStar_Pervasives_Native.None)
         in
      let uu____5352 =
        let uu____5353 =
          let uu____5354 = let uu____5359 = type_of eb  in as_arg uu____5359
             in
          let uu____5360 =
            let uu____5367 =
              let uu____5372 = type_of ea  in as_arg uu____5372  in
            [uu____5367]  in
          uu____5354 :: uu____5360  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5353
         in
      mk_emb em un uu____5352 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5425 =
          let uu____5433 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5433, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5425  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5465  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____5467 =
                   let uu____5468 =
                     let uu____5473 = embed ea cb a  in as_arg uu____5473  in
                   let uu____5474 =
                     let uu____5481 =
                       let uu____5486 = type_of eb  in as_iarg uu____5486  in
                     let uu____5487 =
                       let uu____5494 =
                         let uu____5499 = type_of ea  in as_iarg uu____5499
                          in
                       [uu____5494]  in
                     uu____5481 :: uu____5487  in
                   uu____5468 :: uu____5474  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5467
             | FStar_Util.Inr b ->
                 let uu____5517 =
                   let uu____5518 =
                     let uu____5523 = embed eb cb b  in as_arg uu____5523  in
                   let uu____5524 =
                     let uu____5531 =
                       let uu____5536 = type_of eb  in as_iarg uu____5536  in
                     let uu____5537 =
                       let uu____5544 =
                         let uu____5549 = type_of ea  in as_iarg uu____5549
                          in
                       [uu____5544]  in
                     uu____5531 :: uu____5537  in
                   uu____5518 :: uu____5524  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5517)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____5611)::uu____5612::uu____5613::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5648 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5648
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____5664)::uu____5665::uu____5666::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5701 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____5701
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____5714 -> FStar_Pervasives_Native.None)
         in
      let uu____5719 =
        let uu____5720 =
          let uu____5721 = let uu____5726 = type_of eb  in as_arg uu____5726
             in
          let uu____5727 =
            let uu____5734 =
              let uu____5739 = type_of ea  in as_arg uu____5739  in
            [uu____5734]  in
          uu____5721 :: uu____5727  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5720
         in
      mk_emb em un uu____5719 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5788 -> FStar_Pervasives_Native.None  in
  let uu____5789 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5794 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5789 uu____5794 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5815 =
        let uu____5823 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5823, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5815  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5850  ->
           let typ = let uu____5852 = type_of ea  in as_iarg uu____5852  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5873 =
               let uu____5874 = as_arg tl1  in
               let uu____5879 =
                 let uu____5886 =
                   let uu____5891 = embed ea cb hd1  in as_arg uu____5891  in
                 [uu____5886; typ]  in
               uu____5874 :: uu____5879  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5873
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5939,uu____5940) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5960,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5963,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5964))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5992 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5992
                 (fun hd2  ->
                    let uu____6000 = un cb tl1  in
                    FStar_Util.bind_opt uu____6000
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____6016,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6041 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____6041
                 (fun hd2  ->
                    let uu____6049 = un cb tl1  in
                    FStar_Util.bind_opt uu____6049
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____6064 -> FStar_Pervasives_Native.None)
       in
    let uu____6067 =
      let uu____6068 =
        let uu____6069 = let uu____6074 = type_of ea  in as_arg uu____6074
           in
        [uu____6069]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____6068
       in
    mk_emb em un uu____6067 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____6147  ->
             Lam
               ((fun tas  ->
                   let uu____6179 =
                     let uu____6182 = FStar_List.hd tas  in
                     unembed ea cb uu____6182  in
                   match uu____6179 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____6184 = f a  in embed eb cb uu____6184
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____6197  ->
                     let uu____6200 = type_of eb  in as_arg uu____6200)],
                 Prims.int_one, FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____6260 =
                 let uu____6263 =
                   let uu____6264 =
                     let uu____6265 =
                       let uu____6270 = embed ea cb x  in as_arg uu____6270
                        in
                     [uu____6265]  in
                   cb.iapp lam1 uu____6264  in
                 unembed eb cb uu____6263  in
               match uu____6260 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____6284 =
        let uu____6285 = type_of ea  in
        let uu____6286 = let uu____6287 = type_of eb  in as_iarg uu____6287
           in
        make_arrow1 uu____6285 uu____6286  in
      mk_emb em un uu____6284 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____6305 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6305 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____6310 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6310 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____6315 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6315 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____6320 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6320 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____6325 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6325 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____6330 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6330 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____6335 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6335 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____6340 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6340 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____6345 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6345 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6354 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6355 =
          let uu____6356 =
            let uu____6361 =
              let uu____6362 = e_list e_string  in embed uu____6362 cb l  in
            as_arg uu____6361  in
          [uu____6356]  in
        mkFV uu____6354 [] uu____6355
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6384 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6385 =
          let uu____6386 =
            let uu____6391 =
              let uu____6392 = e_list e_string  in embed uu____6392 cb l  in
            as_arg uu____6391  in
          [uu____6386]  in
        mkFV uu____6384 [] uu____6385
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6414 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6415 =
          let uu____6416 =
            let uu____6421 =
              let uu____6422 = e_list e_string  in embed uu____6422 cb l  in
            as_arg uu____6421  in
          [uu____6416]  in
        mkFV uu____6414 [] uu____6415
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____6456,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6472,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6488,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6504,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6520,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6536,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6552,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6568,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6584,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6600,(l,uu____6602)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6621 =
          let uu____6627 = e_list e_string  in unembed uu____6627 cb l  in
        FStar_Util.bind_opt uu____6621
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6647  -> FStar_Pervasives_Native.Some _6647)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6649,(l,uu____6651)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6670 =
          let uu____6676 = e_list e_string  in unembed uu____6676 cb l  in
        FStar_Util.bind_opt uu____6670
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6696  -> FStar_Pervasives_Native.Some _6696)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____6698,(l,uu____6700)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6719 =
          let uu____6725 = e_list e_string  in unembed uu____6725 cb l  in
        FStar_Util.bind_opt uu____6719
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6745  -> FStar_Pervasives_Native.Some _6745)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6746 ->
        ((let uu____6748 =
            let uu____6754 =
              let uu____6756 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6756
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6754)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6748);
         FStar_Pervasives_Native.None)
     in
  let uu____6760 =
    let uu____6761 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6761 [] []  in
  let uu____6766 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6760 uu____6766 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____6775  -> failwith "bogus_cbs translate")
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
      let uu____6852 =
        let uu____6861 = e_list e  in unembed uu____6861 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6852
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6883  ->
    match uu____6883 with
    | (a,uu____6891) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6906)::[]) when
             let uu____6923 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6923 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6930 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6973 = let uu____6980 = as_arg c  in [uu____6980]  in
      int_to_t2 uu____6973
  
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
          let uu____7034 = f a  in FStar_Pervasives_Native.Some uu____7034
      | uu____7035 -> FStar_Pervasives_Native.None
  
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
          let uu____7089 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____7089
      | uu____7090 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____7134 = FStar_List.map as_a args  in lift_unary f uu____7134
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____7189 = FStar_List.map as_a args  in
        lift_binary f uu____7189
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____7219 = f x  in embed e_int bogus_cbs uu____7219)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____7246 = f x y  in embed e_int bogus_cbs uu____7246)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____7272 = f x  in embed e_bool bogus_cbs uu____7272)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____7310 = f x y  in embed e_bool bogus_cbs uu____7310)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____7348 = f x y  in embed e_string bogus_cbs uu____7348)
  
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
                let uu____7453 =
                  let uu____7462 = as_a a  in
                  let uu____7465 = as_b b  in (uu____7462, uu____7465)  in
                (match uu____7453 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____7480 =
                       let uu____7481 = f a1 b1  in embed_c uu____7481  in
                     FStar_Pervasives_Native.Some uu____7480
                 | uu____7482 -> FStar_Pervasives_Native.None)
            | uu____7491 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7500 = e_list e_char  in
    let uu____7507 = FStar_String.list_of_string s  in
    embed uu____7500 bogus_cbs uu____7507
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7546 =
        let uu____7547 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7547  in
      embed e_int bogus_cbs uu____7546
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7581 = arg_as_string a1  in
        (match uu____7581 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7590 = arg_as_list e_string a2  in
             (match uu____7590 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7608 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7608
              | uu____7610 -> FStar_Pervasives_Native.None)
         | uu____7616 -> FStar_Pervasives_Native.None)
    | uu____7620 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7627 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7627
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cbs (if b then "true" else "false") 
let (string_lowercase : Prims.string -> t) =
  fun s  -> embed e_string bogus_cbs (FStar_String.lowercase s) 
let (string_uppercase : Prims.string -> t) =
  fun s  -> embed e_string bogus_cbs (FStar_String.lowercase s) 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cbs true  in
      let fal = embed e_bool bogus_cbs false  in
      match args with
      | (_typ,uu____7689)::(a1,uu____7691)::(a2,uu____7693)::[] ->
          let uu____7710 = eq_t a1 a2  in
          (match uu____7710 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7719 -> FStar_Pervasives_Native.None)
      | uu____7720 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7735)::(_typ,uu____7737)::(a1,uu____7739)::(a2,uu____7741)::[]
        ->
        let uu____7762 = eq_t a1 a2  in
        (match uu____7762 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7765 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7765
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7768 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7768
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7771 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7786)::(_v,uu____7788)::(t1,uu____7790)::(t2,uu____7792)::
        (a1,uu____7794)::(a2,uu____7796)::[] ->
        let uu____7825 =
          let uu____7826 = eq_t t1 t2  in
          let uu____7827 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____7826 uu____7827  in
        (match uu____7825 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7830 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7830
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7833 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7833
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7836 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____7855 =
        let uu____7857 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____7857  in
      failwith uu____7855
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____7873)::[] ->
        let uu____7882 = unembed e_range bogus_cbs a1  in
        (match uu____7882 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7888 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7888
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7889 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7925 = arg_as_list e_char a1  in
        (match uu____7925 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7941 = arg_as_string a2  in
             (match uu____7941 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____7954 =
                    let uu____7955 = e_list e_string  in
                    embed uu____7955 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7954
              | uu____7965 -> FStar_Pervasives_Native.None)
         | uu____7969 -> FStar_Pervasives_Native.None)
    | uu____7975 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____8008 =
          let uu____8018 = arg_as_string a1  in
          let uu____8022 = arg_as_int a2  in (uu____8018, uu____8022)  in
        (match uu____8008 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1006_8046  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____8051 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8051) ()
              with | uu___1005_8054 -> FStar_Pervasives_Native.None)
         | uu____8057 -> FStar_Pervasives_Native.None)
    | uu____8067 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____8100 =
          let uu____8111 = arg_as_string a1  in
          let uu____8115 = arg_as_char a2  in (uu____8111, uu____8115)  in
        (match uu____8100 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1024_8144  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____8148 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8148) ()
              with | uu___1023_8150 -> FStar_Pervasives_Native.None)
         | uu____8153 -> FStar_Pervasives_Native.None)
    | uu____8164 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____8206 =
          let uu____8220 = arg_as_string a1  in
          let uu____8224 = arg_as_int a2  in
          let uu____8227 = arg_as_int a3  in
          (uu____8220, uu____8224, uu____8227)  in
        (match uu____8206 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1047_8260  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____8265 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8265) ()
              with | uu___1046_8268 -> FStar_Pervasives_Native.None)
         | uu____8271 -> FStar_Pervasives_Native.None)
    | uu____8285 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8345 =
          let uu____8367 = arg_as_string fn  in
          let uu____8371 = arg_as_int from_line  in
          let uu____8374 = arg_as_int from_col  in
          let uu____8377 = arg_as_int to_line  in
          let uu____8380 = arg_as_int to_col  in
          (uu____8367, uu____8371, uu____8374, uu____8377, uu____8380)  in
        (match uu____8345 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8415 =
                 let uu____8416 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8418 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8416 uu____8418  in
               let uu____8420 =
                 let uu____8421 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8423 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8421 uu____8423  in
               FStar_Range.mk_range fn1 uu____8415 uu____8420  in
             let uu____8425 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8425
         | uu____8426 -> FStar_Pervasives_Native.None)
    | uu____8448 -> FStar_Pervasives_Native.None
  
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
                let uu____8538 = FStar_List.splitAt n_tvars args  in
                match uu____8538 with
                | (_tvar_args,rest_args) ->
                    let uu____8587 = FStar_List.hd rest_args  in
                    (match uu____8587 with
                     | (x,uu____8599) ->
                         let uu____8600 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8600
                           (fun x1  ->
                              let uu____8606 = f x1  in
                              embed eb cb uu____8606))
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
                  let uu____8715 = FStar_List.splitAt n_tvars args  in
                  match uu____8715 with
                  | (_tvar_args,rest_args) ->
                      let uu____8764 = FStar_List.hd rest_args  in
                      (match uu____8764 with
                       | (x,uu____8776) ->
                           let uu____8777 =
                             let uu____8782 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8782  in
                           (match uu____8777 with
                            | (y,uu____8800) ->
                                let uu____8801 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____8801
                                  (fun x1  ->
                                     let uu____8807 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____8807
                                       (fun y1  ->
                                          let uu____8813 =
                                            let uu____8814 = f x1 y1  in
                                            embed ec cb uu____8814  in
                                          FStar_Pervasives_Native.Some
                                            uu____8813))))
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
                    let uu____8942 = FStar_List.splitAt n_tvars args  in
                    match uu____8942 with
                    | (_tvar_args,rest_args) ->
                        let uu____8991 = FStar_List.hd rest_args  in
                        (match uu____8991 with
                         | (x,uu____9003) ->
                             let uu____9004 =
                               let uu____9009 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____9009  in
                             (match uu____9004 with
                              | (y,uu____9027) ->
                                  let uu____9028 =
                                    let uu____9033 =
                                      let uu____9040 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____9040  in
                                    FStar_List.hd uu____9033  in
                                  (match uu____9028 with
                                   | (z,uu____9062) ->
                                       let uu____9063 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____9063
                                         (fun x1  ->
                                            let uu____9069 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____9069
                                              (fun y1  ->
                                                 let uu____9075 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____9075
                                                   (fun z1  ->
                                                      let uu____9081 =
                                                        let uu____9082 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____9082
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____9081))))))
                     in
                  f_wrapped
  