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
  | SConst of FStar_Const.sconst 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____62 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____75 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____97 -> false 
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____121 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____156 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____178 -> false
  
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee  -> match projectee with | Range _0 -> _0 
let (uu___is_SConst : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | SConst _0 -> true | uu____197 -> false
  
let (__proj__SConst__item___0 : constant -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | SConst _0 -> _0 
type atom =
  | Var of var 
  | Match of (t * (unit -> FStar_Syntax_Syntax.branch Prims.list)) 
  | UnreducedLet of (var * t FStar_Thunk.t * t FStar_Thunk.t * t
  FStar_Thunk.t * FStar_Syntax_Syntax.letbinding) 
  | UnreducedLetRec of ((var * t * t) Prims.list * t *
  FStar_Syntax_Syntax.letbinding Prims.list) 
  | UVar of FStar_Syntax_Syntax.term FStar_Thunk.t 
and t =
  | Lam of ((t Prims.list -> t) *
  ((t Prims.list * FStar_Syntax_Syntax.binders *
     FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
  (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Util.either * Prims.int)
  
  | Accu of (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Construct of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | FV of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list *
  (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
  | Arrow of
  (FStar_Syntax_Syntax.term FStar_Thunk.t,((t * FStar_Syntax_Syntax.aqual)
                                            Prims.list * comp))
  FStar_Util.either 
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
    match projectee with | Var _0 -> true | uu____739 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____767 -> false
  
let (__proj__Match__item___0 :
  atom -> (t * (unit -> FStar_Syntax_Syntax.branch Prims.list))) =
  fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLet _0 -> true | uu____829 -> false
  
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStar_Thunk.t * t FStar_Thunk.t * t FStar_Thunk.t *
      FStar_Syntax_Syntax.letbinding))
  = fun projectee  -> match projectee with | UnreducedLet _0 -> _0 
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLetRec _0 -> true | uu____912 -> false
  
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee  -> match projectee with | UnreducedLetRec _0 -> _0 
let (uu___is_UVar : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UVar _0 -> true | uu____981 -> false
  
let (__proj__UVar__item___0 : atom -> FStar_Syntax_Syntax.term FStar_Thunk.t)
  = fun projectee  -> match projectee with | UVar _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____1038 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) *
      ((t Prims.list * FStar_Syntax_Syntax.binders *
         FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
      (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Util.either *
      Prims.int))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____1163 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____1226 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____1301 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1362 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1381 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1400 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1418 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1446 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (FStar_Syntax_Syntax.term FStar_Thunk.t,((t * FStar_Syntax_Syntax.aqual)
                                              Prims.list * comp))
      FStar_Util.either)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1527 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1588 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1611 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1656 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_TopLevelLet : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____1730 -> false
  
let (__proj__TopLevelLet__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_TopLevelRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelRec _0 -> true | uu____1806 -> false
  
let (__proj__TopLevelRec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelRec _0 -> _0 
let (uu___is_LocalLetRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalLetRec _0 -> true | uu____1908 -> false
  
let (__proj__LocalLetRec__item___0 :
  t ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee  -> match projectee with | LocalLetRec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____2020 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____2063 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____2100 -> false
  
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
    match projectee with | TOTAL  -> true | uu____2229 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____2240 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____2251 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____2262 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____2273 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____2284 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____2295 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____2306 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____2317 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____2329 -> false
  
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
  fun trm  -> match trm with | Accu uu____2405 -> true | uu____2417 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____2427,uu____2428) -> false | uu____2442 -> true
  
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
  fun uu___0_2557  ->
    if uu___0_2557
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2568  ->
    if uu___1_2568
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
      | (FStar_Syntax_Util.NotEqual ,uu____2584) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2585,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2586) -> FStar_Syntax_Util.Unknown
      | (uu____2587,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2604 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2624),String (s2,uu____2626)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2639,uu____2640) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2676,Lam uu____2677) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2770 = eq_atom a1 a2  in
          eq_and uu____2770 (fun uu____2772  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2811 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2811
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2827 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2884  ->
                        match uu____2884 with
                        | ((a1,uu____2898),(a2,uu____2900)) ->
                            let uu____2909 = eq_t a1 a2  in
                            eq_inj acc uu____2909) FStar_Syntax_Util.Equal)
                uu____2827))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2950 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2950
          then
            let uu____2953 =
              let uu____2954 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2954  in
            eq_and uu____2953 (fun uu____2957  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2964 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2964
      | (Univ u1,Univ u2) ->
          let uu____2968 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2968
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____3015 =
            let uu____3016 =
              let uu____3017 = t11 ()  in
              FStar_Pervasives_Native.fst uu____3017  in
            let uu____3022 =
              let uu____3023 = t21 ()  in
              FStar_Pervasives_Native.fst uu____3023  in
            eq_t uu____3016 uu____3022  in
          eq_and uu____3015
            (fun uu____3031  ->
               let uu____3032 =
                 let uu____3033 = mkAccuVar x  in r1 uu____3033  in
               let uu____3034 =
                 let uu____3035 = mkAccuVar x  in r2 uu____3035  in
               eq_t uu____3032 uu____3034)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____3036,uu____3037) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____3042,uu____3043) -> FStar_Syntax_Util.Unknown

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
          let uu____3124 = eq_arg x y  in
          eq_and uu____3124 (fun uu____3126  -> eq_args xs ys)
      | (uu____3127,uu____3128) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____3175) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____3180 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____3180
    | SConst s -> FStar_Syntax_Print.const_to_string s
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,uu____3198,arity) ->
        let uu____3252 = FStar_Util.string_of_int arity  in
        FStar_Util.format1 "Lam (_, %s args)" uu____3252
    | Accu (a,l) ->
        let uu____3269 =
          let uu____3271 = atom_to_string a  in
          let uu____3273 =
            let uu____3275 =
              let uu____3277 =
                let uu____3279 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____3279  in
              FStar_String.op_Hat uu____3277 ")"  in
            FStar_String.op_Hat ") (" uu____3275  in
          FStar_String.op_Hat uu____3271 uu____3273  in
        FStar_String.op_Hat "Accu (" uu____3269
    | Construct (fv,us,l) ->
        let uu____3317 =
          let uu____3319 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3321 =
            let uu____3323 =
              let uu____3325 =
                let uu____3327 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3327  in
              let uu____3333 =
                let uu____3335 =
                  let uu____3337 =
                    let uu____3339 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3339  in
                  FStar_String.op_Hat uu____3337 "]"  in
                FStar_String.op_Hat "] [" uu____3335  in
              FStar_String.op_Hat uu____3325 uu____3333  in
            FStar_String.op_Hat ") [" uu____3323  in
          FStar_String.op_Hat uu____3319 uu____3321  in
        FStar_String.op_Hat "Construct (" uu____3317
    | FV (fv,us,l) ->
        let uu____3378 =
          let uu____3380 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3382 =
            let uu____3384 =
              let uu____3386 =
                let uu____3388 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3388  in
              let uu____3394 =
                let uu____3396 =
                  let uu____3398 =
                    let uu____3400 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3400  in
                  FStar_String.op_Hat uu____3398 "]"  in
                FStar_String.op_Hat "] [" uu____3396  in
              FStar_String.op_Hat uu____3386 uu____3394  in
            FStar_String.op_Hat ") [" uu____3384  in
          FStar_String.op_Hat uu____3380 uu____3382  in
        FStar_String.op_Hat "FV (" uu____3378
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3422 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3422
    | Type_t u ->
        let uu____3426 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3426
    | Arrow uu____3429 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3471 = t ()  in FStar_Pervasives_Native.fst uu____3471
           in
        let uu____3476 =
          let uu____3478 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3480 =
            let uu____3482 =
              let uu____3484 = t_to_string t1  in
              let uu____3486 =
                let uu____3488 =
                  let uu____3490 =
                    let uu____3492 =
                      let uu____3493 = mkAccuVar x1  in f uu____3493  in
                    t_to_string uu____3492  in
                  FStar_String.op_Hat uu____3490 "}"  in
                FStar_String.op_Hat "{" uu____3488  in
              FStar_String.op_Hat uu____3484 uu____3486  in
            FStar_String.op_Hat ":" uu____3482  in
          FStar_String.op_Hat uu____3478 uu____3480  in
        FStar_String.op_Hat "Refinement " uu____3476
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____3500 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____3500
    | Quote uu____3503 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3510) ->
        let uu____3527 =
          let uu____3529 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3529  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3527
    | Lazy (FStar_Util.Inr (uu____3531,et),uu____3533) ->
        let uu____3550 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3550
    | LocalLetRec
        (uu____3553,l,uu____3555,uu____3556,uu____3557,uu____3558,uu____3559)
        ->
        let uu____3590 =
          let uu____3592 = FStar_Syntax_Print.lbs_to_string [] (true, [l])
             in
          FStar_String.op_Hat uu____3592 ")"  in
        FStar_String.op_Hat "LocalLetRec (" uu____3590
    | TopLevelLet (lb,uu____3601,uu____3602) ->
        let uu____3617 =
          let uu____3619 =
            let uu____3621 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3621  in
          FStar_String.op_Hat uu____3619 ")"  in
        FStar_String.op_Hat "TopLevelLet (" uu____3617
    | TopLevelRec (lb,uu____3625,uu____3626,uu____3627) ->
        let uu____3648 =
          let uu____3650 =
            let uu____3652 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3652  in
          FStar_String.op_Hat uu____3650 ")"  in
        FStar_String.op_Hat "TopLevelRec (" uu____3648

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3658 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3658
    | Match (t,uu____3662) ->
        let uu____3673 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3673
    | UnreducedLet (var,typ,def,body,lb) ->
        let uu____3693 =
          let uu____3695 = FStar_Syntax_Print.lbs_to_string [] (false, [lb])
             in
          FStar_String.op_Hat uu____3695 " in ...)"  in
        FStar_String.op_Hat "UnreducedLet(" uu____3693
    | UnreducedLetRec (uu____3703,body,lbs) ->
        let uu____3726 =
          let uu____3728 = FStar_Syntax_Print.lbs_to_string [] (true, lbs)
             in
          let uu____3734 =
            let uu____3736 =
              let uu____3738 = t_to_string body  in
              FStar_String.op_Hat uu____3738 ")"  in
            FStar_String.op_Hat " in " uu____3736  in
          FStar_String.op_Hat uu____3728 uu____3734  in
        FStar_String.op_Hat "UnreducedLetRec(" uu____3726
    | UVar uu____3743 -> "UVar"

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3754 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3754 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3767 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3767 (FStar_String.concat " ")
  
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
        let uu____4238 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____4238 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____4259 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____4259 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow (FStar_Util.Inr ([a], (Tot (t1, FStar_Pervasives_Native.None))))
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____4342 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____4342
         then
           let uu____4366 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4366
         else ());
        (let uu____4371 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4371
         then f ()
         else
           (let thunk1 = FStar_Thunk.mk f  in
            let li = let uu____4405 = FStar_Dyn.mkdyn x  in (uu____4405, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____4433 'a .
    'Auu____4433 ->
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
              let uu____4484 = FStar_Thunk.force thunk1  in f uu____4484
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____4504 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4504
              then
                let res =
                  let uu____4533 = FStar_Thunk.force thunk1  in f uu____4533
                   in
                ((let uu____4535 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4535
                  then
                    let uu____4559 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4561 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4559
                      uu____4561
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____4570 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4570
                  then
                    let uu____4594 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4594
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____4599 ->
              let aopt = f x  in
              ((let uu____4604 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4604
                then
                  let uu____4628 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4628
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
  let uu____4696 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4696 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____4730 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4735 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4730 uu____4735 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4776 -> FStar_Pervasives_Native.None  in
  let uu____4778 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____4783 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4778 uu____4783 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4825 -> FStar_Pervasives_Native.None  in
  let uu____4827 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____4832 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____4827 uu____4832 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____4874)) -> FStar_Pervasives_Native.Some s1
    | uu____4878 -> FStar_Pervasives_Native.None  in
  let uu____4880 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____4885 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____4880 uu____4885 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4920 -> FStar_Pervasives_Native.None  in
  let uu____4921 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4926 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4921 uu____4926 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4947 =
        let uu____4955 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4955, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4947  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4980  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4981 =
                 let uu____4982 =
                   let uu____4987 = type_of ea  in as_iarg uu____4987  in
                 [uu____4982]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4981
           | FStar_Pervasives_Native.Some x ->
               let uu____4997 =
                 let uu____4998 =
                   let uu____5003 = embed ea cb x  in as_arg uu____5003  in
                 let uu____5004 =
                   let uu____5011 =
                     let uu____5016 = type_of ea  in as_iarg uu____5016  in
                   [uu____5011]  in
                 uu____4998 :: uu____5004  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4997)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____5083)::uu____5084::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____5111 = unembed ea cb a  in
               FStar_Util.bind_opt uu____5111
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____5120 -> FStar_Pervasives_Native.None)
       in
    let uu____5123 =
      let uu____5124 =
        let uu____5125 = let uu____5130 = type_of ea  in as_arg uu____5130
           in
        [uu____5125]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____5124
       in
    mk_emb em un uu____5123 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5177 =
          let uu____5185 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____5185, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5177  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____5216  ->
             let uu____5217 =
               let uu____5218 =
                 let uu____5223 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____5223  in
               let uu____5224 =
                 let uu____5231 =
                   let uu____5236 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____5236  in
                 let uu____5237 =
                   let uu____5244 =
                     let uu____5249 = type_of eb  in as_iarg uu____5249  in
                   let uu____5250 =
                     let uu____5257 =
                       let uu____5262 = type_of ea  in as_iarg uu____5262  in
                     [uu____5257]  in
                   uu____5244 :: uu____5250  in
                 uu____5231 :: uu____5237  in
               uu____5218 :: uu____5224  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____5217)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____5330)::(a,uu____5332)::uu____5333::uu____5334::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5373 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5373
                   (fun a1  ->
                      let uu____5383 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____5383
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____5396 -> FStar_Pervasives_Native.None)
         in
      let uu____5401 =
        let uu____5402 =
          let uu____5403 = let uu____5408 = type_of eb  in as_arg uu____5408
             in
          let uu____5409 =
            let uu____5416 =
              let uu____5421 = type_of ea  in as_arg uu____5421  in
            [uu____5416]  in
          uu____5403 :: uu____5409  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5402
         in
      mk_emb em un uu____5401 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5474 =
          let uu____5482 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5482, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5474  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5514  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____5516 =
                   let uu____5517 =
                     let uu____5522 = embed ea cb a  in as_arg uu____5522  in
                   let uu____5523 =
                     let uu____5530 =
                       let uu____5535 = type_of eb  in as_iarg uu____5535  in
                     let uu____5536 =
                       let uu____5543 =
                         let uu____5548 = type_of ea  in as_iarg uu____5548
                          in
                       [uu____5543]  in
                     uu____5530 :: uu____5536  in
                   uu____5517 :: uu____5523  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5516
             | FStar_Util.Inr b ->
                 let uu____5566 =
                   let uu____5567 =
                     let uu____5572 = embed eb cb b  in as_arg uu____5572  in
                   let uu____5573 =
                     let uu____5580 =
                       let uu____5585 = type_of eb  in as_iarg uu____5585  in
                     let uu____5586 =
                       let uu____5593 =
                         let uu____5598 = type_of ea  in as_iarg uu____5598
                          in
                       [uu____5593]  in
                     uu____5580 :: uu____5586  in
                   uu____5567 :: uu____5573  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5566)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____5660)::uu____5661::uu____5662::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5697 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5697
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____5713)::uu____5714::uu____5715::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5750 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____5750
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____5763 -> FStar_Pervasives_Native.None)
         in
      let uu____5768 =
        let uu____5769 =
          let uu____5770 = let uu____5775 = type_of eb  in as_arg uu____5775
             in
          let uu____5776 =
            let uu____5783 =
              let uu____5788 = type_of ea  in as_arg uu____5788  in
            [uu____5783]  in
          uu____5770 :: uu____5776  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5769
         in
      mk_emb em un uu____5768 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5837 -> FStar_Pervasives_Native.None  in
  let uu____5838 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5843 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5838 uu____5843 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5864 =
        let uu____5872 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5872, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5864  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5899  ->
           let typ = let uu____5901 = type_of ea  in as_iarg uu____5901  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5922 =
               let uu____5923 = as_arg tl1  in
               let uu____5928 =
                 let uu____5935 =
                   let uu____5940 = embed ea cb hd1  in as_arg uu____5940  in
                 [uu____5935; typ]  in
               uu____5923 :: uu____5928  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5922
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5988,uu____5989) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____6009,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____6012,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6013))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6041 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____6041
                 (fun hd2  ->
                    let uu____6049 = un cb tl1  in
                    FStar_Util.bind_opt uu____6049
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____6065,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6090 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____6090
                 (fun hd2  ->
                    let uu____6098 = un cb tl1  in
                    FStar_Util.bind_opt uu____6098
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____6113 -> FStar_Pervasives_Native.None)
       in
    let uu____6116 =
      let uu____6117 =
        let uu____6118 = let uu____6123 = type_of ea  in as_arg uu____6123
           in
        [uu____6118]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____6117
       in
    mk_emb em un uu____6116 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____6197  ->
             let uu____6198 =
               let uu____6231 =
                 let uu____6252 =
                   let uu____6259 =
                     let uu____6264 = type_of eb  in as_arg uu____6264  in
                   [uu____6259]  in
                 FStar_Util.Inr uu____6252  in
               ((fun tas  ->
                   let uu____6322 =
                     let uu____6325 = FStar_List.hd tas  in
                     unembed ea cb uu____6325  in
                   match uu____6322 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____6327 = f a  in embed eb cb uu____6327
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 uu____6231, Prims.int_one)
                in
             Lam uu____6198)
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____6374 =
                 let uu____6377 =
                   let uu____6378 =
                     let uu____6379 =
                       let uu____6384 = embed ea cb x  in as_arg uu____6384
                        in
                     [uu____6379]  in
                   cb.iapp lam1 uu____6378  in
                 unembed eb cb uu____6377  in
               match uu____6374 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____6398 =
        let uu____6399 = type_of ea  in
        let uu____6400 = let uu____6401 = type_of eb  in as_iarg uu____6401
           in
        make_arrow1 uu____6399 uu____6400  in
      mk_emb em un uu____6398 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____6419 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6419 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____6424 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6424 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____6429 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6429 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____6434 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6434 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____6439 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6439 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____6444 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6444 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____6449 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6449 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____6454 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6454 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____6459 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6459 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6468 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6469 =
          let uu____6470 =
            let uu____6475 =
              let uu____6476 = e_list e_string  in embed uu____6476 cb l  in
            as_arg uu____6475  in
          [uu____6470]  in
        mkFV uu____6468 [] uu____6469
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6498 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6499 =
          let uu____6500 =
            let uu____6505 =
              let uu____6506 = e_list e_string  in embed uu____6506 cb l  in
            as_arg uu____6505  in
          [uu____6500]  in
        mkFV uu____6498 [] uu____6499
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6528 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6529 =
          let uu____6530 =
            let uu____6535 =
              let uu____6536 = e_list e_string  in embed uu____6536 cb l  in
            as_arg uu____6535  in
          [uu____6530]  in
        mkFV uu____6528 [] uu____6529
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____6570,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6586,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6602,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6618,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6634,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6650,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6666,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6682,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6698,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6714,(l,uu____6716)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6735 =
          let uu____6741 = e_list e_string  in unembed uu____6741 cb l  in
        FStar_Util.bind_opt uu____6735
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6761  -> FStar_Pervasives_Native.Some _6761)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6763,(l,uu____6765)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6784 =
          let uu____6790 = e_list e_string  in unembed uu____6790 cb l  in
        FStar_Util.bind_opt uu____6784
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6810  -> FStar_Pervasives_Native.Some _6810)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____6812,(l,uu____6814)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6833 =
          let uu____6839 = e_list e_string  in unembed uu____6839 cb l  in
        FStar_Util.bind_opt uu____6833
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6859  -> FStar_Pervasives_Native.Some _6859)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6860 ->
        ((let uu____6862 =
            let uu____6868 =
              let uu____6870 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6870
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6868)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6862);
         FStar_Pervasives_Native.None)
     in
  let uu____6874 =
    let uu____6875 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6875 [] []  in
  let uu____6880 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6874 uu____6880 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____6889  -> failwith "bogus_cbs translate")
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
      let uu____6966 =
        let uu____6975 = e_list e  in unembed uu____6975 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6966
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6997  ->
    match uu____6997 with
    | (a,uu____7005) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____7020)::[]) when
             let uu____7037 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7037 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____7044 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____7087 = let uu____7094 = as_arg c  in [uu____7094]  in
      int_to_t2 uu____7087
  
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
          let uu____7148 = f a  in FStar_Pervasives_Native.Some uu____7148
      | uu____7149 -> FStar_Pervasives_Native.None
  
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
          let uu____7203 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____7203
      | uu____7204 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____7248 = FStar_List.map as_a args  in lift_unary f uu____7248
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____7303 = FStar_List.map as_a args  in
        lift_binary f uu____7303
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____7333 = f x  in embed e_int bogus_cbs uu____7333)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____7360 = f x y  in embed e_int bogus_cbs uu____7360)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____7386 = f x  in embed e_bool bogus_cbs uu____7386)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____7424 = f x y  in embed e_bool bogus_cbs uu____7424)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____7462 = f x y  in embed e_string bogus_cbs uu____7462)
  
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
                let uu____7567 =
                  let uu____7576 = as_a a  in
                  let uu____7579 = as_b b  in (uu____7576, uu____7579)  in
                (match uu____7567 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____7594 =
                       let uu____7595 = f a1 b1  in embed_c uu____7595  in
                     FStar_Pervasives_Native.Some uu____7594
                 | uu____7596 -> FStar_Pervasives_Native.None)
            | uu____7605 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7614 = e_list e_char  in
    let uu____7621 = FStar_String.list_of_string s  in
    embed uu____7614 bogus_cbs uu____7621
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7660 =
        let uu____7661 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7661  in
      embed e_int bogus_cbs uu____7660
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7695 = arg_as_string a1  in
        (match uu____7695 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7704 = arg_as_list e_string a2  in
             (match uu____7704 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7722 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7722
              | uu____7724 -> FStar_Pervasives_Native.None)
         | uu____7730 -> FStar_Pervasives_Native.None)
    | uu____7734 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7741 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7741
  
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
      | (_typ,uu____7803)::(a1,uu____7805)::(a2,uu____7807)::[] ->
          let uu____7824 = eq_t a1 a2  in
          (match uu____7824 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7833 -> FStar_Pervasives_Native.None)
      | uu____7834 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7849)::(_typ,uu____7851)::(a1,uu____7853)::(a2,uu____7855)::[]
        ->
        let uu____7876 = eq_t a1 a2  in
        (match uu____7876 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7879 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7879
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7882 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7882
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7885 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7900)::(_v,uu____7902)::(t1,uu____7904)::(t2,uu____7906)::
        (a1,uu____7908)::(a2,uu____7910)::[] ->
        let uu____7939 =
          let uu____7940 = eq_t t1 t2  in
          let uu____7941 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____7940 uu____7941  in
        (match uu____7939 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7944 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7944
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7947 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7947
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7950 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____7969 =
        let uu____7971 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____7971  in
      failwith uu____7969
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____7987)::[] ->
        let uu____7996 = unembed e_range bogus_cbs a1  in
        (match uu____7996 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8002 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8002
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8003 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____8039 = arg_as_list e_char a1  in
        (match uu____8039 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8055 = arg_as_string a2  in
             (match uu____8055 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____8068 =
                    let uu____8069 = e_list e_string  in
                    embed uu____8069 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____8068
              | uu____8079 -> FStar_Pervasives_Native.None)
         | uu____8083 -> FStar_Pervasives_Native.None)
    | uu____8089 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____8122 =
          let uu____8132 = arg_as_string a1  in
          let uu____8136 = arg_as_int a2  in (uu____8132, uu____8136)  in
        (match uu____8122 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1008_8160  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____8165 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8165) ()
              with | uu___1007_8168 -> FStar_Pervasives_Native.None)
         | uu____8171 -> FStar_Pervasives_Native.None)
    | uu____8181 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____8214 =
          let uu____8225 = arg_as_string a1  in
          let uu____8229 = arg_as_char a2  in (uu____8225, uu____8229)  in
        (match uu____8214 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1026_8258  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____8262 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8262) ()
              with | uu___1025_8264 -> FStar_Pervasives_Native.None)
         | uu____8267 -> FStar_Pervasives_Native.None)
    | uu____8278 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____8320 =
          let uu____8334 = arg_as_string a1  in
          let uu____8338 = arg_as_int a2  in
          let uu____8341 = arg_as_int a3  in
          (uu____8334, uu____8338, uu____8341)  in
        (match uu____8320 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1049_8374  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____8379 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8379) ()
              with | uu___1048_8382 -> FStar_Pervasives_Native.None)
         | uu____8385 -> FStar_Pervasives_Native.None)
    | uu____8399 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8459 =
          let uu____8481 = arg_as_string fn  in
          let uu____8485 = arg_as_int from_line  in
          let uu____8488 = arg_as_int from_col  in
          let uu____8491 = arg_as_int to_line  in
          let uu____8494 = arg_as_int to_col  in
          (uu____8481, uu____8485, uu____8488, uu____8491, uu____8494)  in
        (match uu____8459 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8529 =
                 let uu____8530 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8532 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8530 uu____8532  in
               let uu____8534 =
                 let uu____8535 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8537 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8535 uu____8537  in
               FStar_Range.mk_range fn1 uu____8529 uu____8534  in
             let uu____8539 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8539
         | uu____8540 -> FStar_Pervasives_Native.None)
    | uu____8562 -> FStar_Pervasives_Native.None
  
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
                let uu____8652 = FStar_List.splitAt n_tvars args  in
                match uu____8652 with
                | (_tvar_args,rest_args) ->
                    let uu____8701 = FStar_List.hd rest_args  in
                    (match uu____8701 with
                     | (x,uu____8713) ->
                         let uu____8714 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8714
                           (fun x1  ->
                              let uu____8720 = f x1  in
                              embed eb cb uu____8720))
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
                  let uu____8829 = FStar_List.splitAt n_tvars args  in
                  match uu____8829 with
                  | (_tvar_args,rest_args) ->
                      let uu____8878 = FStar_List.hd rest_args  in
                      (match uu____8878 with
                       | (x,uu____8890) ->
                           let uu____8891 =
                             let uu____8896 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8896  in
                           (match uu____8891 with
                            | (y,uu____8914) ->
                                let uu____8915 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____8915
                                  (fun x1  ->
                                     let uu____8921 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____8921
                                       (fun y1  ->
                                          let uu____8927 =
                                            let uu____8928 = f x1 y1  in
                                            embed ec cb uu____8928  in
                                          FStar_Pervasives_Native.Some
                                            uu____8927))))
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
                    let uu____9056 = FStar_List.splitAt n_tvars args  in
                    match uu____9056 with
                    | (_tvar_args,rest_args) ->
                        let uu____9105 = FStar_List.hd rest_args  in
                        (match uu____9105 with
                         | (x,uu____9117) ->
                             let uu____9118 =
                               let uu____9123 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____9123  in
                             (match uu____9118 with
                              | (y,uu____9141) ->
                                  let uu____9142 =
                                    let uu____9147 =
                                      let uu____9154 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____9154  in
                                    FStar_List.hd uu____9147  in
                                  (match uu____9142 with
                                   | (z,uu____9176) ->
                                       let uu____9177 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____9177
                                         (fun x1  ->
                                            let uu____9183 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____9183
                                              (fun y1  ->
                                                 let uu____9189 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____9189
                                                   (fun z1  ->
                                                      let uu____9195 =
                                                        let uu____9196 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____9196
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____9195))))))
                     in
                  f_wrapped
  