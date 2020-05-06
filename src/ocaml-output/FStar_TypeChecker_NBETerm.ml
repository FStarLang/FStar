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
  | Meta of (t * FStar_Syntax_Syntax.metadata FStar_Thunk.t) 
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
    match projectee with | Var _0 -> true | uu____951 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____979 -> false
  
let (__proj__Match__item___0 :
  atom -> (t * (unit -> FStar_Syntax_Syntax.branch Prims.list))) =
  fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLet _0 -> true | uu____1041 -> false
  
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStar_Thunk.t * t FStar_Thunk.t * t FStar_Thunk.t *
      FStar_Syntax_Syntax.letbinding))
  = fun projectee  -> match projectee with | UnreducedLet _0 -> _0 
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLetRec _0 -> true | uu____1124 -> false
  
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee  -> match projectee with | UnreducedLetRec _0 -> _0 
let (uu___is_UVar : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UVar _0 -> true | uu____1193 -> false
  
let (__proj__UVar__item___0 : atom -> FStar_Syntax_Syntax.term FStar_Thunk.t)
  = fun projectee  -> match projectee with | UVar _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____1250 -> false
  
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
    match projectee with | Accu _0 -> true | uu____1375 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____1438 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____1513 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1574 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1593 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1612 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1630 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1658 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (FStar_Syntax_Syntax.term FStar_Thunk.t,((t * FStar_Syntax_Syntax.aqual)
                                              Prims.list * comp))
      FStar_Util.either)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1739 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1800 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1823 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1868 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Meta : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1935 -> false
  
let (__proj__Meta__item___0 :
  t -> (t * FStar_Syntax_Syntax.metadata FStar_Thunk.t)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_TopLevelLet : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____1985 -> false
  
let (__proj__TopLevelLet__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_TopLevelRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelRec _0 -> true | uu____2061 -> false
  
let (__proj__TopLevelRec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelRec _0 -> _0 
let (uu___is_LocalLetRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalLetRec _0 -> true | uu____2163 -> false
  
let (__proj__LocalLetRec__item___0 :
  t ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee  -> match projectee with | LocalLetRec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____2275 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____2318 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____2355 -> false
  
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
    match projectee with | TOTAL  -> true | uu____2484 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____2495 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____2506 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____2517 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____2528 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____2539 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____2550 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____2561 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____2572 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____2584 -> false
  
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
  fun trm  -> match trm with | Accu uu____2660 -> true | uu____2672 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____2682,uu____2683) -> false | uu____2697 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> FV (i, us, ts) 
let (mkAccuVar : var -> t) = fun v  -> Accu ((Var v), []) 
let (mkAccuMatch : t -> (unit -> FStar_Syntax_Syntax.branch Prims.list) -> t)
  = fun s  -> fun bs  -> Accu ((Match (s, bs)), []) 
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___0_2812  ->
    if uu___0_2812
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2823  ->
    if uu___1_2823
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
      | (FStar_Syntax_Util.NotEqual ,uu____2839) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2840,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2841) -> FStar_Syntax_Util.Unknown
      | (uu____2842,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2859 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2879),String (s2,uu____2881)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2894,uu____2895) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2931,Lam uu____2932) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____3025 = eq_atom a1 a2  in
          eq_and uu____3025 (fun uu____3027  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____3066 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____3066
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____3082 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____3139  ->
                        match uu____3139 with
                        | ((a1,uu____3153),(a2,uu____3155)) ->
                            let uu____3164 = eq_t a1 a2  in
                            eq_inj acc uu____3164) FStar_Syntax_Util.Equal)
                uu____3082))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____3205 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____3205
          then
            let uu____3208 =
              let uu____3209 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____3209  in
            eq_and uu____3208 (fun uu____3212  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____3219 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3219
      | (Univ u1,Univ u2) ->
          let uu____3223 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3223
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____3270 =
            let uu____3271 =
              let uu____3272 = t11 ()  in
              FStar_Pervasives_Native.fst uu____3272  in
            let uu____3277 =
              let uu____3278 = t21 ()  in
              FStar_Pervasives_Native.fst uu____3278  in
            eq_t uu____3271 uu____3277  in
          eq_and uu____3270
            (fun uu____3286  ->
               let uu____3287 =
                 let uu____3288 = mkAccuVar x  in r1 uu____3288  in
               let uu____3289 =
                 let uu____3290 = mkAccuVar x  in r2 uu____3290  in
               eq_t uu____3287 uu____3289)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____3291,uu____3292) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) ->
          let uu____3297 = FStar_Syntax_Syntax.bv_eq bv1 bv2  in
          equal_if uu____3297
      | (uu____3299,uu____3300) -> FStar_Syntax_Util.Unknown

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
          let uu____3381 = eq_arg x y  in
          eq_and uu____3381 (fun uu____3383  -> eq_args xs ys)
      | (uu____3384,uu____3385) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____3432) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____3437 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____3437
    | SConst s -> FStar_Syntax_Print.const_to_string s
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,uu____3455,arity) ->
        let uu____3509 = FStar_Util.string_of_int arity  in
        FStar_Util.format1 "Lam (_, %s args)" uu____3509
    | Accu (a,l) ->
        let uu____3526 =
          let uu____3528 = atom_to_string a  in
          let uu____3530 =
            let uu____3532 =
              let uu____3534 =
                let uu____3536 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____3536  in
              FStar_String.op_Hat uu____3534 ")"  in
            FStar_String.op_Hat ") (" uu____3532  in
          FStar_String.op_Hat uu____3528 uu____3530  in
        FStar_String.op_Hat "Accu (" uu____3526
    | Construct (fv,us,l) ->
        let uu____3574 =
          let uu____3576 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3578 =
            let uu____3580 =
              let uu____3582 =
                let uu____3584 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3584  in
              let uu____3590 =
                let uu____3592 =
                  let uu____3594 =
                    let uu____3596 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3596  in
                  FStar_String.op_Hat uu____3594 "]"  in
                FStar_String.op_Hat "] [" uu____3592  in
              FStar_String.op_Hat uu____3582 uu____3590  in
            FStar_String.op_Hat ") [" uu____3580  in
          FStar_String.op_Hat uu____3576 uu____3578  in
        FStar_String.op_Hat "Construct (" uu____3574
    | FV (fv,us,l) ->
        let uu____3635 =
          let uu____3637 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3639 =
            let uu____3641 =
              let uu____3643 =
                let uu____3645 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3645  in
              let uu____3651 =
                let uu____3653 =
                  let uu____3655 =
                    let uu____3657 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3657  in
                  FStar_String.op_Hat uu____3655 "]"  in
                FStar_String.op_Hat "] [" uu____3653  in
              FStar_String.op_Hat uu____3643 uu____3651  in
            FStar_String.op_Hat ") [" uu____3641  in
          FStar_String.op_Hat uu____3637 uu____3639  in
        FStar_String.op_Hat "FV (" uu____3635
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3679 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3679
    | Type_t u ->
        let uu____3683 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3683
    | Arrow uu____3686 -> "Arrow"
    | Refinement (f,t1) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t2 =
          let uu____3728 = t1 ()  in FStar_Pervasives_Native.fst uu____3728
           in
        let uu____3733 =
          let uu____3735 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3737 =
            let uu____3739 =
              let uu____3741 = t_to_string t2  in
              let uu____3743 =
                let uu____3745 =
                  let uu____3747 =
                    let uu____3749 =
                      let uu____3750 = mkAccuVar x1  in f uu____3750  in
                    t_to_string uu____3749  in
                  FStar_String.op_Hat uu____3747 "}"  in
                FStar_String.op_Hat "{" uu____3745  in
              FStar_String.op_Hat uu____3741 uu____3743  in
            FStar_String.op_Hat ":" uu____3739  in
          FStar_String.op_Hat uu____3735 uu____3737  in
        FStar_String.op_Hat "Refinement " uu____3733
    | Unknown  -> "Unknown"
    | Reflect t1 ->
        let uu____3757 = t_to_string t1  in
        FStar_String.op_Hat "Reflect " uu____3757
    | Quote uu____3760 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3767) ->
        let uu____3784 =
          let uu____3786 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3786  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3784
    | Lazy (FStar_Util.Inr (uu____3788,et),uu____3790) ->
        let uu____3807 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3807
    | LocalLetRec
        (uu____3810,l,uu____3812,uu____3813,uu____3814,uu____3815,uu____3816)
        ->
        let uu____3847 =
          let uu____3849 = FStar_Syntax_Print.lbs_to_string [] (true, [l])
             in
          FStar_String.op_Hat uu____3849 ")"  in
        FStar_String.op_Hat "LocalLetRec (" uu____3847
    | TopLevelLet (lb,uu____3858,uu____3859) ->
        let uu____3874 =
          let uu____3876 =
            let uu____3878 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3878  in
          FStar_String.op_Hat uu____3876 ")"  in
        FStar_String.op_Hat "TopLevelLet (" uu____3874
    | TopLevelRec (lb,uu____3882,uu____3883,uu____3884) ->
        let uu____3905 =
          let uu____3907 =
            let uu____3909 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3909  in
          FStar_String.op_Hat uu____3907 ")"  in
        FStar_String.op_Hat "TopLevelRec (" uu____3905

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v ->
        let uu____3915 = FStar_Syntax_Print.bv_to_string v  in
        FStar_String.op_Hat "Var " uu____3915
    | Match (t1,uu____3919) ->
        let uu____3930 = t_to_string t1  in
        FStar_String.op_Hat "Match " uu____3930
    | UnreducedLet (var1,typ,def,body,lb) ->
        let uu____3950 =
          let uu____3952 = FStar_Syntax_Print.lbs_to_string [] (false, [lb])
             in
          FStar_String.op_Hat uu____3952 " in ...)"  in
        FStar_String.op_Hat "UnreducedLet(" uu____3950
    | UnreducedLetRec (uu____3960,body,lbs) ->
        let uu____3983 =
          let uu____3985 = FStar_Syntax_Print.lbs_to_string [] (true, lbs)
             in
          let uu____3991 =
            let uu____3993 =
              let uu____3995 = t_to_string body  in
              FStar_String.op_Hat uu____3995 ")"  in
            FStar_String.op_Hat " in " uu____3993  in
          FStar_String.op_Hat uu____3985 uu____3991  in
        FStar_String.op_Hat "UnreducedLetRec(" uu____3983
    | UVar uu____4000 -> "UVar"

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____4011 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____4011 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args1  ->
    let uu____4024 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____4024 (FStar_String.concat " ")
  
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
  fun cbs  -> fun t1  -> cbs.translate t1 
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
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) -> t FStar_Pervasives_Native.option -> 'b embedding
  =
  fun ea  ->
    fun ab  ->
      fun ba  ->
        fun ot  ->
          mk_emb
            (fun cbs  ->
               fun x  -> let uu____4535 = ba x  in embed ea cbs uu____4535)
            (fun cbs  ->
               fun t1  ->
                 let uu____4541 = unembed ea cbs t1  in
                 FStar_Util.map_opt uu____4541 ab)
            (match ot with
             | FStar_Pervasives_Native.Some t1 -> t1
             | FStar_Pervasives_Native.None  -> ea.typ) ea.emb_typ
  
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args1  ->
        let uu____4566 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____4566 us args1
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args1  ->
        let uu____4587 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____4587 us args1
  
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
        (let uu____4670 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____4670
         then
           let uu____4694 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4694
         else ());
        (let uu____4699 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4699
         then f ()
         else
           (let thunk = FStar_Thunk.mk f  in
            let li = let uu____4733 = FStar_Dyn.mkdyn x  in (uu____4733, et)
               in
            Lazy ((FStar_Util.Inr li), thunk)))
  
let lazy_unembed :
  'uuuuuu4761 'a .
    'uuuuuu4761 ->
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
              let uu____4812 = FStar_Thunk.force thunk  in f uu____4812
          | Lazy (FStar_Util.Inr (b,et'),thunk) ->
              let uu____4832 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4832
              then
                let res =
                  let uu____4861 = FStar_Thunk.force thunk  in f uu____4861
                   in
                ((let uu____4863 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4863
                  then
                    let uu____4887 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4889 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4887
                      uu____4889
                  else ());
                 res)
              else
                (let a1 = FStar_Dyn.undyn b  in
                 (let uu____4898 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4898
                  then
                    let uu____4922 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4922
                  else ());
                 FStar_Pervasives_Native.Some a1)
          | uu____4927 ->
              let aopt = f x  in
              ((let uu____4932 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4932
                then
                  let uu____4956 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4956
                else ());
               aopt)
  
let (mk_any_emb : t -> t embedding) =
  fun ty  ->
    let em _cb a = a  in
    let un _cb t1 = FStar_Pervasives_Native.Some t1  in
    mk_emb em un ty FStar_Syntax_Syntax.ET_abstract
  
let (e_any : t embedding) =
  let em _cb a = a  in
  let un _cb t1 = FStar_Pervasives_Native.Some t1  in
  let uu____5024 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____5024 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t1 = FStar_Pervasives_Native.Some ()  in
  let uu____5058 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____5063 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____5058 uu____5063 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t1 =
    match t1 with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____5104 -> FStar_Pervasives_Native.None  in
  let uu____5106 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____5111 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____5106 uu____5111 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____5153 -> FStar_Pervasives_Native.None  in
  let uu____5155 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____5160 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____5155 uu____5160 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____5202)) -> FStar_Pervasives_Native.Some s1
    | uu____5206 -> FStar_Pervasives_Native.None  in
  let uu____5208 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____5213 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____5208 uu____5213 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____5248 -> FStar_Pervasives_Native.None  in
  let uu____5249 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____5254 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____5249 uu____5254 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____5275 =
        let uu____5283 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____5283, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5275  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____5308  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____5309 =
                 let uu____5310 =
                   let uu____5315 = type_of ea  in as_iarg uu____5315  in
                 [uu____5310]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5309
           | FStar_Pervasives_Native.Some x ->
               let uu____5325 =
                 let uu____5326 =
                   let uu____5331 = embed ea cb x  in as_arg uu____5331  in
                 let uu____5332 =
                   let uu____5339 =
                     let uu____5344 = type_of ea  in as_iarg uu____5344  in
                   [uu____5339]  in
                 uu____5326 :: uu____5332  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5325)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar,us,args1) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar,us,(a1,uu____5411)::uu____5412::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.some_lid
               ->
               let uu____5439 = unembed ea cb a1  in
               FStar_Util.bind_opt uu____5439
                 (fun a2  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a2))
           | uu____5448 -> FStar_Pervasives_Native.None)
       in
    let uu____5451 =
      let uu____5452 =
        let uu____5453 = let uu____5458 = type_of ea  in as_arg uu____5458
           in
        [uu____5453]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____5452
       in
    mk_emb em un uu____5451 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5505 =
          let uu____5513 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____5513, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5505  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____5544  ->
             let uu____5545 =
               let uu____5546 =
                 let uu____5551 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____5551  in
               let uu____5552 =
                 let uu____5559 =
                   let uu____5564 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____5564  in
                 let uu____5565 =
                   let uu____5572 =
                     let uu____5577 = type_of eb  in as_iarg uu____5577  in
                   let uu____5578 =
                     let uu____5585 =
                       let uu____5590 = type_of ea  in as_iarg uu____5590  in
                     [uu____5585]  in
                   uu____5572 :: uu____5578  in
                 uu____5559 :: uu____5565  in
               uu____5546 :: uu____5552  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____5545)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar,us,(b1,uu____5658)::(a1,uu____5660)::uu____5661::uu____5662::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5701 = unembed ea cb a1  in
                 FStar_Util.bind_opt uu____5701
                   (fun a2  ->
                      let uu____5711 = unembed eb cb b1  in
                      FStar_Util.bind_opt uu____5711
                        (fun b2  -> FStar_Pervasives_Native.Some (a2, b2)))
             | uu____5724 -> FStar_Pervasives_Native.None)
         in
      let uu____5729 =
        let uu____5730 =
          let uu____5731 = let uu____5736 = type_of eb  in as_arg uu____5736
             in
          let uu____5737 =
            let uu____5744 =
              let uu____5749 = type_of ea  in as_arg uu____5749  in
            [uu____5744]  in
          uu____5731 :: uu____5737  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5730
         in
      mk_emb em un uu____5729 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5802 =
          let uu____5810 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5810, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5802  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5842  ->
             match s with
             | FStar_Util.Inl a1 ->
                 let uu____5844 =
                   let uu____5845 =
                     let uu____5850 = embed ea cb a1  in as_arg uu____5850
                      in
                   let uu____5851 =
                     let uu____5858 =
                       let uu____5863 = type_of eb  in as_iarg uu____5863  in
                     let uu____5864 =
                       let uu____5871 =
                         let uu____5876 = type_of ea  in as_iarg uu____5876
                          in
                       [uu____5871]  in
                     uu____5858 :: uu____5864  in
                   uu____5845 :: uu____5851  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5844
             | FStar_Util.Inr b1 ->
                 let uu____5894 =
                   let uu____5895 =
                     let uu____5900 = embed eb cb b1  in as_arg uu____5900
                      in
                   let uu____5901 =
                     let uu____5908 =
                       let uu____5913 = type_of eb  in as_iarg uu____5913  in
                     let uu____5914 =
                       let uu____5921 =
                         let uu____5926 = type_of ea  in as_iarg uu____5926
                          in
                       [uu____5921]  in
                     uu____5908 :: uu____5914  in
                   uu____5895 :: uu____5901  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5894)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar,us,(a1,uu____5988)::uu____5989::uu____5990::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____6025 = unembed ea cb a1  in
                 FStar_Util.bind_opt uu____6025
                   (fun a2  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
             | Construct
                 (fvar,us,(b1,uu____6041)::uu____6042::uu____6043::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____6078 = unembed eb cb b1  in
                 FStar_Util.bind_opt uu____6078
                   (fun b2  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
             | uu____6091 -> FStar_Pervasives_Native.None)
         in
      let uu____6096 =
        let uu____6097 =
          let uu____6098 = let uu____6103 = type_of eb  in as_arg uu____6103
             in
          let uu____6104 =
            let uu____6111 =
              let uu____6116 = type_of ea  in as_arg uu____6116  in
            [uu____6111]  in
          uu____6098 :: uu____6104  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____6097
         in
      mk_emb em un uu____6096 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t1 =
    match t1 with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____6165 -> FStar_Pervasives_Native.None  in
  let uu____6166 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____6171 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____6166 uu____6171 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____6192 =
        let uu____6200 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____6200, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____6192  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____6227  ->
           let typ = let uu____6229 = type_of ea  in as_iarg uu____6229  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons hd tl =
             let uu____6250 =
               let uu____6251 = as_arg tl  in
               let uu____6256 =
                 let uu____6263 =
                   let uu____6268 = embed ea cb hd  in as_arg uu____6268  in
                 [uu____6263; typ]  in
               uu____6251 :: uu____6256  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____6250
              in
           FStar_List.fold_right cons l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____6316,uu____6317) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____6337,(tl,FStar_Pervasives_Native.None )::(hd,FStar_Pervasives_Native.None
                                                                   )::
                (uu____6340,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6341))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6369 = unembed ea cb hd  in
               FStar_Util.bind_opt uu____6369
                 (fun hd1  ->
                    let uu____6377 = un cb tl  in
                    FStar_Util.bind_opt uu____6377
                      (fun tl1  -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | Construct
               (fv,uu____6393,(tl,FStar_Pervasives_Native.None )::(hd,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6418 = unembed ea cb hd  in
               FStar_Util.bind_opt uu____6418
                 (fun hd1  ->
                    let uu____6426 = un cb tl  in
                    FStar_Util.bind_opt uu____6426
                      (fun tl1  -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | uu____6441 -> FStar_Pervasives_Native.None)
       in
    let uu____6444 =
      let uu____6445 =
        let uu____6446 = let uu____6451 = type_of ea  in as_arg uu____6451
           in
        [uu____6446]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____6445
       in
    mk_emb em un uu____6444 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____6525  ->
             let uu____6526 =
               let uu____6559 =
                 let uu____6580 =
                   let uu____6587 =
                     let uu____6592 = type_of eb  in as_arg uu____6592  in
                   [uu____6587]  in
                 FStar_Util.Inr uu____6580  in
               ((fun tas  ->
                   let uu____6650 =
                     let uu____6653 = FStar_List.hd tas  in
                     unembed ea cb uu____6653  in
                   match uu____6650 with
                   | FStar_Pervasives_Native.Some a1 ->
                       let uu____6655 = f a1  in embed eb cb uu____6655
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 uu____6559, Prims.int_one)
                in
             Lam uu____6526)
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____6702 =
                 let uu____6705 =
                   let uu____6706 =
                     let uu____6707 =
                       let uu____6712 = embed ea cb x  in as_arg uu____6712
                        in
                     [uu____6707]  in
                   cb.iapp lam1 uu____6706  in
                 unembed eb cb uu____6705  in
               match uu____6702 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____6726 =
        let uu____6727 = type_of ea  in
        let uu____6728 = let uu____6729 = type_of eb  in as_iarg uu____6729
           in
        make_arrow1 uu____6727 uu____6728  in
      mk_emb em un uu____6726 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n =
    match n with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____6747 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6747 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____6752 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6752 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____6757 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6757 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____6762 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6762 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____6767 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6767 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____6772 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6772 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____6777 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6777 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____6782 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6782 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____6787 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6787 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6796 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6797 =
          let uu____6798 =
            let uu____6803 =
              let uu____6804 = e_list e_string  in embed uu____6804 cb l  in
            as_arg uu____6803  in
          [uu____6798]  in
        mkFV uu____6796 [] uu____6797
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6826 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6827 =
          let uu____6828 =
            let uu____6833 =
              let uu____6834 = e_list e_string  in embed uu____6834 cb l  in
            as_arg uu____6833  in
          [uu____6828]  in
        mkFV uu____6826 [] uu____6827
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6856 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6857 =
          let uu____6858 =
            let uu____6863 =
              let uu____6864 = e_list e_string  in embed uu____6864 cb l  in
            as_arg uu____6863  in
          [uu____6858]  in
        mkFV uu____6856 [] uu____6857
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____6898,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6914,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6930,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6946,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6962,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6978,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6994,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____7010,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____7026,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____7042,(l,uu____7044)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____7063 =
          let uu____7069 = e_list e_string  in unembed uu____7069 cb l  in
        FStar_Util.bind_opt uu____7063
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7089  -> FStar_Pervasives_Native.Some uu____7089)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____7091,(l,uu____7093)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____7112 =
          let uu____7118 = e_list e_string  in unembed uu____7118 cb l  in
        FStar_Util.bind_opt uu____7112
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7138  -> FStar_Pervasives_Native.Some uu____7138)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____7140,(l,uu____7142)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____7161 =
          let uu____7167 = e_list e_string  in unembed uu____7167 cb l  in
        FStar_Util.bind_opt uu____7161
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7187  -> FStar_Pervasives_Native.Some uu____7187)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____7188 ->
        ((let uu____7190 =
            let uu____7196 =
              let uu____7198 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____7198
               in
            (FStar_Errors.Warning_NotEmbedded, uu____7196)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____7190);
         FStar_Pervasives_Native.None)
     in
  let uu____7202 =
    let uu____7203 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____7203 [] []  in
  let uu____7208 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____7202 uu____7208 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____7217  -> failwith "bogus_cbs translate")
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
    fun a1  ->
      let uu____7294 =
        let uu____7303 = e_list e  in unembed uu____7303 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu____7294
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____7325  ->
    match uu____7325 with
    | (a,uu____7333) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____7348)::[]) when
             let uu____7365 =
               FStar_Ident.string_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7365 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____7372 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t  ->
    fun n  ->
      let c = embed e_int bogus_cbs n  in
      let int_to_t1 args1 = FV (int_to_t, [], args1)  in
      let uu____7415 = let uu____7422 = as_arg c  in [uu____7422]  in
      int_to_t1 uu____7415
  
let lift_unary :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun aopts  ->
      match aopts with
      | (FStar_Pervasives_Native.Some a1)::[] ->
          let uu____7476 = f a1  in FStar_Pervasives_Native.Some uu____7476
      | uu____7477 -> FStar_Pervasives_Native.None
  
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
          let uu____7531 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____7531
      | uu____7532 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args1  ->
        let uu____7576 = FStar_List.map as_a args1  in
        lift_unary f uu____7576
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args1  ->
        let uu____7631 = FStar_List.map as_a args1  in
        lift_binary f uu____7631
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____7661 = f x  in embed e_int bogus_cbs uu____7661)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____7688 = f x y  in embed e_int bogus_cbs uu____7688)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____7714 = f x  in embed e_bool bogus_cbs uu____7714)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____7752 = f x y  in embed e_bool bogus_cbs uu____7752)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____7790 = f x y  in embed e_string bogus_cbs uu____7790)
  
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
          fun args1  ->
            match args1 with
            | a1::b1::[] ->
                let uu____7895 =
                  let uu____7904 = as_a a1  in
                  let uu____7907 = as_b b1  in (uu____7904, uu____7907)  in
                (match uu____7895 with
                 | (FStar_Pervasives_Native.Some
                    a2,FStar_Pervasives_Native.Some b2) ->
                     let uu____7922 =
                       let uu____7923 = f a2 b2  in embed_c uu____7923  in
                     FStar_Pervasives_Native.Some uu____7922
                 | uu____7924 -> FStar_Pervasives_Native.None)
            | uu____7933 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7942 = e_list e_char  in
    let uu____7949 = FStar_String.list_of_string s  in
    embed uu____7942 bogus_cbs uu____7949
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7988 =
        let uu____7989 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7989  in
      embed e_int bogus_cbs uu____7988
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8023 = arg_as_string a1  in
        (match uu____8023 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8032 = arg_as_list e_string a2  in
             (match uu____8032 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____8050 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____8050
              | uu____8052 -> FStar_Pervasives_Native.None)
         | uu____8058 -> FStar_Pervasives_Native.None)
    | uu____8062 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____8069 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____8069
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cbs (if b then "true" else "false") 
let (string_lowercase : Prims.string -> t) =
  fun s  -> embed e_string bogus_cbs (FStar_String.lowercase s) 
let (string_uppercase : Prims.string -> t) =
  fun s  -> embed e_string bogus_cbs (FStar_String.lowercase s) 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args1  ->
      let tru = embed e_bool bogus_cbs true  in
      let fal = embed e_bool bogus_cbs false  in
      match args1 with
      | (_typ,uu____8131)::(a1,uu____8133)::(a2,uu____8135)::[] ->
          let uu____8152 = eq_t a1 a2  in
          (match uu____8152 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____8161 -> FStar_Pervasives_Native.None)
      | uu____8162 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (_u,uu____8177)::(_typ,uu____8179)::(a1,uu____8181)::(a2,uu____8183)::[]
        ->
        let uu____8204 = eq_t a1 a2  in
        (match uu____8204 with
         | FStar_Syntax_Util.Equal  ->
             let uu____8207 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____8207
         | FStar_Syntax_Util.NotEqual  ->
             let uu____8210 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____8210
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____8213 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (_u,uu____8228)::(_v,uu____8230)::(t1,uu____8232)::(t2,uu____8234)::
        (a1,uu____8236)::(a2,uu____8238)::[] ->
        let uu____8267 =
          let uu____8268 = eq_t t1 t2  in
          let uu____8269 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____8268 uu____8269  in
        (match uu____8267 with
         | FStar_Syntax_Util.Equal  ->
             let uu____8272 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____8272
         | FStar_Syntax_Util.NotEqual  ->
             let uu____8275 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____8275
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____8278 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args1  ->
      let uu____8297 =
        let uu____8299 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____8299  in
      failwith uu____8297
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (a1,uu____8315)::[] ->
        let uu____8324 = unembed e_range bogus_cbs a1  in
        (match uu____8324 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8330 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8330
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8331 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8367 = arg_as_list e_char a1  in
        (match uu____8367 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8383 = arg_as_string a2  in
             (match uu____8383 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____8396 =
                    let uu____8397 = e_list e_string  in
                    embed uu____8397 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____8396
              | uu____8407 -> FStar_Pervasives_Native.None)
         | uu____8411 -> FStar_Pervasives_Native.None)
    | uu____8417 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8450 =
          let uu____8460 = arg_as_string a1  in
          let uu____8464 = arg_as_int a2  in (uu____8460, uu____8464)  in
        (match uu____8450 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1024_8488  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____8493 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8493) ()
              with | uu___1023_8496 -> FStar_Pervasives_Native.None)
         | uu____8499 -> FStar_Pervasives_Native.None)
    | uu____8509 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8542 =
          let uu____8553 = arg_as_string a1  in
          let uu____8557 = arg_as_char a2  in (uu____8553, uu____8557)  in
        (match uu____8542 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1042_8586  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____8590 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8590) ()
              with | uu___1041_8592 -> FStar_Pervasives_Native.None)
         | uu____8595 -> FStar_Pervasives_Native.None)
    | uu____8606 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::a3::[] ->
        let uu____8648 =
          let uu____8662 = arg_as_string a1  in
          let uu____8666 = arg_as_int a2  in
          let uu____8669 = arg_as_int a3  in
          (uu____8662, uu____8666, uu____8669)  in
        (match uu____8648 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1065_8702  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____8707 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8707) ()
              with | uu___1064_8710 -> FStar_Pervasives_Native.None)
         | uu____8713 -> FStar_Pervasives_Native.None)
    | uu____8727 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8787 =
          let uu____8809 = arg_as_string fn  in
          let uu____8813 = arg_as_int from_line  in
          let uu____8816 = arg_as_int from_col  in
          let uu____8819 = arg_as_int to_line  in
          let uu____8822 = arg_as_int to_col  in
          (uu____8809, uu____8813, uu____8816, uu____8819, uu____8822)  in
        (match uu____8787 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8857 =
                 let uu____8858 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8860 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8858 uu____8860  in
               let uu____8862 =
                 let uu____8863 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8865 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8863 uu____8865  in
               FStar_Range.mk_range fn1 uu____8857 uu____8862  in
             let uu____8867 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8867
         | uu____8868 -> FStar_Pervasives_Native.None)
    | uu____8890 -> FStar_Pervasives_Native.None
  
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
              let f_wrapped args1 =
                let uu____8980 = FStar_List.splitAt n_tvars args1  in
                match uu____8980 with
                | (_tvar_args,rest_args) ->
                    let uu____9029 = FStar_List.hd rest_args  in
                    (match uu____9029 with
                     | (x,uu____9041) ->
                         let uu____9042 = unembed ea cb x  in
                         FStar_Util.map_opt uu____9042
                           (fun x1  ->
                              let uu____9048 = f x1  in
                              embed eb cb uu____9048))
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
                let f_wrapped args1 =
                  let uu____9157 = FStar_List.splitAt n_tvars args1  in
                  match uu____9157 with
                  | (_tvar_args,rest_args) ->
                      let uu____9206 = FStar_List.hd rest_args  in
                      (match uu____9206 with
                       | (x,uu____9218) ->
                           let uu____9219 =
                             let uu____9224 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____9224  in
                           (match uu____9219 with
                            | (y,uu____9242) ->
                                let uu____9243 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____9243
                                  (fun x1  ->
                                     let uu____9249 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____9249
                                       (fun y1  ->
                                          let uu____9255 =
                                            let uu____9256 = f x1 y1  in
                                            embed ec cb uu____9256  in
                                          FStar_Pervasives_Native.Some
                                            uu____9255))))
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
                  let f_wrapped args1 =
                    let uu____9384 = FStar_List.splitAt n_tvars args1  in
                    match uu____9384 with
                    | (_tvar_args,rest_args) ->
                        let uu____9433 = FStar_List.hd rest_args  in
                        (match uu____9433 with
                         | (x,uu____9445) ->
                             let uu____9446 =
                               let uu____9451 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____9451  in
                             (match uu____9446 with
                              | (y,uu____9469) ->
                                  let uu____9470 =
                                    let uu____9475 =
                                      let uu____9482 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____9482  in
                                    FStar_List.hd uu____9475  in
                                  (match uu____9470 with
                                   | (z,uu____9504) ->
                                       let uu____9505 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____9505
                                         (fun x1  ->
                                            let uu____9511 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____9511
                                              (fun y1  ->
                                                 let uu____9517 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____9517
                                                   (fun z1  ->
                                                      let uu____9523 =
                                                        let uu____9524 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____9524
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____9523))))))
                     in
                  f_wrapped
  