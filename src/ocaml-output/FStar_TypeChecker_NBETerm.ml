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
  fun projectee -> match projectee with | Unit -> true | uu____64 -> false
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> true | uu____77 -> false
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> _0
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee -> match projectee with | Int _0 -> true | uu____99 -> false
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee -> match projectee with | Int _0 -> _0
let (uu___is_String : constant -> Prims.bool) =
  fun projectee ->
    match projectee with | String _0 -> true | uu____123 -> false
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee ->
    match projectee with | Char _0 -> true | uu____158 -> false
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee -> match projectee with | Char _0 -> _0
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee ->
    match projectee with | Range _0 -> true | uu____180 -> false
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee -> match projectee with | Range _0 -> _0
let (uu___is_SConst : constant -> Prims.bool) =
  fun projectee ->
    match projectee with | SConst _0 -> true | uu____199 -> false
let (__proj__SConst__item___0 : constant -> FStar_Const.sconst) =
  fun projectee -> match projectee with | SConst _0 -> _0
type atom =
  | Var of var 
  | Match of (t * (unit -> FStar_Syntax_Syntax.branch Prims.list)) 
  | UnreducedLet of (var * t FStar_Thunk.t * t FStar_Thunk.t * t
  FStar_Thunk.t * FStar_Syntax_Syntax.letbinding) 
  | UnreducedLetRec of ((var * t * t) Prims.list * t *
  FStar_Syntax_Syntax.letbinding Prims.list) 
  | UVar of FStar_Syntax_Syntax.term FStar_Thunk.t 
and t' =
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
  | Arrow of (FStar_Syntax_Syntax.term FStar_Thunk.t,
  ((t * FStar_Syntax_Syntax.aqual) Prims.list * comp)) FStar_Util.either 
  | Refinement of ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual))) 
  | Reflect of t 
  | Quote of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo) 
  | Lazy of ((FStar_Syntax_Syntax.lazyinfo,
  (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Util.either * t
  FStar_Thunk.t) 
  | Meta of (t * FStar_Syntax_Syntax.metadata FStar_Thunk.t) 
  | TopLevelLet of (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
  FStar_Syntax_Syntax.aqual) Prims.list) 
  | TopLevelRec of (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | LocalLetRec of (Prims.int * FStar_Syntax_Syntax.letbinding *
  FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
  FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool Prims.list) 
and t = {
  nbe_t: t' ;
  nbe_r: FStar_Range.range }
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
  fun projectee -> match projectee with | Var _0 -> true | uu____683 -> false
let (__proj__Var__item___0 : atom -> var) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | Match _0 -> true | uu____711 -> false
let (__proj__Match__item___0 :
  atom -> (t * (unit -> FStar_Syntax_Syntax.branch Prims.list))) =
  fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UnreducedLet _0 -> true | uu____773 -> false
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStar_Thunk.t * t FStar_Thunk.t * t FStar_Thunk.t *
      FStar_Syntax_Syntax.letbinding))
  = fun projectee -> match projectee with | UnreducedLet _0 -> _0
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UnreducedLetRec _0 -> true | uu____856 -> false
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee -> match projectee with | UnreducedLetRec _0 -> _0
let (uu___is_UVar : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UVar _0 -> true | uu____925 -> false
let (__proj__UVar__item___0 : atom -> FStar_Syntax_Syntax.term FStar_Thunk.t)
  = fun projectee -> match projectee with | UVar _0 -> _0
let (uu___is_Lam : t' -> Prims.bool) =
  fun projectee -> match projectee with | Lam _0 -> true | uu____982 -> false
let (__proj__Lam__item___0 :
  t' ->
    ((t Prims.list -> t) *
      ((t Prims.list * FStar_Syntax_Syntax.binders *
         FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
      (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Util.either *
      Prims.int))
  = fun projectee -> match projectee with | Lam _0 -> _0
let (uu___is_Accu : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Accu _0 -> true | uu____1107 -> false
let (__proj__Accu__item___0 :
  t' -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee -> match projectee with | Accu _0 -> _0
let (uu___is_Construct : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Construct _0 -> true | uu____1170 -> false
let (__proj__Construct__item___0 :
  t' ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | Construct _0 -> _0
let (uu___is_FV : t' -> Prims.bool) =
  fun projectee -> match projectee with | FV _0 -> true | uu____1245 -> false
let (__proj__FV__item___0 :
  t' ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | FV _0 -> _0
let (uu___is_Constant : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Constant _0 -> true | uu____1306 -> false
let (__proj__Constant__item___0 : t' -> constant) =
  fun projectee -> match projectee with | Constant _0 -> _0
let (uu___is_Type_t : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Type_t _0 -> true | uu____1325 -> false
let (__proj__Type_t__item___0 : t' -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Type_t _0 -> _0
let (uu___is_Univ : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Univ _0 -> true | uu____1344 -> false
let (__proj__Univ__item___0 : t' -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Unknown : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Unknown -> true | uu____1362 -> false
let (uu___is_Arrow : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Arrow _0 -> true | uu____1390 -> false
let (__proj__Arrow__item___0 :
  t' ->
    (FStar_Syntax_Syntax.term FStar_Thunk.t,
      ((t * FStar_Syntax_Syntax.aqual) Prims.list * comp)) FStar_Util.either)
  = fun projectee -> match projectee with | Arrow _0 -> _0
let (uu___is_Refinement : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Refinement _0 -> true | uu____1471 -> false
let (__proj__Refinement__item___0 :
  t' -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee -> match projectee with | Refinement _0 -> _0
let (uu___is_Reflect : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Reflect _0 -> true | uu____1532 -> false
let (__proj__Reflect__item___0 : t' -> t) =
  fun projectee -> match projectee with | Reflect _0 -> _0
let (uu___is_Quote : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Quote _0 -> true | uu____1555 -> false
let (__proj__Quote__item___0 :
  t' -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee -> match projectee with | Quote _0 -> _0
let (uu___is_Lazy : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Lazy _0 -> true | uu____1600 -> false
let (__proj__Lazy__item___0 :
  t' ->
    ((FStar_Syntax_Syntax.lazyinfo,
      (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Util.either * t
      FStar_Thunk.t))
  = fun projectee -> match projectee with | Lazy _0 -> _0
let (uu___is_Meta : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____1667 -> false
let (__proj__Meta__item___0 :
  t' -> (t * FStar_Syntax_Syntax.metadata FStar_Thunk.t)) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_TopLevelLet : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelLet _0 -> true | uu____1717 -> false
let (__proj__TopLevelLet__item___0 :
  t' ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | TopLevelLet _0 -> _0
let (uu___is_TopLevelRec : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelRec _0 -> true | uu____1793 -> false
let (__proj__TopLevelRec__item___0 :
  t' ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | TopLevelRec _0 -> _0
let (uu___is_LocalLetRec : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | LocalLetRec _0 -> true | uu____1895 -> false
let (__proj__LocalLetRec__item___0 :
  t' ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee -> match projectee with | LocalLetRec _0 -> _0
let (__proj__Mkt__item__nbe_t : t -> t') =
  fun projectee -> match projectee with | { nbe_t; nbe_r;_} -> nbe_t
let (__proj__Mkt__item__nbe_r : t -> FStar_Range.range) =
  fun projectee -> match projectee with | { nbe_t; nbe_r;_} -> nbe_r
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee ->
    match projectee with | Tot _0 -> true | uu____2023 -> false
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Tot _0 -> _0
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee ->
    match projectee with | GTot _0 -> true | uu____2066 -> false
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | GTot _0 -> _0
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee ->
    match projectee with | Comp _0 -> true | uu____2103 -> false
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee -> match projectee with | Comp _0 -> _0
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStar_Syntax_Syntax.universes) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        comp_univs
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_name
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        result_typ
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ -> (t * FStar_Syntax_Syntax.aqual) Prims.list) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_args
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} -> flags
let (uu___is_TOTAL : cflag -> Prims.bool) =
  fun projectee -> match projectee with | TOTAL -> true | uu____2232 -> false
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | MLEFFECT -> true | uu____2243 -> false
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | RETURN -> true | uu____2254 -> false
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | PARTIAL_RETURN -> true | uu____2265 -> false
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SOMETRIVIAL -> true | uu____2276 -> false
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TRIVIAL_POSTCONDITION -> true
    | uu____2287 -> false
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SHOULD_NOT_INLINE -> true | uu____2298 -> false
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee -> match projectee with | LEMMA -> true | uu____2309 -> false
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee -> match projectee with | CPS -> true | uu____2320 -> false
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | DECREASES _0 -> true | uu____2332 -> false
let (__proj__DECREASES__item___0 : cflag -> t) =
  fun projectee -> match projectee with | DECREASES _0 -> _0
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_effect
let (__proj__Mkresidual_comp__item__residual_typ :
  residual_comp -> t FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_typ
let (__proj__Mkresidual_comp__item__residual_flags :
  residual_comp -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_flags
type arg = (t * FStar_Syntax_Syntax.aqual)
type args = (t * FStar_Syntax_Syntax.aqual) Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (isAccu : t -> Prims.bool) =
  fun trm ->
    match trm.nbe_t with | Accu uu____2408 -> true | uu____2420 -> false
let (isNotAccu : t -> Prims.bool) =
  fun x ->
    match x.nbe_t with
    | Accu (uu____2430, uu____2431) -> false
    | uu____2445 -> true
let (mk_rt : FStar_Range.range -> t' -> t) =
  fun r -> fun t1 -> { nbe_t = t1; nbe_r = r }
let (mk_t : t' -> t) = fun t1 -> mk_rt FStar_Range.dummyRange t1
let (nbe_t_of_t : t -> t') = fun t1 -> t1.nbe_t
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun i ->
    fun us -> fun ts -> FStar_All.pipe_left mk_t (Construct (i, us, ts))
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun i ->
    fun us ->
      fun ts ->
        let uu____2518 = FStar_Syntax_Syntax.range_of_fv i in
        mk_rt uu____2518 (FV (i, us, ts))
let (mkAccuVar : var -> t) =
  fun v ->
    let uu____2533 = FStar_Syntax_Syntax.range_of_bv v in
    mk_rt uu____2533 (Accu ((Var v), []))
let (mkAccuMatch : t -> (unit -> FStar_Syntax_Syntax.branch Prims.list) -> t)
  = fun s -> fun bs -> FStar_All.pipe_left mk_t (Accu ((Match (s, bs)), []))
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___0_2585 ->
    if uu___0_2585
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2596 ->
    if uu___1_2596
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.NotEqual
let (eq_inj :
  FStar_Syntax_Util.eq_result ->
    FStar_Syntax_Util.eq_result -> FStar_Syntax_Util.eq_result)
  =
  fun r1 ->
    fun r2 ->
      match (r1, r2) with
      | (FStar_Syntax_Util.Equal, FStar_Syntax_Util.Equal) ->
          FStar_Syntax_Util.Equal
      | (FStar_Syntax_Util.NotEqual, uu____2612) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2613, FStar_Syntax_Util.NotEqual) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown, uu____2614) -> FStar_Syntax_Util.Unknown
      | (uu____2615, FStar_Syntax_Util.Unknown) -> FStar_Syntax_Util.Unknown
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f ->
    fun g ->
      match f with
      | FStar_Syntax_Util.Equal -> g ()
      | uu____2632 -> FStar_Syntax_Util.Unknown
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (Unit, Unit) -> FStar_Syntax_Util.Equal
      | (Bool b1, Bool b2) -> equal_iff (b1 = b2)
      | (Int i1, Int i2) -> equal_iff (i1 = i2)
      | (String (s1, uu____2652), String (s2, uu____2654)) ->
          equal_iff (s1 = s2)
      | (Char c11, Char c21) -> equal_iff (c11 = c21)
      | (Range r1, Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2667, uu____2668) -> FStar_Syntax_Util.NotEqual
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1 ->
    fun t2 ->
      match ((t1.nbe_t), (t2.nbe_t)) with
      | (Lam uu____2704, Lam uu____2705) -> FStar_Syntax_Util.Unknown
      | (Accu (a1, as1), Accu (a2, as2)) ->
          let uu____2798 = eq_atom a1 a2 in
          eq_and uu____2798 (fun uu____2800 -> eq_args as1 as2)
      | (Construct (v1, us1, args1), Construct (v2, us2, args2)) ->
          let uu____2839 = FStar_Syntax_Syntax.fv_eq v1 v2 in
          if uu____2839
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2855 = FStar_List.zip args1 args2 in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc ->
                      fun uu____2912 ->
                        match uu____2912 with
                        | ((a1, uu____2926), (a2, uu____2928)) ->
                            let uu____2937 = eq_t a1 a2 in
                            eq_inj acc uu____2937) FStar_Syntax_Util.Equal)
                uu____2855))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1, us1, args1), FV (v2, us2, args2)) ->
          let uu____2978 = FStar_Syntax_Syntax.fv_eq v1 v2 in
          if uu____2978
          then
            let uu____2981 =
              let uu____2982 = FStar_Syntax_Util.eq_univs_list us1 us2 in
              equal_iff uu____2982 in
            eq_and uu____2981 (fun uu____2985 -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1, Constant c2) -> eq_constant c1 c2
      | (Type_t u1, Type_t u2) ->
          let uu____2992 = FStar_Syntax_Util.eq_univs u1 u2 in
          equal_iff uu____2992
      | (Univ u1, Univ u2) ->
          let uu____2996 = FStar_Syntax_Util.eq_univs u1 u2 in
          equal_iff uu____2996
      | (Refinement (r1, t11), Refinement (r2, t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit in
          let uu____3043 =
            let uu____3044 =
              let uu____3045 = t11 () in
              FStar_Pervasives_Native.fst uu____3045 in
            let uu____3050 =
              let uu____3051 = t21 () in
              FStar_Pervasives_Native.fst uu____3051 in
            eq_t uu____3044 uu____3050 in
          eq_and uu____3043
            (fun uu____3059 ->
               let uu____3060 = let uu____3061 = mkAccuVar x in r1 uu____3061 in
               let uu____3062 = let uu____3063 = mkAccuVar x in r2 uu____3063 in
               eq_t uu____3060 uu____3062)
      | (Unknown, Unknown) -> FStar_Syntax_Util.Equal
      | (uu____3064, uu____3065) -> FStar_Syntax_Util.Unknown
and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (Var bv1, Var bv2) ->
          let uu____3070 = FStar_Syntax_Syntax.bv_eq bv1 bv2 in
          equal_if uu____3070
      | (uu____3072, uu____3073) -> FStar_Syntax_Util.Unknown
and (eq_arg : arg -> arg -> FStar_Syntax_Util.eq_result) =
  fun a1 ->
    fun a2 ->
      eq_t (FStar_Pervasives_Native.fst a1) (FStar_Pervasives_Native.fst a2)
and (eq_args : args -> args -> FStar_Syntax_Util.eq_result) =
  fun as1 ->
    fun as2 ->
      match (as1, as2) with
      | ([], []) -> FStar_Syntax_Util.Equal
      | (x::xs, y::ys) ->
          let uu____3154 = eq_arg x y in
          eq_and uu____3154 (fun uu____3156 -> eq_args xs ys)
      | (uu____3157, uu____3158) -> FStar_Syntax_Util.Unknown
let (constant_to_string : constant -> Prims.string) =
  fun c ->
    match c with
    | Unit -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s, uu____3205) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____3210 = FStar_Range.string_of_range r in
        FStar_Util.format1 "Range %s" uu____3210
    | SConst s -> FStar_Syntax_Print.const_to_string s
let rec (t_to_string : t -> Prims.string) =
  fun x ->
    match x.nbe_t with
    | Lam (b, uu____3228, arity) ->
        let uu____3282 = FStar_Util.string_of_int arity in
        FStar_Util.format1 "Lam (_, %s args)" uu____3282
    | Accu (a, l) ->
        let uu____3299 =
          let uu____3301 = atom_to_string a in
          let uu____3303 =
            let uu____3305 =
              let uu____3307 =
                let uu____3309 =
                  FStar_List.map
                    (fun x1 -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l in
                FStar_String.concat "; " uu____3309 in
              FStar_String.op_Hat uu____3307 ")" in
            FStar_String.op_Hat ") (" uu____3305 in
          FStar_String.op_Hat uu____3301 uu____3303 in
        FStar_String.op_Hat "Accu (" uu____3299
    | Construct (fv, us, l) ->
        let uu____3347 =
          let uu____3349 = FStar_Syntax_Print.fv_to_string fv in
          let uu____3351 =
            let uu____3353 =
              let uu____3355 =
                let uu____3357 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us in
                FStar_String.concat "; " uu____3357 in
              let uu____3363 =
                let uu____3365 =
                  let uu____3367 =
                    let uu____3369 =
                      FStar_List.map
                        (fun x1 ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStar_String.concat "; " uu____3369 in
                  FStar_String.op_Hat uu____3367 "]" in
                FStar_String.op_Hat "] [" uu____3365 in
              FStar_String.op_Hat uu____3355 uu____3363 in
            FStar_String.op_Hat ") [" uu____3353 in
          FStar_String.op_Hat uu____3349 uu____3351 in
        FStar_String.op_Hat "Construct (" uu____3347
    | FV (fv, us, l) ->
        let uu____3408 =
          let uu____3410 = FStar_Syntax_Print.fv_to_string fv in
          let uu____3412 =
            let uu____3414 =
              let uu____3416 =
                let uu____3418 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us in
                FStar_String.concat "; " uu____3418 in
              let uu____3424 =
                let uu____3426 =
                  let uu____3428 =
                    let uu____3430 =
                      FStar_List.map
                        (fun x1 ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStar_String.concat "; " uu____3430 in
                  FStar_String.op_Hat uu____3428 "]" in
                FStar_String.op_Hat "] [" uu____3426 in
              FStar_String.op_Hat uu____3416 uu____3424 in
            FStar_String.op_Hat ") [" uu____3414 in
          FStar_String.op_Hat uu____3410 uu____3412 in
        FStar_String.op_Hat "FV (" uu____3408
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3452 = FStar_Syntax_Print.univ_to_string u in
        FStar_String.op_Hat "Universe " uu____3452
    | Type_t u ->
        let uu____3456 = FStar_Syntax_Print.univ_to_string u in
        FStar_String.op_Hat "Type_t " uu____3456
    | Arrow uu____3459 -> "Arrow"
    | Refinement (f, t1) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit in
        let t2 =
          let uu____3501 = t1 () in FStar_Pervasives_Native.fst uu____3501 in
        let uu____3506 =
          let uu____3508 = FStar_Syntax_Print.bv_to_string x1 in
          let uu____3510 =
            let uu____3512 =
              let uu____3514 = t_to_string t2 in
              let uu____3516 =
                let uu____3518 =
                  let uu____3520 =
                    let uu____3522 =
                      let uu____3523 = mkAccuVar x1 in f uu____3523 in
                    t_to_string uu____3522 in
                  FStar_String.op_Hat uu____3520 "}" in
                FStar_String.op_Hat "{" uu____3518 in
              FStar_String.op_Hat uu____3514 uu____3516 in
            FStar_String.op_Hat ":" uu____3512 in
          FStar_String.op_Hat uu____3508 uu____3510 in
        FStar_String.op_Hat "Refinement " uu____3506
    | Unknown -> "Unknown"
    | Reflect t1 ->
        let uu____3530 = t_to_string t1 in
        FStar_String.op_Hat "Reflect " uu____3530
    | Quote uu____3533 -> "Quote _"
    | Lazy (FStar_Util.Inl li, uu____3540) ->
        let uu____3557 =
          let uu____3559 = FStar_Syntax_Util.unfold_lazy li in
          FStar_Syntax_Print.term_to_string uu____3559 in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3557
    | Lazy (FStar_Util.Inr (uu____3561, et), uu____3563) ->
        let uu____3580 = FStar_Syntax_Print.emb_typ_to_string et in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3580
    | LocalLetRec
        (uu____3583, l, uu____3585, uu____3586, uu____3587, uu____3588,
         uu____3589)
        ->
        let uu____3620 =
          let uu____3622 = FStar_Syntax_Print.lbs_to_string [] (true, [l]) in
          FStar_String.op_Hat uu____3622 ")" in
        FStar_String.op_Hat "LocalLetRec (" uu____3620
    | TopLevelLet (lb, uu____3631, uu____3632) ->
        let uu____3647 =
          let uu____3649 =
            let uu____3651 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            FStar_Syntax_Print.fv_to_string uu____3651 in
          FStar_String.op_Hat uu____3649 ")" in
        FStar_String.op_Hat "TopLevelLet (" uu____3647
    | TopLevelRec (lb, uu____3655, uu____3656, uu____3657) ->
        let uu____3678 =
          let uu____3680 =
            let uu____3682 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            FStar_Syntax_Print.fv_to_string uu____3682 in
          FStar_String.op_Hat uu____3680 ")" in
        FStar_String.op_Hat "TopLevelRec (" uu____3678
and (atom_to_string : atom -> Prims.string) =
  fun a ->
    match a with
    | Var v ->
        let uu____3688 = FStar_Syntax_Print.bv_to_string v in
        FStar_String.op_Hat "Var " uu____3688
    | Match (t1, uu____3692) ->
        let uu____3703 = t_to_string t1 in
        FStar_String.op_Hat "Match " uu____3703
    | UnreducedLet (var1, typ, def, body, lb) ->
        let uu____3723 =
          let uu____3725 = FStar_Syntax_Print.lbs_to_string [] (false, [lb]) in
          FStar_String.op_Hat uu____3725 " in ...)" in
        FStar_String.op_Hat "UnreducedLet(" uu____3723
    | UnreducedLetRec (uu____3733, body, lbs) ->
        let uu____3756 =
          let uu____3758 = FStar_Syntax_Print.lbs_to_string [] (true, lbs) in
          let uu____3764 =
            let uu____3766 =
              let uu____3768 = t_to_string body in
              FStar_String.op_Hat uu____3768 ")" in
            FStar_String.op_Hat " in " uu____3766 in
          FStar_String.op_Hat uu____3758 uu____3764 in
        FStar_String.op_Hat "UnreducedLetRec(" uu____3756
    | UVar uu____3773 -> "UVar"
let (arg_to_string : arg -> Prims.string) =
  fun a ->
    let uu____3784 = FStar_All.pipe_right a FStar_Pervasives_Native.fst in
    FStar_All.pipe_right uu____3784 t_to_string
let (args_to_string : args -> Prims.string) =
  fun args1 ->
    let uu____3797 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____3797 (FStar_String.concat " ")
type nbe_cbs =
  {
  iapp: t -> args -> t ;
  translate: FStar_Syntax_Syntax.term -> t }
let (__proj__Mknbe_cbs__item__iapp : nbe_cbs -> t -> args -> t) =
  fun projectee -> match projectee with | { iapp; translate;_} -> iapp
let (__proj__Mknbe_cbs__item__translate :
  nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun projectee -> match projectee with | { iapp; translate;_} -> translate
let (iapp_cb : nbe_cbs -> t -> args -> t) =
  fun cbs -> fun h -> fun a -> cbs.iapp h a
let (translate_cb : nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun cbs -> fun t1 -> cbs.translate t1
type 'a embedding =
  {
  em: nbe_cbs -> 'a -> t ;
  un: nbe_cbs -> t -> 'a FStar_Pervasives_Native.option ;
  typ: t ;
  emb_typ: FStar_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun projectee -> match projectee with | { em; un; typ; emb_typ;_} -> em
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee -> match projectee with | { em; un; typ; emb_typ;_} -> un
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee -> match projectee with | { em; un; typ; emb_typ;_} -> typ
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee ->
    match projectee with | { em; un; typ; emb_typ;_} -> emb_typ
let embed : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun e -> fun cb -> fun x -> e.em cb x
let unembed :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun e -> fun cb -> fun trm -> e.un cb trm
let type_of : 'a . 'a embedding -> t = fun e -> e.typ
let mk_emb :
  'a .
    (nbe_cbs -> 'a -> t) ->
      (nbe_cbs -> t -> 'a FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  = fun em -> fun un -> fun typ -> fun et -> { em; un; typ; emb_typ = et }
let mk_emb' :
  'uuuuuu4257 .
    (nbe_cbs -> 'uuuuuu4257 -> t') ->
      (nbe_cbs -> t' -> 'uuuuuu4257 FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'uuuuuu4257 embedding
  =
  fun em ->
    fun un ->
      mk_emb
        (fun cbs ->
           fun t1 ->
             let uu____4307 = em cbs t1 in
             FStar_All.pipe_left mk_t uu____4307)
        (fun cbs -> fun t1 -> un cbs t1.nbe_t)
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) -> t FStar_Pervasives_Native.option -> 'b embedding
  =
  fun ea ->
    fun ab ->
      fun ba ->
        fun ot ->
          mk_emb
            (fun cbs ->
               fun x -> let uu____4372 = ba x in embed ea cbs uu____4372)
            (fun cbs ->
               fun t1 ->
                 let uu____4378 = unembed ea cbs t1 in
                 FStar_Util.map_opt uu____4378 ab)
            (match ot with
             | FStar_Pervasives_Native.Some t1 -> t1
             | FStar_Pervasives_Native.None -> ea.typ) ea.emb_typ
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l ->
    fun us ->
      fun args1 ->
        let uu____4403 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
        mkConstruct uu____4403 us args1
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l ->
    fun us ->
      fun args1 ->
        let uu____4424 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None in
        mkFV uu____4424 us args1
let (as_iarg : t -> arg) =
  fun a -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
let (as_arg : t -> arg) = fun a -> (a, FStar_Pervasives_Native.None)
let (make_arrow1 : t -> arg -> t) =
  fun t1 ->
    fun a ->
      FStar_All.pipe_left mk_t
        (Arrow
           (FStar_Util.Inr ([a], (Tot (t1, FStar_Pervasives_Native.None)))))
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et ->
    fun x ->
      fun f ->
        (let uu____4507 = FStar_ST.op_Bang FStar_Options.debug_embedding in
         if uu____4507
         then
           let uu____4531 = FStar_Syntax_Print.emb_typ_to_string et in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4531
         else ());
        (let uu____4536 = FStar_ST.op_Bang FStar_Options.eager_embedding in
         if uu____4536
         then f ()
         else
           (let thunk = FStar_Thunk.mk f in
            let li = let uu____4570 = FStar_Dyn.mkdyn x in (uu____4570, et) in
            FStar_All.pipe_left mk_t (Lazy ((FStar_Util.Inr li), thunk))))
let lazy_unembed :
  'uuuuuu4598 'a .
    'uuuuuu4598 ->
      FStar_Syntax_Syntax.emb_typ ->
        t ->
          (t -> 'a FStar_Pervasives_Native.option) ->
            'a FStar_Pervasives_Native.option
  =
  fun cb ->
    fun et ->
      fun x ->
        fun f ->
          match x.nbe_t with
          | Lazy (FStar_Util.Inl li, thunk) ->
              let uu____4649 = FStar_Thunk.force thunk in f uu____4649
          | Lazy (FStar_Util.Inr (b, et'), thunk) ->
              let uu____4669 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding) in
              if uu____4669
              then
                let res =
                  let uu____4698 = FStar_Thunk.force thunk in f uu____4698 in
                ((let uu____4700 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____4700
                  then
                    let uu____4724 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu____4726 = FStar_Syntax_Print.emb_typ_to_string et' in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4724
                      uu____4726
                  else ());
                 res)
              else
                (let a1 = FStar_Dyn.undyn b in
                 (let uu____4735 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu____4735
                  then
                    let uu____4759 = FStar_Syntax_Print.emb_typ_to_string et in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4759
                  else ());
                 FStar_Pervasives_Native.Some a1)
          | uu____4764 ->
              let aopt = f x in
              ((let uu____4769 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu____4769
                then
                  let uu____4793 = FStar_Syntax_Print.emb_typ_to_string et in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4793
                else ());
               aopt)
let (mk_any_emb : t -> t embedding) =
  fun ty ->
    let em _cb a = a in
    let un _cb t1 = FStar_Pervasives_Native.Some t1 in
    mk_emb em un ty FStar_Syntax_Syntax.ET_abstract
let (e_any : t embedding) =
  let em _cb a = a in
  let un _cb t1 = FStar_Pervasives_Native.Some t1 in
  let uu____4861 = lid_as_typ FStar_Parser_Const.term_lid [] [] in
  mk_emb em un uu____4861 FStar_Syntax_Syntax.ET_abstract
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit in
  let un _cb t1 = FStar_Pervasives_Native.Some () in
  let uu____4895 = lid_as_typ FStar_Parser_Const.unit_lid [] [] in
  let uu____4900 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
  mk_emb' em un uu____4895 uu____4900
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a) in
  let un _cb t1 =
    match t1 with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4941 -> FStar_Pervasives_Native.None in
  let uu____4943 = lid_as_typ FStar_Parser_Const.bool_lid [] [] in
  let uu____4948 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
  mk_emb' em un uu____4943 uu____4948
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c) in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4990 -> FStar_Pervasives_Native.None in
  let uu____4992 = lid_as_typ FStar_Parser_Const.char_lid [] [] in
  let uu____4997 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char in
  mk_emb' em un uu____4992 uu____4997
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange)) in
  let un _cb s =
    match s with
    | Constant (String (s1, uu____5039)) -> FStar_Pervasives_Native.Some s1
    | uu____5043 -> FStar_Pervasives_Native.None in
  let uu____5045 = lid_as_typ FStar_Parser_Const.string_lid [] [] in
  let uu____5050 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string in
  mk_emb' em un uu____5045 uu____5050
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c) in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____5085 -> FStar_Pervasives_Native.None in
  let uu____5086 = lid_as_typ FStar_Parser_Const.int_lid [] [] in
  let uu____5091 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int in
  mk_emb' em un uu____5086 uu____5091
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let etyp =
      let uu____5112 =
        let uu____5120 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu____5120, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____5112 in
    let em cb o =
      lazy_embed etyp o
        (fun uu____5145 ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu____5146 =
                 let uu____5147 =
                   let uu____5152 = type_of ea in as_iarg uu____5152 in
                 [uu____5147] in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5146
           | FStar_Pervasives_Native.Some x ->
               let uu____5162 =
                 let uu____5163 =
                   let uu____5168 = embed ea cb x in as_arg uu____5168 in
                 let uu____5169 =
                   let uu____5176 =
                     let uu____5181 = type_of ea in as_iarg uu____5181 in
                   [uu____5176] in
                 uu____5163 :: uu____5169 in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5162) in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1 ->
           match trm1.nbe_t with
           | Construct (fvar, us, args1) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar, us, (a1, uu____5248)::uu____5249::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.some_lid
               ->
               let uu____5276 = unembed ea cb a1 in
               FStar_Util.bind_opt uu____5276
                 (fun a2 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a2))
           | uu____5285 -> FStar_Pervasives_Native.None) in
    let uu____5288 =
      let uu____5289 =
        let uu____5290 = let uu____5295 = type_of ea in as_arg uu____5295 in
        [uu____5290] in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____5289 in
    mk_emb em un uu____5288 etyp
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let etyp =
        let uu____5342 =
          let uu____5350 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu____5350, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____5342 in
      let em cb x =
        lazy_embed etyp x
          (fun uu____5381 ->
             let uu____5382 =
               let uu____5383 =
                 let uu____5388 = embed eb cb (FStar_Pervasives_Native.snd x) in
                 as_arg uu____5388 in
               let uu____5389 =
                 let uu____5396 =
                   let uu____5401 =
                     embed ea cb (FStar_Pervasives_Native.fst x) in
                   as_arg uu____5401 in
                 let uu____5402 =
                   let uu____5409 =
                     let uu____5414 = type_of eb in as_iarg uu____5414 in
                   let uu____5415 =
                     let uu____5422 =
                       let uu____5427 = type_of ea in as_iarg uu____5427 in
                     [uu____5422] in
                   uu____5409 :: uu____5415 in
                 uu____5396 :: uu____5402 in
               uu____5383 :: uu____5389 in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____5382) in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1 ->
             match trm1.nbe_t with
             | Construct
                 (fvar, us,
                  (b1, uu____5495)::(a1, uu____5497)::uu____5498::uu____5499::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5538 = unembed ea cb a1 in
                 FStar_Util.bind_opt uu____5538
                   (fun a2 ->
                      let uu____5548 = unembed eb cb b1 in
                      FStar_Util.bind_opt uu____5548
                        (fun b2 -> FStar_Pervasives_Native.Some (a2, b2)))
             | uu____5561 -> FStar_Pervasives_Native.None) in
      let uu____5566 =
        let uu____5567 =
          let uu____5568 = let uu____5573 = type_of eb in as_arg uu____5573 in
          let uu____5574 =
            let uu____5581 = let uu____5586 = type_of ea in as_arg uu____5586 in
            [uu____5581] in
          uu____5568 :: uu____5574 in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5567 in
      mk_emb em un uu____5566 etyp
let e_either :
  'a 'b .
    'a embedding -> 'b embedding -> ('a, 'b) FStar_Util.either embedding
  =
  fun ea ->
    fun eb ->
      let etyp =
        let uu____5639 =
          let uu____5647 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu____5647, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu____5639 in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5679 ->
             match s with
             | FStar_Util.Inl a1 ->
                 let uu____5681 =
                   let uu____5682 =
                     let uu____5687 = embed ea cb a1 in as_arg uu____5687 in
                   let uu____5688 =
                     let uu____5695 =
                       let uu____5700 = type_of eb in as_iarg uu____5700 in
                     let uu____5701 =
                       let uu____5708 =
                         let uu____5713 = type_of ea in as_iarg uu____5713 in
                       [uu____5708] in
                     uu____5695 :: uu____5701 in
                   uu____5682 :: uu____5688 in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5681
             | FStar_Util.Inr b1 ->
                 let uu____5731 =
                   let uu____5732 =
                     let uu____5737 = embed eb cb b1 in as_arg uu____5737 in
                   let uu____5738 =
                     let uu____5745 =
                       let uu____5750 = type_of eb in as_iarg uu____5750 in
                     let uu____5751 =
                       let uu____5758 =
                         let uu____5763 = type_of ea in as_iarg uu____5763 in
                       [uu____5758] in
                     uu____5745 :: uu____5751 in
                   uu____5732 :: uu____5738 in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5731) in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1 ->
             match trm1.nbe_t with
             | Construct
                 (fvar, us, (a1, uu____5825)::uu____5826::uu____5827::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5862 = unembed ea cb a1 in
                 FStar_Util.bind_opt uu____5862
                   (fun a2 ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
             | Construct
                 (fvar, us, (b1, uu____5878)::uu____5879::uu____5880::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5915 = unembed eb cb b1 in
                 FStar_Util.bind_opt uu____5915
                   (fun b2 ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
             | uu____5928 -> FStar_Pervasives_Native.None) in
      let uu____5933 =
        let uu____5934 =
          let uu____5935 = let uu____5940 = type_of eb in as_arg uu____5940 in
          let uu____5941 =
            let uu____5948 = let uu____5953 = type_of ea in as_arg uu____5953 in
            [uu____5948] in
          uu____5935 :: uu____5941 in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5934 in
      mk_emb em un uu____5933 etyp
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r) in
  let un cb t1 =
    match t1 with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____6002 -> FStar_Pervasives_Native.None in
  let uu____6003 = lid_as_typ FStar_Parser_Const.range_lid [] [] in
  let uu____6008 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range in
  mk_emb' em un uu____6003 uu____6008
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let etyp =
      let uu____6029 =
        let uu____6037 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu____6037, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu____6029 in
    let em cb l =
      lazy_embed etyp l
        (fun uu____6064 ->
           let typ = let uu____6066 = type_of ea in as_iarg uu____6066 in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ] in
           let cons hd tl =
             let uu____6087 =
               let uu____6088 = as_arg tl in
               let uu____6093 =
                 let uu____6100 =
                   let uu____6105 = embed ea cb hd in as_arg uu____6105 in
                 [uu____6100; typ] in
               uu____6088 :: uu____6093 in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____6087 in
           FStar_List.fold_right cons l nil) in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1 ->
           match trm1.nbe_t with
           | Construct (fv, uu____6153, uu____6154) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv, uu____6174,
                (tl, FStar_Pervasives_Native.None)::(hd,
                                                     FStar_Pervasives_Native.None)::
                (uu____6177, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6178))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6206 = unembed ea cb hd in
               FStar_Util.bind_opt uu____6206
                 (fun hd1 ->
                    let uu____6214 = un cb tl in
                    FStar_Util.bind_opt uu____6214
                      (fun tl1 -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | Construct
               (fv, uu____6230,
                (tl, FStar_Pervasives_Native.None)::(hd,
                                                     FStar_Pervasives_Native.None)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6255 = unembed ea cb hd in
               FStar_Util.bind_opt uu____6255
                 (fun hd1 ->
                    let uu____6263 = un cb tl in
                    FStar_Util.bind_opt uu____6263
                      (fun tl1 -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | uu____6278 -> FStar_Pervasives_Native.None) in
    let uu____6281 =
      let uu____6282 =
        let uu____6283 = let uu____6288 = type_of ea in as_arg uu____6288 in
        [uu____6283] in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____6282 in
    mk_emb em un uu____6281 etyp
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea ->
    fun eb ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let em cb f =
        lazy_embed etyp f
          (fun uu____6362 ->
             let uu____6363 =
               let uu____6364 =
                 let uu____6397 =
                   let uu____6418 =
                     let uu____6425 =
                       let uu____6430 = type_of eb in as_arg uu____6430 in
                     [uu____6425] in
                   FStar_Util.Inr uu____6418 in
                 ((fun tas ->
                     let uu____6488 =
                       let uu____6491 = FStar_List.hd tas in
                       unembed ea cb uu____6491 in
                     match uu____6488 with
                     | FStar_Pervasives_Native.Some a1 ->
                         let uu____6493 = f a1 in embed eb cb uu____6493
                     | FStar_Pervasives_Native.None ->
                         failwith "cannot unembed function argument"),
                   uu____6397, Prims.int_one) in
               Lam uu____6364 in
             FStar_All.pipe_left mk_t uu____6363) in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x ->
               let uu____6540 =
                 let uu____6543 =
                   let uu____6544 =
                     let uu____6545 =
                       let uu____6550 = embed ea cb x in as_arg uu____6550 in
                     [uu____6545] in
                   cb.iapp lam1 uu____6544 in
                 unembed eb cb uu____6543 in
               match uu____6540 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None ->
                   failwith "cannot unembed function result") in
        lazy_unembed cb etyp lam k in
      let uu____6564 =
        let uu____6565 = type_of ea in
        let uu____6566 = let uu____6567 = type_of eb in as_iarg uu____6567 in
        make_arrow1 uu____6565 uu____6566 in
      mk_emb em un uu____6564 etyp
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n =
    match n with
    | FStar_Syntax_Embeddings.Simpl ->
        let uu____6585 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____6585 [] []
    | FStar_Syntax_Embeddings.Weak ->
        let uu____6590 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____6590 [] []
    | FStar_Syntax_Embeddings.HNF ->
        let uu____6595 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____6595 [] []
    | FStar_Syntax_Embeddings.Primops ->
        let uu____6600 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____6600 [] []
    | FStar_Syntax_Embeddings.Delta ->
        let uu____6605 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____6605 [] []
    | FStar_Syntax_Embeddings.Zeta ->
        let uu____6610 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____6610 [] []
    | FStar_Syntax_Embeddings.Iota ->
        let uu____6615 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____6615 [] []
    | FStar_Syntax_Embeddings.Reify ->
        let uu____6620 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____6620 [] []
    | FStar_Syntax_Embeddings.NBE ->
        let uu____6625 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu____6625 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6634 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____6635 =
          let uu____6636 =
            let uu____6641 =
              let uu____6642 = e_list e_string in embed uu____6642 cb l in
            as_arg uu____6641 in
          [uu____6636] in
        mkFV uu____6634 [] uu____6635
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6664 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____6665 =
          let uu____6666 =
            let uu____6671 =
              let uu____6672 = e_list e_string in embed uu____6672 cb l in
            as_arg uu____6671 in
          [uu____6666] in
        mkFV uu____6664 [] uu____6665
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6694 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____6695 =
          let uu____6696 =
            let uu____6701 =
              let uu____6702 = e_list e_string in embed uu____6702 cb l in
            as_arg uu____6701 in
          [uu____6696] in
        mkFV uu____6694 [] uu____6695 in
  let un cb t0 =
    match t0.nbe_t with
    | FV (fv, uu____6736, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv, uu____6752, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv, uu____6768, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv, uu____6784, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv, uu____6800, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv, uu____6816, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv, uu____6832, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv, uu____6848, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv, uu____6864, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv, uu____6880, (l, uu____6882)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6901 =
          let uu____6907 = e_list e_string in unembed uu____6907 cb l in
        FStar_Util.bind_opt uu____6901
          (fun ss ->
             FStar_All.pipe_left
               (fun uu____6927 -> FStar_Pervasives_Native.Some uu____6927)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv, uu____6929, (l, uu____6931)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6950 =
          let uu____6956 = e_list e_string in unembed uu____6956 cb l in
        FStar_Util.bind_opt uu____6950
          (fun ss ->
             FStar_All.pipe_left
               (fun uu____6976 -> FStar_Pervasives_Native.Some uu____6976)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv, uu____6978, (l, uu____6980)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6999 =
          let uu____7005 = e_list e_string in unembed uu____7005 cb l in
        FStar_Util.bind_opt uu____6999
          (fun ss ->
             FStar_All.pipe_left
               (fun uu____7025 -> FStar_Pervasives_Native.Some uu____7025)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____7026 ->
        ((let uu____7028 =
            let uu____7034 =
              let uu____7036 = t_to_string t0 in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____7036 in
            (FStar_Errors.Warning_NotEmbedded, uu____7034) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____7028);
         FStar_Pervasives_Native.None) in
  let uu____7040 =
    let uu____7041 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    mkFV uu____7041 [] [] in
  let uu____7046 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step in
  mk_emb em un uu____7040 uu____7046
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h -> fun _args -> h);
    translate = (fun uu____7055 -> failwith "bogus_cbs translate")
  }
let (arg_as_int : arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_int bogus_cbs)
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_bool bogus_cbs)
let (arg_as_char : arg -> FStar_Char.char FStar_Pervasives_Native.option) =
  fun a ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_char bogus_cbs)
let (arg_as_string : arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_string bogus_cbs)
let arg_as_list :
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e ->
    fun a1 ->
      let uu____7132 =
        let uu____7141 = e_list e in unembed uu____7141 bogus_cbs in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu____7132
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____7163 ->
    match uu____7163 with
    | (a, uu____7171) ->
        (match a.nbe_t with
         | FV
             (fv1, [],
              ({ nbe_t = Constant (Int i); nbe_r = uu____7186;_}, uu____7187)::[])
             when
             let uu____7204 =
               FStar_Ident.string_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             FStar_Util.ends_with uu____7204 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____7211 -> FStar_Pervasives_Native.None)
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t ->
    fun n ->
      let c = embed e_int bogus_cbs n in
      let int_to_t1 args1 =
        FStar_All.pipe_left mk_t (FV (int_to_t, [], args1)) in
      let uu____7254 = let uu____7261 = as_arg c in [uu____7261] in
      int_to_t1 uu____7254
let lift_unary :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun aopts ->
      match aopts with
      | (FStar_Pervasives_Native.Some a1)::[] ->
          let uu____7315 = f a1 in FStar_Pervasives_Native.Some uu____7315
      | uu____7316 -> FStar_Pervasives_Native.None
let lift_binary :
  'a 'b .
    ('a -> 'a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun aopts ->
      match aopts with
      | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
          a1)::[] ->
          let uu____7370 = f a0 a1 in FStar_Pervasives_Native.Some uu____7370
      | uu____7371 -> FStar_Pervasives_Native.None
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun f ->
      fun args1 ->
        let uu____7415 = FStar_List.map as_a args1 in lift_unary f uu____7415
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun f ->
      fun args1 ->
        let uu____7470 = FStar_List.map as_a args1 in
        lift_binary f uu____7470
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    unary_op arg_as_int
      (fun x -> let uu____7500 = f x in embed e_int bogus_cbs uu____7500)
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_int
      (fun x ->
         fun y -> let uu____7527 = f x y in embed e_int bogus_cbs uu____7527)
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f ->
    unary_op arg_as_bool
      (fun x -> let uu____7553 = f x in embed e_bool bogus_cbs uu____7553)
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_bool
      (fun x ->
         fun y -> let uu____7591 = f x y in embed e_bool bogus_cbs uu____7591)
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_string
      (fun x ->
         fun y ->
           let uu____7629 = f x y in embed e_string bogus_cbs uu____7629)
let mixed_binary_op :
  'a 'b 'c .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      (arg -> 'b FStar_Pervasives_Native.option) ->
        ('c -> t) ->
          ('a -> 'b -> 'c) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun as_b ->
      fun embed_c ->
        fun f ->
          fun args1 ->
            match args1 with
            | a1::b1::[] ->
                let uu____7734 =
                  let uu____7743 = as_a a1 in
                  let uu____7746 = as_b b1 in (uu____7743, uu____7746) in
                (match uu____7734 with
                 | (FStar_Pervasives_Native.Some a2,
                    FStar_Pervasives_Native.Some b2) ->
                     let uu____7761 =
                       let uu____7762 = f a2 b2 in embed_c uu____7762 in
                     FStar_Pervasives_Native.Some uu____7761
                 | uu____7763 -> FStar_Pervasives_Native.None)
            | uu____7772 -> FStar_Pervasives_Native.None
let (list_of_string' : Prims.string -> t) =
  fun s ->
    let uu____7781 = e_list e_char in
    let uu____7788 = FStar_String.list_of_string s in
    embed uu____7781 bogus_cbs uu____7788
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l ->
    let s = FStar_String.string_of_list l in
    FStar_All.pipe_left mk_t (Constant (String (s, FStar_Range.dummyRange)))
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1 ->
    fun s2 ->
      let r = FStar_String.compare s1 s2 in
      let uu____7827 =
        let uu____7828 = FStar_Util.string_of_int r in
        FStar_BigInt.big_int_of_string uu____7828 in
      embed e_int bogus_cbs uu____7827
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu____7862 = arg_as_string a1 in
        (match uu____7862 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7871 = arg_as_list e_string a2 in
             (match uu____7871 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____7889 = embed e_string bogus_cbs r in
                  FStar_Pervasives_Native.Some uu____7889
              | uu____7891 -> FStar_Pervasives_Native.None)
         | uu____7897 -> FStar_Pervasives_Native.None)
    | uu____7901 -> FStar_Pervasives_Native.None
let (string_of_int : FStar_BigInt.t -> t) =
  fun i ->
    let uu____7908 = FStar_BigInt.string_of_big_int i in
    embed e_string bogus_cbs uu____7908
let (string_of_bool : Prims.bool -> t) =
  fun b -> embed e_string bogus_cbs (if b then "true" else "false")
let (string_lowercase : Prims.string -> t) =
  fun s -> embed e_string bogus_cbs (FStar_String.lowercase s)
let (string_uppercase : Prims.string -> t) =
  fun s -> embed e_string bogus_cbs (FStar_String.lowercase s)
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg ->
    fun args1 ->
      let tru = embed e_bool bogus_cbs true in
      let fal = embed e_bool bogus_cbs false in
      match args1 with
      | (_typ, uu____7970)::(a1, uu____7972)::(a2, uu____7974)::[] ->
          let uu____7991 = eq_t a1 a2 in
          (match uu____7991 with
           | FStar_Syntax_Util.Equal ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____8000 -> FStar_Pervasives_Native.None)
      | uu____8001 -> failwith "Unexpected number of arguments"
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | (_u, uu____8016)::(_typ, uu____8018)::(a1, uu____8020)::(a2,
                                                               uu____8022)::[]
        ->
        let uu____8043 = eq_t a1 a2 in
        (match uu____8043 with
         | FStar_Syntax_Util.Equal ->
             let uu____8046 = embed e_bool bogus_cbs true in
             FStar_Pervasives_Native.Some uu____8046
         | FStar_Syntax_Util.NotEqual ->
             let uu____8049 = embed e_bool bogus_cbs false in
             FStar_Pervasives_Native.Some uu____8049
         | FStar_Syntax_Util.Unknown -> FStar_Pervasives_Native.None)
    | uu____8052 -> failwith "Unexpected number of arguments"
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | (_u, uu____8067)::(_v, uu____8069)::(t1, uu____8071)::(t2, uu____8073)::
        (a1, uu____8075)::(a2, uu____8077)::[] ->
        let uu____8106 =
          let uu____8107 = eq_t t1 t2 in
          let uu____8108 = eq_t a1 a2 in
          FStar_Syntax_Util.eq_inj uu____8107 uu____8108 in
        (match uu____8106 with
         | FStar_Syntax_Util.Equal ->
             let uu____8111 = embed e_bool bogus_cbs true in
             FStar_Pervasives_Native.Some uu____8111
         | FStar_Syntax_Util.NotEqual ->
             let uu____8114 = embed e_bool bogus_cbs false in
             FStar_Pervasives_Native.Some uu____8114
         | FStar_Syntax_Util.Unknown -> FStar_Pervasives_Native.None)
    | uu____8117 -> failwith "Unexpected number of arguments"
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid ->
    fun args1 ->
      let uu____8136 =
        let uu____8138 = FStar_Ident.string_of_lid lid in
        FStar_String.op_Hat "No interpretation for " uu____8138 in
      failwith uu____8136
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | (a1, uu____8154)::[] ->
        let uu____8163 = unembed e_range bogus_cbs a1 in
        (match uu____8163 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8169 = embed e_range bogus_cbs r in
             FStar_Pervasives_Native.Some uu____8169
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | uu____8170 -> failwith "Unexpected number of arguments"
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu____8206 = arg_as_list e_char a1 in
        (match uu____8206 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8222 = arg_as_string a2 in
             (match uu____8222 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2 in
                  let uu____8235 =
                    let uu____8236 = e_list e_string in
                    embed uu____8236 bogus_cbs r in
                  FStar_Pervasives_Native.Some uu____8235
              | uu____8246 -> FStar_Pervasives_Native.None)
         | uu____8250 -> FStar_Pervasives_Native.None)
    | uu____8256 -> FStar_Pervasives_Native.None
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu____8289 =
          let uu____8299 = arg_as_string a1 in
          let uu____8303 = arg_as_int a2 in (uu____8299, uu____8303) in
        (match uu____8289 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some i)
             ->
             (try
                (fun uu___1042_8327 ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i in
                       let uu____8332 = embed e_char bogus_cbs r in
                       FStar_Pervasives_Native.Some uu____8332) ()
              with | uu___1041_8335 -> FStar_Pervasives_Native.None)
         | uu____8338 -> FStar_Pervasives_Native.None)
    | uu____8348 -> FStar_Pervasives_Native.None
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu____8381 =
          let uu____8392 = arg_as_string a1 in
          let uu____8396 = arg_as_char a2 in (uu____8392, uu____8396) in
        (match uu____8381 with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some c)
             ->
             (try
                (fun uu___1060_8425 ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c in
                       let uu____8429 = embed e_int bogus_cbs r in
                       FStar_Pervasives_Native.Some uu____8429) ()
              with | uu___1059_8431 -> FStar_Pervasives_Native.None)
         | uu____8434 -> FStar_Pervasives_Native.None)
    | uu____8445 -> FStar_Pervasives_Native.None
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::a3::[] ->
        let uu____8487 =
          let uu____8501 = arg_as_string a1 in
          let uu____8505 = arg_as_int a2 in
          let uu____8508 = arg_as_int a3 in
          (uu____8501, uu____8505, uu____8508) in
        (match uu____8487 with
         | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some n1,
            FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1 in
             let n21 = FStar_BigInt.to_int_fs n2 in
             (try
                (fun uu___1083_8541 ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21 in
                       let uu____8546 = embed e_string bogus_cbs r in
                       FStar_Pervasives_Native.Some uu____8546) ()
              with | uu___1082_8549 -> FStar_Pervasives_Native.None)
         | uu____8552 -> FStar_Pervasives_Native.None)
    | uu____8566 -> FStar_Pervasives_Native.None
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8626 =
          let uu____8648 = arg_as_string fn in
          let uu____8652 = arg_as_int from_line in
          let uu____8655 = arg_as_int from_col in
          let uu____8658 = arg_as_int to_line in
          let uu____8661 = arg_as_int to_col in
          (uu____8648, uu____8652, uu____8655, uu____8658, uu____8661) in
        (match uu____8626 with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu____8696 =
                 let uu____8697 = FStar_BigInt.to_int_fs from_l in
                 let uu____8699 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____8697 uu____8699 in
               let uu____8701 =
                 let uu____8702 = FStar_BigInt.to_int_fs to_l in
                 let uu____8704 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____8702 uu____8704 in
               FStar_Range.mk_range fn1 uu____8696 uu____8701 in
             let uu____8706 = embed e_range bogus_cbs r in
             FStar_Pervasives_Native.Some uu____8706
         | uu____8707 -> FStar_Pervasives_Native.None)
    | uu____8729 -> FStar_Pervasives_Native.None
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          Prims.int ->
            FStar_Ident.lid ->
              nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun f ->
        fun n_tvars ->
          fun _fv_lid ->
            fun cb ->
              let f_wrapped args1 =
                let uu____8819 = FStar_List.splitAt n_tvars args1 in
                match uu____8819 with
                | (_tvar_args, rest_args) ->
                    let uu____8868 = FStar_List.hd rest_args in
                    (match uu____8868 with
                     | (x, uu____8880) ->
                         let uu____8881 = unembed ea cb x in
                         FStar_Util.map_opt uu____8881
                           (fun x1 ->
                              let uu____8887 = f x1 in embed eb cb uu____8887)) in
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
  fun ea ->
    fun eb ->
      fun ec ->
        fun f ->
          fun n_tvars ->
            fun _fv_lid ->
              fun cb ->
                let f_wrapped args1 =
                  let uu____8996 = FStar_List.splitAt n_tvars args1 in
                  match uu____8996 with
                  | (_tvar_args, rest_args) ->
                      let uu____9045 = FStar_List.hd rest_args in
                      (match uu____9045 with
                       | (x, uu____9057) ->
                           let uu____9058 =
                             let uu____9063 = FStar_List.tl rest_args in
                             FStar_List.hd uu____9063 in
                           (match uu____9058 with
                            | (y, uu____9081) ->
                                let uu____9082 = unembed ea cb x in
                                FStar_Util.bind_opt uu____9082
                                  (fun x1 ->
                                     let uu____9088 = unembed eb cb y in
                                     FStar_Util.bind_opt uu____9088
                                       (fun y1 ->
                                          let uu____9094 =
                                            let uu____9095 = f x1 y1 in
                                            embed ec cb uu____9095 in
                                          FStar_Pervasives_Native.Some
                                            uu____9094)))) in
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
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun f ->
            fun n_tvars ->
              fun _fv_lid ->
                fun cb ->
                  let f_wrapped args1 =
                    let uu____9223 = FStar_List.splitAt n_tvars args1 in
                    match uu____9223 with
                    | (_tvar_args, rest_args) ->
                        let uu____9272 = FStar_List.hd rest_args in
                        (match uu____9272 with
                         | (x, uu____9284) ->
                             let uu____9285 =
                               let uu____9290 = FStar_List.tl rest_args in
                               FStar_List.hd uu____9290 in
                             (match uu____9285 with
                              | (y, uu____9308) ->
                                  let uu____9309 =
                                    let uu____9314 =
                                      let uu____9321 =
                                        FStar_List.tl rest_args in
                                      FStar_List.tl uu____9321 in
                                    FStar_List.hd uu____9314 in
                                  (match uu____9309 with
                                   | (z, uu____9343) ->
                                       let uu____9344 = unembed ea cb x in
                                       FStar_Util.bind_opt uu____9344
                                         (fun x1 ->
                                            let uu____9350 = unembed eb cb y in
                                            FStar_Util.bind_opt uu____9350
                                              (fun y1 ->
                                                 let uu____9356 =
                                                   unembed ec cb z in
                                                 FStar_Util.bind_opt
                                                   uu____9356
                                                   (fun z1 ->
                                                      let uu____9362 =
                                                        let uu____9363 =
                                                          f x1 y1 z1 in
                                                        embed ed cb
                                                          uu____9363 in
                                                      FStar_Pervasives_Native.Some
                                                        uu____9362)))))) in
                  f_wrapped