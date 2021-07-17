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
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> true | uu___ -> false
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> _0
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee -> match projectee with | Int _0 -> true | uu___ -> false
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee -> match projectee with | Int _0 -> _0
let (uu___is_String : constant -> Prims.bool) =
  fun projectee -> match projectee with | String _0 -> true | uu___ -> false
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee -> match projectee with | Char _0 -> true | uu___ -> false
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee -> match projectee with | Char _0 -> _0
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee -> match projectee with | Range _0 -> true | uu___ -> false
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee -> match projectee with | Range _0 -> _0
let (uu___is_SConst : constant -> Prims.bool) =
  fun projectee -> match projectee with | SConst _0 -> true | uu___ -> false
let (__proj__SConst__item___0 : constant -> FStar_Const.sconst) =
  fun projectee -> match projectee with | SConst _0 -> _0
type atom =
  | Var of var 
  | Match of (t *
  (unit -> FStar_Syntax_Syntax.ascription FStar_Pervasives_Native.option) *
  (unit -> FStar_Syntax_Syntax.branch Prims.list)) 
  | UnreducedLet of (var * t FStar_Thunk.t * t FStar_Thunk.t * t
  FStar_Thunk.t * FStar_Syntax_Syntax.letbinding) 
  | UnreducedLetRec of ((var * t * t) Prims.list * t *
  FStar_Syntax_Syntax.letbinding Prims.list) 
  | UVar of FStar_Syntax_Syntax.term FStar_Thunk.t 
and t' =
  | Lam of ((t Prims.list -> t) *
  ((t Prims.list * FStar_Syntax_Syntax.binders *
     FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
  (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Pervasives.either *
  Prims.int) 
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
  ((t * FStar_Syntax_Syntax.aqual) Prims.list * comp))
  FStar_Pervasives.either 
  | Refinement of ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual))) 
  | Reflect of t 
  | Quote of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo) 
  | Lazy of ((FStar_Syntax_Syntax.lazyinfo,
  (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Pervasives.either * t
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
  | DECREASES_lex of t Prims.list 
  | DECREASES_wf of (t * t) 
and residual_comp =
  {
  residual_effect: FStar_Ident.lident ;
  residual_typ: t FStar_Pervasives_Native.option ;
  residual_flags: cflag Prims.list }
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let (__proj__Var__item___0 : atom -> var) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee -> match projectee with | Match _0 -> true | uu___ -> false
let (__proj__Match__item___0 :
  atom ->
    (t *
      (unit -> FStar_Syntax_Syntax.ascription FStar_Pervasives_Native.option)
      * (unit -> FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UnreducedLet _0 -> true | uu___ -> false
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStar_Thunk.t * t FStar_Thunk.t * t FStar_Thunk.t *
      FStar_Syntax_Syntax.letbinding))
  = fun projectee -> match projectee with | UnreducedLet _0 -> _0
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UnreducedLetRec _0 -> true | uu___ -> false
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee -> match projectee with | UnreducedLetRec _0 -> _0
let (uu___is_UVar : atom -> Prims.bool) =
  fun projectee -> match projectee with | UVar _0 -> true | uu___ -> false
let (__proj__UVar__item___0 : atom -> FStar_Syntax_Syntax.term FStar_Thunk.t)
  = fun projectee -> match projectee with | UVar _0 -> _0
let (uu___is_Lam : t' -> Prims.bool) =
  fun projectee -> match projectee with | Lam _0 -> true | uu___ -> false
let (__proj__Lam__item___0 :
  t' ->
    ((t Prims.list -> t) *
      ((t Prims.list * FStar_Syntax_Syntax.binders *
         FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
      (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Pervasives.either *
      Prims.int))
  = fun projectee -> match projectee with | Lam _0 -> _0
let (uu___is_Accu : t' -> Prims.bool) =
  fun projectee -> match projectee with | Accu _0 -> true | uu___ -> false
let (__proj__Accu__item___0 :
  t' -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee -> match projectee with | Accu _0 -> _0
let (uu___is_Construct : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Construct _0 -> true | uu___ -> false
let (__proj__Construct__item___0 :
  t' ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | Construct _0 -> _0
let (uu___is_FV : t' -> Prims.bool) =
  fun projectee -> match projectee with | FV _0 -> true | uu___ -> false
let (__proj__FV__item___0 :
  t' ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | FV _0 -> _0
let (uu___is_Constant : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Constant _0 -> true | uu___ -> false
let (__proj__Constant__item___0 : t' -> constant) =
  fun projectee -> match projectee with | Constant _0 -> _0
let (uu___is_Type_t : t' -> Prims.bool) =
  fun projectee -> match projectee with | Type_t _0 -> true | uu___ -> false
let (__proj__Type_t__item___0 : t' -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Type_t _0 -> _0
let (uu___is_Univ : t' -> Prims.bool) =
  fun projectee -> match projectee with | Univ _0 -> true | uu___ -> false
let (__proj__Univ__item___0 : t' -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Unknown : t' -> Prims.bool) =
  fun projectee -> match projectee with | Unknown -> true | uu___ -> false
let (uu___is_Arrow : t' -> Prims.bool) =
  fun projectee -> match projectee with | Arrow _0 -> true | uu___ -> false
let (__proj__Arrow__item___0 :
  t' ->
    (FStar_Syntax_Syntax.term FStar_Thunk.t,
      ((t * FStar_Syntax_Syntax.aqual) Prims.list * comp))
      FStar_Pervasives.either)
  = fun projectee -> match projectee with | Arrow _0 -> _0
let (uu___is_Refinement : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Refinement _0 -> true | uu___ -> false
let (__proj__Refinement__item___0 :
  t' -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee -> match projectee with | Refinement _0 -> _0
let (uu___is_Reflect : t' -> Prims.bool) =
  fun projectee -> match projectee with | Reflect _0 -> true | uu___ -> false
let (__proj__Reflect__item___0 : t' -> t) =
  fun projectee -> match projectee with | Reflect _0 -> _0
let (uu___is_Quote : t' -> Prims.bool) =
  fun projectee -> match projectee with | Quote _0 -> true | uu___ -> false
let (__proj__Quote__item___0 :
  t' -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee -> match projectee with | Quote _0 -> _0
let (uu___is_Lazy : t' -> Prims.bool) =
  fun projectee -> match projectee with | Lazy _0 -> true | uu___ -> false
let (__proj__Lazy__item___0 :
  t' ->
    ((FStar_Syntax_Syntax.lazyinfo,
      (FStar_Dyn.dyn * FStar_Syntax_Syntax.emb_typ)) FStar_Pervasives.either
      * t FStar_Thunk.t))
  = fun projectee -> match projectee with | Lazy _0 -> _0
let (uu___is_Meta : t' -> Prims.bool) =
  fun projectee -> match projectee with | Meta _0 -> true | uu___ -> false
let (__proj__Meta__item___0 :
  t' -> (t * FStar_Syntax_Syntax.metadata FStar_Thunk.t)) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_TopLevelLet : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelLet _0 -> true | uu___ -> false
let (__proj__TopLevelLet__item___0 :
  t' ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | TopLevelLet _0 -> _0
let (uu___is_TopLevelRec : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelRec _0 -> true | uu___ -> false
let (__proj__TopLevelRec__item___0 :
  t' ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | TopLevelRec _0 -> _0
let (uu___is_LocalLetRec : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | LocalLetRec _0 -> true | uu___ -> false
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
  fun projectee -> match projectee with | Tot _0 -> true | uu___ -> false
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Tot _0 -> _0
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee -> match projectee with | GTot _0 -> true | uu___ -> false
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | GTot _0 -> _0
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee -> match projectee with | Comp _0 -> true | uu___ -> false
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
  fun projectee -> match projectee with | TOTAL -> true | uu___ -> false
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee -> match projectee with | MLEFFECT -> true | uu___ -> false
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee -> match projectee with | RETURN -> true | uu___ -> false
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | PARTIAL_RETURN -> true | uu___ -> false
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SOMETRIVIAL -> true | uu___ -> false
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | TRIVIAL_POSTCONDITION -> true | uu___ -> false
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SHOULD_NOT_INLINE -> true | uu___ -> false
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee -> match projectee with | LEMMA -> true | uu___ -> false
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee -> match projectee with | CPS -> true | uu___ -> false
let (uu___is_DECREASES_lex : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | DECREASES_lex _0 -> true | uu___ -> false
let (__proj__DECREASES_lex__item___0 : cflag -> t Prims.list) =
  fun projectee -> match projectee with | DECREASES_lex _0 -> _0
let (uu___is_DECREASES_wf : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | DECREASES_wf _0 -> true | uu___ -> false
let (__proj__DECREASES_wf__item___0 : cflag -> (t * t)) =
  fun projectee -> match projectee with | DECREASES_wf _0 -> _0
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
  fun trm -> match trm.nbe_t with | Accu uu___ -> true | uu___ -> false
let (isNotAccu : t -> Prims.bool) =
  fun x -> match x.nbe_t with | Accu (uu___, uu___1) -> false | uu___ -> true
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
        let uu___ = FStar_Syntax_Syntax.range_of_fv i in
        mk_rt uu___ (FV (i, us, ts))
let (mkAccuVar : var -> t) =
  fun v ->
    let uu___ = FStar_Syntax_Syntax.range_of_bv v in
    mk_rt uu___ (Accu ((Var v), []))
let (mkAccuMatch :
  t ->
    (unit -> FStar_Syntax_Syntax.ascription FStar_Pervasives_Native.option)
      -> (unit -> FStar_Syntax_Syntax.branch Prims.list) -> t)
  =
  fun s ->
    fun ret ->
      fun bs -> FStar_All.pipe_left mk_t (Accu ((Match (s, ret, bs)), []))
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___ ->
    if uu___ then FStar_Syntax_Util.Equal else FStar_Syntax_Util.Unknown
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___ ->
    if uu___ then FStar_Syntax_Util.Equal else FStar_Syntax_Util.NotEqual
let (eq_inj :
  FStar_Syntax_Util.eq_result ->
    FStar_Syntax_Util.eq_result -> FStar_Syntax_Util.eq_result)
  =
  fun r1 ->
    fun r2 ->
      match (r1, r2) with
      | (FStar_Syntax_Util.Equal, FStar_Syntax_Util.Equal) ->
          FStar_Syntax_Util.Equal
      | (FStar_Syntax_Util.NotEqual, uu___) -> FStar_Syntax_Util.NotEqual
      | (uu___, FStar_Syntax_Util.NotEqual) -> FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown, uu___) -> FStar_Syntax_Util.Unknown
      | (uu___, FStar_Syntax_Util.Unknown) -> FStar_Syntax_Util.Unknown
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f ->
    fun g ->
      match f with
      | FStar_Syntax_Util.Equal -> g ()
      | uu___ -> FStar_Syntax_Util.Unknown
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (Unit, Unit) -> FStar_Syntax_Util.Equal
      | (Bool b1, Bool b2) -> equal_iff (b1 = b2)
      | (Int i1, Int i2) -> equal_iff (i1 = i2)
      | (String (s1, uu___), String (s2, uu___1)) -> equal_iff (s1 = s2)
      | (Char c11, Char c21) -> equal_iff (c11 = c21)
      | (Range r1, Range r2) -> FStar_Syntax_Util.Unknown
      | (uu___, uu___1) -> FStar_Syntax_Util.NotEqual
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1 ->
    fun t2 ->
      match ((t1.nbe_t), (t2.nbe_t)) with
      | (Lam uu___, Lam uu___1) -> FStar_Syntax_Util.Unknown
      | (Accu (a1, as1), Accu (a2, as2)) ->
          let uu___ = eq_atom a1 a2 in
          eq_and uu___ (fun uu___1 -> eq_args as1 as2)
      | (Construct (v1, us1, args1), Construct (v2, us2, args2)) ->
          let uu___ = FStar_Syntax_Syntax.fv_eq v1 v2 in
          if uu___
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu___2 = FStar_List.zip args1 args2 in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc ->
                      fun uu___3 ->
                        match uu___3 with
                        | ((a1, uu___4), (a2, uu___5)) ->
                            let uu___6 = eq_t a1 a2 in eq_inj acc uu___6)
                   FStar_Syntax_Util.Equal) uu___2))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1, us1, args1), FV (v2, us2, args2)) ->
          let uu___ = FStar_Syntax_Syntax.fv_eq v1 v2 in
          if uu___
          then
            let uu___1 =
              let uu___2 = FStar_Syntax_Util.eq_univs_list us1 us2 in
              equal_iff uu___2 in
            eq_and uu___1 (fun uu___2 -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1, Constant c2) -> eq_constant c1 c2
      | (Type_t u1, Type_t u2) ->
          let uu___ = FStar_Syntax_Util.eq_univs u1 u2 in equal_iff uu___
      | (Univ u1, Univ u2) ->
          let uu___ = FStar_Syntax_Util.eq_univs u1 u2 in equal_iff uu___
      | (Refinement (r1, t11), Refinement (r2, t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit in
          let uu___ =
            let uu___1 =
              let uu___2 = t11 () in FStar_Pervasives_Native.fst uu___2 in
            let uu___2 =
              let uu___3 = t21 () in FStar_Pervasives_Native.fst uu___3 in
            eq_t uu___1 uu___2 in
          eq_and uu___
            (fun uu___1 ->
               let uu___2 = let uu___3 = mkAccuVar x in r1 uu___3 in
               let uu___3 = let uu___4 = mkAccuVar x in r2 uu___4 in
               eq_t uu___2 uu___3)
      | (Unknown, Unknown) -> FStar_Syntax_Util.Equal
      | (uu___, uu___1) -> FStar_Syntax_Util.Unknown
and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (Var bv1, Var bv2) ->
          let uu___ = FStar_Syntax_Syntax.bv_eq bv1 bv2 in equal_if uu___
      | (uu___, uu___1) -> FStar_Syntax_Util.Unknown
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
          let uu___ = eq_arg x y in
          eq_and uu___ (fun uu___1 -> eq_args xs ys)
      | (uu___, uu___1) -> FStar_Syntax_Util.Unknown
let (constant_to_string : constant -> Prims.string) =
  fun c ->
    match c with
    | Unit -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s, uu___) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu___ = FStar_Range.string_of_range r in
        FStar_Util.format1 "Range %s" uu___
    | SConst s -> FStar_Syntax_Print.const_to_string s
let rec (t_to_string : t -> Prims.string) =
  fun x ->
    match x.nbe_t with
    | Lam (b, uu___, arity) ->
        let uu___1 = FStar_Util.string_of_int arity in
        FStar_Util.format1 "Lam (_, %s args)" uu___1
    | Accu (a, l) ->
        let uu___ =
          let uu___1 = atom_to_string a in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_List.map
                    (fun x1 -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l in
                FStar_String.concat "; " uu___5 in
              FStar_String.op_Hat uu___4 ")" in
            FStar_String.op_Hat ") (" uu___3 in
          FStar_String.op_Hat uu___1 uu___2 in
        FStar_String.op_Hat "Accu (" uu___
    | Construct (fv, us, l) ->
        let uu___ =
          let uu___1 = FStar_Syntax_Print.fv_to_string fv in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us in
                FStar_String.concat "; " uu___5 in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStar_List.map
                        (fun x1 ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStar_String.concat "; " uu___8 in
                  FStar_String.op_Hat uu___7 "]" in
                FStar_String.op_Hat "] [" uu___6 in
              FStar_String.op_Hat uu___4 uu___5 in
            FStar_String.op_Hat ") [" uu___3 in
          FStar_String.op_Hat uu___1 uu___2 in
        FStar_String.op_Hat "Construct (" uu___
    | FV (fv, us, l) ->
        let uu___ =
          let uu___1 = FStar_Syntax_Print.fv_to_string fv in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us in
                FStar_String.concat "; " uu___5 in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStar_List.map
                        (fun x1 ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStar_String.concat "; " uu___8 in
                  FStar_String.op_Hat uu___7 "]" in
                FStar_String.op_Hat "] [" uu___6 in
              FStar_String.op_Hat uu___4 uu___5 in
            FStar_String.op_Hat ") [" uu___3 in
          FStar_String.op_Hat uu___1 uu___2 in
        FStar_String.op_Hat "FV (" uu___
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu___ = FStar_Syntax_Print.univ_to_string u in
        FStar_String.op_Hat "Universe " uu___
    | Type_t u ->
        let uu___ = FStar_Syntax_Print.univ_to_string u in
        FStar_String.op_Hat "Type_t " uu___
    | Arrow uu___ -> "Arrow"
    | Refinement (f, t1) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit in
        let t2 = let uu___ = t1 () in FStar_Pervasives_Native.fst uu___ in
        let uu___ =
          let uu___1 = FStar_Syntax_Print.bv_to_string x1 in
          let uu___2 =
            let uu___3 =
              let uu___4 = t_to_string t2 in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 = let uu___9 = mkAccuVar x1 in f uu___9 in
                    t_to_string uu___8 in
                  FStar_String.op_Hat uu___7 "}" in
                FStar_String.op_Hat "{" uu___6 in
              FStar_String.op_Hat uu___4 uu___5 in
            FStar_String.op_Hat ":" uu___3 in
          FStar_String.op_Hat uu___1 uu___2 in
        FStar_String.op_Hat "Refinement " uu___
    | Unknown -> "Unknown"
    | Reflect t1 ->
        let uu___ = t_to_string t1 in FStar_String.op_Hat "Reflect " uu___
    | Quote uu___ -> "Quote _"
    | Lazy (FStar_Pervasives.Inl li, uu___) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Util.unfold_lazy li in
          FStar_Syntax_Print.term_to_string uu___2 in
        FStar_Util.format1 "Lazy (Inl {%s})" uu___1
    | Lazy (FStar_Pervasives.Inr (uu___, et), uu___1) ->
        let uu___2 = FStar_Syntax_Print.emb_typ_to_string et in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu___2
    | LocalLetRec (uu___, l, uu___1, uu___2, uu___3, uu___4, uu___5) ->
        let uu___6 =
          let uu___7 = FStar_Syntax_Print.lbs_to_string [] (true, [l]) in
          FStar_String.op_Hat uu___7 ")" in
        FStar_String.op_Hat "LocalLetRec (" uu___6
    | TopLevelLet (lb, uu___, uu___1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            FStar_Syntax_Print.fv_to_string uu___4 in
          FStar_String.op_Hat uu___3 ")" in
        FStar_String.op_Hat "TopLevelLet (" uu___2
    | TopLevelRec (lb, uu___, uu___1, uu___2) ->
        let uu___3 =
          let uu___4 =
            let uu___5 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            FStar_Syntax_Print.fv_to_string uu___5 in
          FStar_String.op_Hat uu___4 ")" in
        FStar_String.op_Hat "TopLevelRec (" uu___3
    | Meta (t1, uu___) ->
        let uu___1 = t_to_string t1 in FStar_String.op_Hat "Meta " uu___1
and (atom_to_string : atom -> Prims.string) =
  fun a ->
    match a with
    | Var v ->
        let uu___ = FStar_Syntax_Print.bv_to_string v in
        FStar_String.op_Hat "Var " uu___
    | Match (t1, uu___, uu___1) ->
        let uu___2 = t_to_string t1 in FStar_String.op_Hat "Match " uu___2
    | UnreducedLet (var1, typ, def, body, lb) ->
        let uu___ =
          let uu___1 = FStar_Syntax_Print.lbs_to_string [] (false, [lb]) in
          FStar_String.op_Hat uu___1 " in ...)" in
        FStar_String.op_Hat "UnreducedLet(" uu___
    | UnreducedLetRec (uu___, body, lbs) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Print.lbs_to_string [] (true, lbs) in
          let uu___3 =
            let uu___4 =
              let uu___5 = t_to_string body in FStar_String.op_Hat uu___5 ")" in
            FStar_String.op_Hat " in " uu___4 in
          FStar_String.op_Hat uu___2 uu___3 in
        FStar_String.op_Hat "UnreducedLetRec(" uu___1
    | UVar uu___ -> "UVar"
let (arg_to_string : arg -> Prims.string) =
  fun a ->
    let uu___ = FStar_All.pipe_right a FStar_Pervasives_Native.fst in
    FStar_All.pipe_right uu___ t_to_string
let (args_to_string : args -> Prims.string) =
  fun args1 ->
    let uu___ = FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu___ (FStar_String.concat " ")
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
  'uuuuu .
    (nbe_cbs -> 'uuuuu -> t') ->
      (nbe_cbs -> t' -> 'uuuuu FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'uuuuu embedding
  =
  fun em ->
    fun un ->
      mk_emb
        (fun cbs ->
           fun t1 -> let uu___ = em cbs t1 in FStar_All.pipe_left mk_t uu___)
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
          mk_emb (fun cbs -> fun x -> let uu___ = ba x in embed ea cbs uu___)
            (fun cbs ->
               fun t1 ->
                 let uu___ = unembed ea cbs t1 in FStar_Util.map_opt uu___ ab)
            (match ot with
             | FStar_Pervasives_Native.Some t1 -> t1
             | FStar_Pervasives_Native.None -> ea.typ) ea.emb_typ
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l ->
    fun us ->
      fun args1 ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
        mkConstruct uu___ us args1
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l ->
    fun us ->
      fun args1 ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None in
        mkFV uu___ us args1
let (as_iarg : t -> arg) =
  fun a -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
let (as_arg : t -> arg) = fun a -> (a, FStar_Pervasives_Native.None)
let (make_arrow1 : t -> arg -> t) =
  fun t1 ->
    fun a ->
      FStar_All.pipe_left mk_t
        (Arrow
           (FStar_Pervasives.Inr
              ([a], (Tot (t1, FStar_Pervasives_Native.None)))))
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et ->
    fun x ->
      fun f ->
        (let uu___1 = FStar_ST.op_Bang FStar_Options.debug_embedding in
         if uu___1
         then
           let uu___2 = FStar_Syntax_Print.emb_typ_to_string et in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu___2
         else ());
        (let uu___1 = FStar_ST.op_Bang FStar_Options.eager_embedding in
         if uu___1
         then f ()
         else
           (let thunk = FStar_Thunk.mk f in
            let li = let uu___3 = FStar_Dyn.mkdyn x in (uu___3, et) in
            FStar_All.pipe_left mk_t
              (Lazy ((FStar_Pervasives.Inr li), thunk))))
let lazy_unembed :
  'uuuuu 'a .
    'uuuuu ->
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
          | Lazy (FStar_Pervasives.Inl li, thunk) ->
              let uu___ = FStar_Thunk.force thunk in f uu___
          | Lazy (FStar_Pervasives.Inr (b, et'), thunk) ->
              let uu___ =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding) in
              if uu___
              then
                let res = let uu___1 = FStar_Thunk.force thunk in f uu___1 in
                ((let uu___2 = FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu___2
                  then
                    let uu___3 = FStar_Syntax_Print.emb_typ_to_string et in
                    let uu___4 = FStar_Syntax_Print.emb_typ_to_string et' in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu___3
                      uu___4
                  else ());
                 res)
              else
                (let a1 = FStar_Dyn.undyn b in
                 (let uu___3 = FStar_ST.op_Bang FStar_Options.debug_embedding in
                  if uu___3
                  then
                    let uu___4 = FStar_Syntax_Print.emb_typ_to_string et in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu___4
                  else ());
                 FStar_Pervasives_Native.Some a1)
          | uu___ ->
              let aopt = f x in
              ((let uu___2 = FStar_ST.op_Bang FStar_Options.debug_embedding in
                if uu___2
                then
                  let uu___3 = FStar_Syntax_Print.emb_typ_to_string et in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu___3
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
  let uu___ = lid_as_typ FStar_Parser_Const.term_lid [] [] in
  mk_emb em un uu___ FStar_Syntax_Syntax.ET_abstract
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit in
  let un _cb t1 = FStar_Pervasives_Native.Some () in
  let uu___ = lid_as_typ FStar_Parser_Const.unit_lid [] [] in
  let uu___1 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
  mk_emb' em un uu___ uu___1
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a) in
  let un _cb t1 =
    match t1 with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu___ -> FStar_Pervasives_Native.None in
  let uu___ = lid_as_typ FStar_Parser_Const.bool_lid [] [] in
  let uu___1 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
  mk_emb' em un uu___ uu___1
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c) in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu___ -> FStar_Pervasives_Native.None in
  let uu___ = lid_as_typ FStar_Parser_Const.char_lid [] [] in
  let uu___1 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char in
  mk_emb' em un uu___ uu___1
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange)) in
  let un _cb s =
    match s with
    | Constant (String (s1, uu___)) -> FStar_Pervasives_Native.Some s1
    | uu___ -> FStar_Pervasives_Native.None in
  let uu___ = lid_as_typ FStar_Parser_Const.string_lid [] [] in
  let uu___1 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string in
  mk_emb' em un uu___ uu___1
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c) in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu___ -> FStar_Pervasives_Native.None in
  let uu___ = lid_as_typ FStar_Parser_Const.int_lid [] [] in
  let uu___1 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int in
  mk_emb' em un uu___ uu___1
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let etyp =
      let uu___ =
        let uu___1 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid in
        (uu___1, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu___ in
    let em cb o =
      lazy_embed etyp o
        (fun uu___ ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu___1 =
                 let uu___2 = let uu___3 = type_of ea in as_iarg uu___3 in
                 [uu___2] in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu___1
           | FStar_Pervasives_Native.Some x ->
               let uu___1 =
                 let uu___2 = let uu___3 = embed ea cb x in as_arg uu___3 in
                 let uu___3 =
                   let uu___4 = let uu___5 = type_of ea in as_iarg uu___5 in
                   [uu___4] in
                 uu___2 :: uu___3 in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu___1) in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1 ->
           match trm1.nbe_t with
           | Construct (fvar, us, args1) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar, us, (a1, uu___)::uu___1::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.some_lid
               ->
               let uu___2 = unembed ea cb a1 in
               FStar_Util.bind_opt uu___2
                 (fun a2 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a2))
           | uu___ -> FStar_Pervasives_Native.None) in
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = type_of ea in as_arg uu___3 in [uu___2] in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu___1 in
    mk_emb em un uu___ etyp
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let etyp =
        let uu___ =
          let uu___1 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid in
          (uu___1, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu___ in
      let em cb x =
        lazy_embed etyp x
          (fun uu___ ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = embed eb cb (FStar_Pervasives_Native.snd x) in
                 as_arg uu___3 in
               let uu___3 =
                 let uu___4 =
                   let uu___5 = embed ea cb (FStar_Pervasives_Native.fst x) in
                   as_arg uu___5 in
                 let uu___5 =
                   let uu___6 = let uu___7 = type_of eb in as_iarg uu___7 in
                   let uu___7 =
                     let uu___8 = let uu___9 = type_of ea in as_iarg uu___9 in
                     [uu___8] in
                   uu___6 :: uu___7 in
                 uu___4 :: uu___5 in
               uu___2 :: uu___3 in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu___1) in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1 ->
             match trm1.nbe_t with
             | Construct
                 (fvar, us, (b1, uu___)::(a1, uu___1)::uu___2::uu___3::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu___4 = unembed ea cb a1 in
                 FStar_Util.bind_opt uu___4
                   (fun a2 ->
                      let uu___5 = unembed eb cb b1 in
                      FStar_Util.bind_opt uu___5
                        (fun b2 -> FStar_Pervasives_Native.Some (a2, b2)))
             | uu___ -> FStar_Pervasives_Native.None) in
      let uu___ =
        let uu___1 =
          let uu___2 = let uu___3 = type_of eb in as_arg uu___3 in
          let uu___3 =
            let uu___4 = let uu___5 = type_of ea in as_arg uu___5 in [uu___4] in
          uu___2 :: uu___3 in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu___1 in
      mk_emb em un uu___ etyp
let e_either :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a, 'b) FStar_Pervasives.either embedding
  =
  fun ea ->
    fun eb ->
      let etyp =
        let uu___ =
          let uu___1 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid in
          (uu___1, [ea.emb_typ; eb.emb_typ]) in
        FStar_Syntax_Syntax.ET_app uu___ in
      let em cb s =
        lazy_embed etyp s
          (fun uu___ ->
             match s with
             | FStar_Pervasives.Inl a1 ->
                 let uu___1 =
                   let uu___2 = let uu___3 = embed ea cb a1 in as_arg uu___3 in
                   let uu___3 =
                     let uu___4 = let uu___5 = type_of eb in as_iarg uu___5 in
                     let uu___5 =
                       let uu___6 = let uu___7 = type_of ea in as_iarg uu___7 in
                       [uu___6] in
                     uu___4 :: uu___5 in
                   uu___2 :: uu___3 in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu___1
             | FStar_Pervasives.Inr b1 ->
                 let uu___1 =
                   let uu___2 = let uu___3 = embed eb cb b1 in as_arg uu___3 in
                   let uu___3 =
                     let uu___4 = let uu___5 = type_of eb in as_iarg uu___5 in
                     let uu___5 =
                       let uu___6 = let uu___7 = type_of ea in as_iarg uu___7 in
                       [uu___6] in
                     uu___4 :: uu___5 in
                   uu___2 :: uu___3 in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu___1) in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1 ->
             match trm1.nbe_t with
             | Construct (fvar, us, (a1, uu___)::uu___1::uu___2::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu___3 = unembed ea cb a1 in
                 FStar_Util.bind_opt uu___3
                   (fun a2 ->
                      FStar_Pervasives_Native.Some (FStar_Pervasives.Inl a2))
             | Construct (fvar, us, (b1, uu___)::uu___1::uu___2::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu___3 = unembed eb cb b1 in
                 FStar_Util.bind_opt uu___3
                   (fun b2 ->
                      FStar_Pervasives_Native.Some (FStar_Pervasives.Inr b2))
             | uu___ -> FStar_Pervasives_Native.None) in
      let uu___ =
        let uu___1 =
          let uu___2 = let uu___3 = type_of eb in as_arg uu___3 in
          let uu___3 =
            let uu___4 = let uu___5 = type_of ea in as_arg uu___5 in [uu___4] in
          uu___2 :: uu___3 in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu___1 in
      mk_emb em un uu___ etyp
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r) in
  let un cb t1 =
    match t1 with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu___ -> FStar_Pervasives_Native.None in
  let uu___ = lid_as_typ FStar_Parser_Const.range_lid [] [] in
  let uu___1 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range in
  mk_emb' em un uu___ uu___1
let (e_vconfig : FStar_VConfig.vconfig embedding) =
  let em cb r = failwith "e_vconfig NBE" in
  let un cb t1 = failwith "e_vconfig NBE" in
  let uu___ = lid_as_typ FStar_Parser_Const.vconfig_lid [] [] in
  let uu___1 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_vconfig in
  mk_emb' em un uu___ uu___1
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let etyp =
      let uu___ =
        let uu___1 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid in
        (uu___1, [ea.emb_typ]) in
      FStar_Syntax_Syntax.ET_app uu___ in
    let em cb l =
      lazy_embed etyp l
        (fun uu___ ->
           let typ = let uu___1 = type_of ea in as_iarg uu___1 in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ] in
           let cons hd tl =
             let uu___1 =
               let uu___2 = as_arg tl in
               let uu___3 =
                 let uu___4 = let uu___5 = embed ea cb hd in as_arg uu___5 in
                 [uu___4; typ] in
               uu___2 :: uu___3 in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu___1 in
           FStar_List.fold_right cons l nil) in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1 ->
           match trm1.nbe_t with
           | Construct (fv, uu___, uu___1) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv, uu___,
                (tl, FStar_Pervasives_Native.None)::(hd,
                                                     FStar_Pervasives_Native.None)::
                (uu___1, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu___2))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu___3 = unembed ea cb hd in
               FStar_Util.bind_opt uu___3
                 (fun hd1 ->
                    let uu___4 = un cb tl in
                    FStar_Util.bind_opt uu___4
                      (fun tl1 -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | Construct
               (fv, uu___,
                (tl, FStar_Pervasives_Native.None)::(hd,
                                                     FStar_Pervasives_Native.None)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu___1 = unembed ea cb hd in
               FStar_Util.bind_opt uu___1
                 (fun hd1 ->
                    let uu___2 = un cb tl in
                    FStar_Util.bind_opt uu___2
                      (fun tl1 -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | uu___ -> FStar_Pervasives_Native.None) in
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = type_of ea in as_arg uu___3 in [uu___2] in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu___1 in
    mk_emb em un uu___ etyp
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea ->
    fun eb ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ)) in
      let em cb f =
        lazy_embed etyp f
          (fun uu___ ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = let uu___6 = type_of eb in as_arg uu___6 in
                     [uu___5] in
                   FStar_Pervasives.Inr uu___4 in
                 ((fun tas ->
                     let uu___4 =
                       let uu___5 = FStar_List.hd tas in unembed ea cb uu___5 in
                     match uu___4 with
                     | FStar_Pervasives_Native.Some a1 ->
                         let uu___5 = f a1 in embed eb cb uu___5
                     | FStar_Pervasives_Native.None ->
                         failwith "cannot unembed function argument"),
                   uu___3, Prims.int_one) in
               Lam uu___2 in
             FStar_All.pipe_left mk_t uu___1) in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x ->
               let uu___ =
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = let uu___4 = embed ea cb x in as_arg uu___4 in
                     [uu___3] in
                   cb.iapp lam1 uu___2 in
                 unembed eb cb uu___1 in
               match uu___ with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None ->
                   failwith "cannot unembed function result") in
        lazy_unembed cb etyp lam k in
      let uu___ =
        let uu___1 = type_of ea in
        let uu___2 = let uu___3 = type_of eb in as_iarg uu___3 in
        make_arrow1 uu___1 uu___2 in
      mk_emb em un uu___ etyp
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n =
    match n with
    | FStar_Syntax_Embeddings.Simpl ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Syntax_Embeddings.Weak ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Syntax_Embeddings.HNF ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Syntax_Embeddings.Primops ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Syntax_Embeddings.Delta ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Syntax_Embeddings.Zeta ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Syntax_Embeddings.Iota ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Syntax_Embeddings.Reify ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Syntax_Embeddings.NBE ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu___1 =
          let uu___2 =
            let uu___3 = let uu___4 = e_list e_string in embed uu___4 cb l in
            as_arg uu___3 in
          [uu___2] in
        mkFV uu___ [] uu___1
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu___1 =
          let uu___2 =
            let uu___3 = let uu___4 = e_list e_string in embed uu___4 cb l in
            as_arg uu___3 in
          [uu___2] in
        mkFV uu___ [] uu___1
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu___1 =
          let uu___2 =
            let uu___3 = let uu___4 = e_list e_string in embed uu___4 cb l in
            as_arg uu___3 in
          [uu___2] in
        mkFV uu___ [] uu___1
    | FStar_Syntax_Embeddings.ZetaFull ->
        let uu___ =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta_full
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        mkFV uu___ [] [] in
  let un cb t0 =
    match t0.nbe_t with
    | FV (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv, uu___, []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv, uu___, (l, uu___1)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu___2 = let uu___3 = e_list e_string in unembed uu___3 cb l in
        FStar_Util.bind_opt uu___2
          (fun ss ->
             FStar_All.pipe_left
               (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv, uu___, (l, uu___1)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu___2 = let uu___3 = e_list e_string in unembed uu___3 cb l in
        FStar_Util.bind_opt uu___2
          (fun ss ->
             FStar_All.pipe_left
               (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv, uu___, (l, uu___1)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu___2 = let uu___3 = e_list e_string in unembed uu___3 cb l in
        FStar_Util.bind_opt uu___2
          (fun ss ->
             FStar_All.pipe_left
               (fun uu___3 -> FStar_Pervasives_Native.Some uu___3)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = t_to_string t0 in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu___4 in
            (FStar_Errors.Warning_NotEmbedded, uu___3) in
          FStar_Errors.log_issue FStar_Range.dummyRange uu___2);
         FStar_Pervasives_Native.None) in
  let uu___ =
    let uu___1 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    mkFV uu___1 [] [] in
  let uu___1 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step in
  mk_emb em un uu___ uu___1
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h -> fun _args -> h);
    translate = (fun uu___ -> failwith "bogus_cbs translate")
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
      let uu___ = let uu___1 = e_list e in unembed uu___1 bogus_cbs in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu___
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t *
      FStar_Syntax_Syntax.meta_source_info FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | (a, uu___1) ->
        let uu___2 =
          match a.nbe_t with
          | Meta (t1, tm) ->
              let uu___3 = FStar_Thunk.force tm in
              (match uu___3 with
               | FStar_Syntax_Syntax.Meta_desugared m ->
                   (t1, (FStar_Pervasives_Native.Some m))
               | uu___4 -> (a, FStar_Pervasives_Native.None))
          | uu___3 -> (a, FStar_Pervasives_Native.None) in
        (match uu___2 with
         | (a1, m) ->
             (match a1.nbe_t with
              | FV
                  (fv1, [],
                   ({ nbe_t = Constant (Int i); nbe_r = uu___3;_}, uu___4)::[])
                  when
                  let uu___5 =
                    FStar_Ident.string_of_lid
                      (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  FStar_Util.ends_with uu___5 "int_to_t" ->
                  FStar_Pervasives_Native.Some (fv1, i, m)
              | uu___3 -> FStar_Pervasives_Native.None))
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t ->
    fun n ->
      let c = embed e_int bogus_cbs n in
      let int_to_t1 args1 =
        FStar_All.pipe_left mk_t (FV (int_to_t, [], args1)) in
      let uu___ = let uu___1 = as_arg c in [uu___1] in int_to_t1 uu___
let (with_meta_ds :
  t ->
    FStar_Syntax_Syntax.meta_source_info FStar_Pervasives_Native.option -> t)
  =
  fun t1 ->
    fun m ->
      match m with
      | FStar_Pervasives_Native.None -> t1
      | FStar_Pervasives_Native.Some m1 ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Thunk.mk
                  (fun uu___3 -> FStar_Syntax_Syntax.Meta_desugared m1) in
              (t1, uu___2) in
            Meta uu___1 in
          mk_t uu___
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
          let uu___ = f a1 in FStar_Pervasives_Native.Some uu___
      | uu___ -> FStar_Pervasives_Native.None
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
          let uu___ = f a0 a1 in FStar_Pervasives_Native.Some uu___
      | uu___ -> FStar_Pervasives_Native.None
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun f ->
      fun args1 ->
        let uu___ = FStar_List.map as_a args1 in lift_unary f uu___
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun f ->
      fun args1 ->
        let uu___ = FStar_List.map as_a args1 in lift_binary f uu___
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    unary_op arg_as_int
      (fun x -> let uu___ = f x in embed e_int bogus_cbs uu___)
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_int
      (fun x -> fun y -> let uu___ = f x y in embed e_int bogus_cbs uu___)
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f ->
    unary_op arg_as_bool
      (fun x -> let uu___ = f x in embed e_bool bogus_cbs uu___)
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_bool
      (fun x -> fun y -> let uu___ = f x y in embed e_bool bogus_cbs uu___)
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_string
      (fun x -> fun y -> let uu___ = f x y in embed e_string bogus_cbs uu___)
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
                let uu___ =
                  let uu___1 = as_a a1 in
                  let uu___2 = as_b b1 in (uu___1, uu___2) in
                (match uu___ with
                 | (FStar_Pervasives_Native.Some a2,
                    FStar_Pervasives_Native.Some b2) ->
                     let uu___1 = let uu___2 = f a2 b2 in embed_c uu___2 in
                     FStar_Pervasives_Native.Some uu___1
                 | uu___1 -> FStar_Pervasives_Native.None)
            | uu___ -> FStar_Pervasives_Native.None
let (list_of_string' : Prims.string -> t) =
  fun s ->
    let uu___ = e_list e_char in
    let uu___1 = FStar_String.list_of_string s in
    embed uu___ bogus_cbs uu___1
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l ->
    let s = FStar_String.string_of_list l in
    FStar_All.pipe_left mk_t (Constant (String (s, FStar_Range.dummyRange)))
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1 ->
    fun s2 ->
      let r = FStar_String.compare s1 s2 in
      let uu___ =
        let uu___1 = FStar_Util.string_of_int r in
        FStar_BigInt.big_int_of_string uu___1 in
      embed e_int bogus_cbs uu___
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu___ = arg_as_string a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some s1 ->
             let uu___1 = arg_as_list e_string a2 in
             (match uu___1 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu___2 = embed e_string bogus_cbs r in
                  FStar_Pervasives_Native.Some uu___2
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (string_of_int : FStar_BigInt.t -> t) =
  fun i ->
    let uu___ = FStar_BigInt.string_of_big_int i in
    embed e_string bogus_cbs uu___
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
      | (_typ, uu___)::(a1, uu___1)::(a2, uu___2)::[] ->
          let uu___3 = eq_t a1 a2 in
          (match uu___3 with
           | FStar_Syntax_Util.Equal ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu___4 -> FStar_Pervasives_Native.None)
      | uu___ -> failwith "Unexpected number of arguments"
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | (_u, uu___)::(_typ, uu___1)::(a1, uu___2)::(a2, uu___3)::[] ->
        let uu___4 = eq_t a1 a2 in
        (match uu___4 with
         | FStar_Syntax_Util.Equal ->
             let uu___5 = embed e_bool bogus_cbs true in
             FStar_Pervasives_Native.Some uu___5
         | FStar_Syntax_Util.NotEqual ->
             let uu___5 = embed e_bool bogus_cbs false in
             FStar_Pervasives_Native.Some uu___5
         | FStar_Syntax_Util.Unknown -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments"
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | (_u, uu___)::(_v, uu___1)::(t1, uu___2)::(t2, uu___3)::(a1, uu___4)::
        (a2, uu___5)::[] ->
        let uu___6 =
          let uu___7 = eq_t t1 t2 in
          let uu___8 = eq_t a1 a2 in FStar_Syntax_Util.eq_inj uu___7 uu___8 in
        (match uu___6 with
         | FStar_Syntax_Util.Equal ->
             let uu___7 = embed e_bool bogus_cbs true in
             FStar_Pervasives_Native.Some uu___7
         | FStar_Syntax_Util.NotEqual ->
             let uu___7 = embed e_bool bogus_cbs false in
             FStar_Pervasives_Native.Some uu___7
         | FStar_Syntax_Util.Unknown -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments"
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid ->
    fun args1 ->
      let uu___ =
        let uu___1 = FStar_Ident.string_of_lid lid in
        FStar_String.op_Hat "No interpretation for " uu___1 in
      failwith uu___
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | (a1, uu___)::[] ->
        let uu___1 = unembed e_range bogus_cbs a1 in
        (match uu___1 with
         | FStar_Pervasives_Native.Some r ->
             let uu___2 = embed e_range bogus_cbs r in
             FStar_Pervasives_Native.Some uu___2
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments"
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu___ = arg_as_list e_char a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some s1 ->
             let uu___1 = arg_as_string a2 in
             (match uu___1 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2 in
                  let uu___2 =
                    let uu___3 = e_list e_string in embed uu___3 bogus_cbs r in
                  FStar_Pervasives_Native.Some uu___2
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu___ =
          let uu___1 = arg_as_string a1 in
          let uu___2 = arg_as_int a2 in (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some i)
             ->
             (try
                (fun uu___1 ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i in
                       let uu___2 = embed e_char bogus_cbs r in
                       FStar_Pervasives_Native.Some uu___2) ()
              with | uu___1 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu___ =
          let uu___1 = arg_as_string a1 in
          let uu___2 = arg_as_char a2 in (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some c)
             ->
             (try
                (fun uu___1 ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c in
                       let uu___2 = embed e_int bogus_cbs r in
                       FStar_Pervasives_Native.Some uu___2) ()
              with | uu___1 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::a3::[] ->
        let uu___ =
          let uu___1 = arg_as_string a1 in
          let uu___2 = arg_as_int a2 in
          let uu___3 = arg_as_int a3 in (uu___1, uu___2, uu___3) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some n1,
            FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1 in
             let n21 = FStar_BigInt.to_int_fs n2 in
             (try
                (fun uu___1 ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21 in
                       let uu___2 = embed e_string bogus_cbs r in
                       FStar_Pervasives_Native.Some uu___2) ()
              with | uu___1 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu___ =
          let uu___1 = arg_as_string fn in
          let uu___2 = arg_as_int from_line in
          let uu___3 = arg_as_int from_col in
          let uu___4 = arg_as_int to_line in
          let uu___5 = arg_as_int to_col in
          (uu___1, uu___2, uu___3, uu___4, uu___5) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu___1 =
                 let uu___2 = FStar_BigInt.to_int_fs from_l in
                 let uu___3 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu___2 uu___3 in
               let uu___2 =
                 let uu___3 = FStar_BigInt.to_int_fs to_l in
                 let uu___4 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu___3 uu___4 in
               FStar_Range.mk_range fn1 uu___1 uu___2 in
             let uu___1 = embed e_range bogus_cbs r in
             FStar_Pervasives_Native.Some uu___1
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (and_op : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu___ = arg_as_bool a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some (false) ->
             let uu___1 = embed e_bool bogus_cbs false in
             FStar_Pervasives_Native.Some uu___1
         | FStar_Pervasives_Native.Some (true) ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst a2)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments"
let (or_op : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu___ = arg_as_bool a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some (true) ->
             let uu___1 = embed e_bool bogus_cbs true in
             FStar_Pervasives_Native.Some uu___1
         | FStar_Pervasives_Native.Some (false) ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst a2)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments"
let (division_op : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu___ =
          let uu___1 = arg_as_int a1 in
          let uu___2 = arg_as_int a2 in (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some m, FStar_Pervasives_Native.Some n)
             ->
             let uu___1 =
               let uu___2 = FStar_BigInt.to_int_fs n in
               uu___2 <> Prims.int_zero in
             if uu___1
             then
               let uu___2 =
                 let uu___3 = FStar_BigInt.div_big_int m n in
                 embed e_int bogus_cbs uu___3 in
               FStar_Pervasives_Native.Some uu___2
             else FStar_Pervasives_Native.None
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments"
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
                let uu___ = FStar_List.splitAt n_tvars args1 in
                match uu___ with
                | (_tvar_args, rest_args) ->
                    let uu___1 = FStar_List.hd rest_args in
                    (match uu___1 with
                     | (x, uu___2) ->
                         let uu___3 = unembed ea cb x in
                         FStar_Util.map_opt uu___3
                           (fun x1 -> let uu___4 = f x1 in embed eb cb uu___4)) in
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
                  let uu___ = FStar_List.splitAt n_tvars args1 in
                  match uu___ with
                  | (_tvar_args, rest_args) ->
                      let uu___1 = FStar_List.hd rest_args in
                      (match uu___1 with
                       | (x, uu___2) ->
                           let uu___3 =
                             let uu___4 = FStar_List.tl rest_args in
                             FStar_List.hd uu___4 in
                           (match uu___3 with
                            | (y, uu___4) ->
                                let uu___5 = unembed ea cb x in
                                FStar_Util.bind_opt uu___5
                                  (fun x1 ->
                                     let uu___6 = unembed eb cb y in
                                     FStar_Util.bind_opt uu___6
                                       (fun y1 ->
                                          let uu___7 =
                                            let uu___8 = f x1 y1 in
                                            embed ec cb uu___8 in
                                          FStar_Pervasives_Native.Some uu___7)))) in
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
                    let uu___ = FStar_List.splitAt n_tvars args1 in
                    match uu___ with
                    | (_tvar_args, rest_args) ->
                        let uu___1 = FStar_List.hd rest_args in
                        (match uu___1 with
                         | (x, uu___2) ->
                             let uu___3 =
                               let uu___4 = FStar_List.tl rest_args in
                               FStar_List.hd uu___4 in
                             (match uu___3 with
                              | (y, uu___4) ->
                                  let uu___5 =
                                    let uu___6 =
                                      let uu___7 = FStar_List.tl rest_args in
                                      FStar_List.tl uu___7 in
                                    FStar_List.hd uu___6 in
                                  (match uu___5 with
                                   | (z, uu___6) ->
                                       let uu___7 = unembed ea cb x in
                                       FStar_Util.bind_opt uu___7
                                         (fun x1 ->
                                            let uu___8 = unembed eb cb y in
                                            FStar_Util.bind_opt uu___8
                                              (fun y1 ->
                                                 let uu___9 = unembed ec cb z in
                                                 FStar_Util.bind_opt uu___9
                                                   (fun z1 ->
                                                      let uu___10 =
                                                        let uu___11 =
                                                          f x1 y1 z1 in
                                                        embed ed cb uu___11 in
                                                      FStar_Pervasives_Native.Some
                                                        uu___10)))))) in
                  f_wrapped