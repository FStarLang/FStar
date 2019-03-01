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
  fun projectee  ->
    match projectee with | Unit  -> true | uu____60721 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____60734 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____60757 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____60782 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____60818 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____60841 -> false
  
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee  -> match projectee with | Range _0 -> _0 
type atom =
  | Var of var 
  | Match of (t * (t -> t) *
  ((t -> FStar_Syntax_Syntax.term) -> FStar_Syntax_Syntax.branch Prims.list)) 
and t =
  | Lam of ((t Prims.list -> t) *
  (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list * Prims.int *
  (unit -> residual_comp) FStar_Pervasives_Native.option) 
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
  FStar_Util.either * t FStar_Common.thunk) 
  | Rec of (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
  Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list *
  Prims.int * Prims.bool Prims.list *
  (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)) 
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
    match projectee with | Var _0 -> true | uu____61224 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____61261 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____61362 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____61482 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____61546 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____61622 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____61684 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____61704 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____61724 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____61743 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____61775 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____61869 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____61931 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____61955 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____62001 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____62099 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____62233 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____62277 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____62315 -> false
  
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
    match projectee with | TOTAL  -> true | uu____62445 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____62456 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____62467 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____62478 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____62489 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____62500 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____62511 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____62522 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____62533 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____62545 -> false
  
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
  fun trm  ->
    match trm with | Accu uu____62622 -> true | uu____62634 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____62644,uu____62645) -> false
    | uu____62659 -> true
  
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
  fun uu___516_62795  ->
    if uu___516_62795
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_62806  ->
    if uu___517_62806
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
      | (FStar_Syntax_Util.NotEqual ,uu____62822) ->
          FStar_Syntax_Util.NotEqual
      | (uu____62823,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____62824) -> FStar_Syntax_Util.Unknown
      | (uu____62825,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____62842 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____62862),String (s2,uu____62864)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____62877,uu____62878) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____62914,Lam uu____62915) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____63004 = eq_atom a1 a2  in
          eq_and uu____63004 (fun uu____63006  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____63045 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63045
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____63061 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____63118  ->
                        match uu____63118 with
                        | ((a1,uu____63132),(a2,uu____63134)) ->
                            let uu____63143 = eq_t a1 a2  in
                            eq_inj acc uu____63143) FStar_Syntax_Util.Equal)
                uu____63061))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____63184 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63184
          then
            let uu____63187 =
              let uu____63188 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____63188  in
            eq_and uu____63187 (fun uu____63191  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____63198 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63198
      | (Univ u1,Univ u2) ->
          let uu____63202 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63202
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____63249 =
            let uu____63250 =
              let uu____63251 = t11 ()  in
              FStar_Pervasives_Native.fst uu____63251  in
            let uu____63256 =
              let uu____63257 = t21 ()  in
              FStar_Pervasives_Native.fst uu____63257  in
            eq_t uu____63250 uu____63256  in
          eq_and uu____63249
            (fun uu____63265  ->
               let uu____63266 =
                 let uu____63267 = mkAccuVar x  in r1 uu____63267  in
               let uu____63268 =
                 let uu____63269 = mkAccuVar x  in r2 uu____63269  in
               eq_t uu____63266 uu____63268)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____63270,uu____63271) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____63276,uu____63277) -> FStar_Syntax_Util.Unknown

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
          let uu____63358 = eq_arg x y  in
          eq_and uu____63358 (fun uu____63360  -> eq_args xs ys)
      | (uu____63361,uu____63362) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____63409) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____63414 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____63414
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____63443) ->
        let uu____63488 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____63499 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____63488 uu____63499
    | Accu (a,l) ->
        let uu____63516 =
          let uu____63518 = atom_to_string a  in
          let uu____63520 =
            let uu____63522 =
              let uu____63524 =
                let uu____63526 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____63526  in
              FStar_String.op_Hat uu____63524 ")"  in
            FStar_String.op_Hat ") (" uu____63522  in
          FStar_String.op_Hat uu____63518 uu____63520  in
        FStar_String.op_Hat "Accu (" uu____63516
    | Construct (fv,us,l) ->
        let uu____63564 =
          let uu____63566 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63568 =
            let uu____63570 =
              let uu____63572 =
                let uu____63574 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63574  in
              let uu____63580 =
                let uu____63582 =
                  let uu____63584 =
                    let uu____63586 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63586  in
                  FStar_String.op_Hat uu____63584 "]"  in
                FStar_String.op_Hat "] [" uu____63582  in
              FStar_String.op_Hat uu____63572 uu____63580  in
            FStar_String.op_Hat ") [" uu____63570  in
          FStar_String.op_Hat uu____63566 uu____63568  in
        FStar_String.op_Hat "Construct (" uu____63564
    | FV (fv,us,l) ->
        let uu____63625 =
          let uu____63627 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63629 =
            let uu____63631 =
              let uu____63633 =
                let uu____63635 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63635  in
              let uu____63641 =
                let uu____63643 =
                  let uu____63645 =
                    let uu____63647 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63647  in
                  FStar_String.op_Hat uu____63645 "]"  in
                FStar_String.op_Hat "] [" uu____63643  in
              FStar_String.op_Hat uu____63633 uu____63641  in
            FStar_String.op_Hat ") [" uu____63631  in
          FStar_String.op_Hat uu____63627 uu____63629  in
        FStar_String.op_Hat "FV (" uu____63625
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____63669 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____63669
    | Type_t u ->
        let uu____63673 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____63673
    | Arrow uu____63676 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____63722 = t ()  in FStar_Pervasives_Native.fst uu____63722
           in
        let uu____63727 =
          let uu____63729 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____63731 =
            let uu____63733 =
              let uu____63735 = t_to_string t1  in
              let uu____63737 =
                let uu____63739 =
                  let uu____63741 =
                    let uu____63743 =
                      let uu____63744 = mkAccuVar x1  in f uu____63744  in
                    t_to_string uu____63743  in
                  FStar_String.op_Hat uu____63741 "}"  in
                FStar_String.op_Hat "{" uu____63739  in
              FStar_String.op_Hat uu____63735 uu____63737  in
            FStar_String.op_Hat ":" uu____63733  in
          FStar_String.op_Hat uu____63729 uu____63731  in
        FStar_String.op_Hat "Refinement " uu____63727
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____63751 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____63751
    | Quote uu____63754 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____63761) ->
        let uu____63778 =
          let uu____63780 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____63780  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____63778
    | Lazy (FStar_Util.Inr (uu____63782,et),uu____63784) ->
        let uu____63801 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____63801
    | Rec
        (uu____63804,uu____63805,l,uu____63807,uu____63808,uu____63809,uu____63810)
        ->
        let uu____63855 =
          let uu____63857 =
            let uu____63859 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____63859  in
          FStar_String.op_Hat uu____63857 ")"  in
        FStar_String.op_Hat "Rec (" uu____63855

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____63870 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____63870
    | Match (t,uu____63874,uu____63875) ->
        let uu____63898 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____63898

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____63902 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____63902 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____63909 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____63909 (FStar_String.concat " ")

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
        let uu____64380 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____64380 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____64401 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____64401 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____64442  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____64457  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____64500 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____64500
         then
           let uu____64524 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____64524
         else ());
        (let uu____64529 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____64529
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____64563 = FStar_Dyn.mkdyn x  in (uu____64563, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____64631 'a .
    'Auu____64631 ->
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
              let uu____64682 = FStar_Common.force_thunk thunk1  in
              f uu____64682
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____64742 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____64742
              then
                let res =
                  let uu____64771 = FStar_Common.force_thunk thunk1  in
                  f uu____64771  in
                ((let uu____64813 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64813
                  then
                    let uu____64837 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____64839 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____64837
                      uu____64839
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____64848 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64848
                  then
                    let uu____64872 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____64872
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____64877 ->
              let aopt = f x  in
              ((let uu____64882 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____64882
                then
                  let uu____64906 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____64906
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
  let uu____64974 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____64974 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____65008 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____65013 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____65008 uu____65013 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____65054 -> FStar_Pervasives_Native.None  in
  let uu____65056 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____65061 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____65056 uu____65061 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____65103 -> FStar_Pervasives_Native.None  in
  let uu____65105 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____65110 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____65105 uu____65110 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____65152)) -> FStar_Pervasives_Native.Some s1
    | uu____65156 -> FStar_Pervasives_Native.None  in
  let uu____65158 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____65163 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____65158 uu____65163 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____65198 -> FStar_Pervasives_Native.None  in
  let uu____65199 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____65204 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____65199 uu____65204 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____65225 =
        let uu____65233 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____65233, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____65225  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____65258  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____65259 =
                 let uu____65260 =
                   let uu____65265 = type_of ea  in as_iarg uu____65265  in
                 [uu____65260]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65259
           | FStar_Pervasives_Native.Some x ->
               let uu____65275 =
                 let uu____65276 =
                   let uu____65281 = embed ea cb x  in as_arg uu____65281  in
                 let uu____65282 =
                   let uu____65289 =
                     let uu____65294 = type_of ea  in as_iarg uu____65294  in
                   [uu____65289]  in
                 uu____65276 :: uu____65282  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65275)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____65361)::uu____65362::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____65389 = unembed ea cb a  in
               FStar_Util.bind_opt uu____65389
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____65398 -> FStar_Pervasives_Native.None)
       in
    let uu____65401 =
      let uu____65402 =
        let uu____65403 = let uu____65408 = type_of ea  in as_arg uu____65408
           in
        [uu____65403]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____65402
       in
    mk_emb em un uu____65401 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65455 =
          let uu____65463 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____65463, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65455  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____65494  ->
             let uu____65495 =
               let uu____65496 =
                 let uu____65501 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____65501  in
               let uu____65502 =
                 let uu____65509 =
                   let uu____65514 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____65514  in
                 let uu____65515 =
                   let uu____65522 =
                     let uu____65527 = type_of eb  in as_iarg uu____65527  in
                   let uu____65528 =
                     let uu____65535 =
                       let uu____65540 = type_of ea  in as_iarg uu____65540
                        in
                     [uu____65535]  in
                   uu____65522 :: uu____65528  in
                 uu____65509 :: uu____65515  in
               uu____65496 :: uu____65502  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____65495)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____65608)::(a,uu____65610)::uu____65611::uu____65612::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____65651 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65651
                   (fun a1  ->
                      let uu____65661 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____65661
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____65674 -> FStar_Pervasives_Native.None)
         in
      let uu____65679 =
        let uu____65680 =
          let uu____65681 =
            let uu____65686 = type_of eb  in as_arg uu____65686  in
          let uu____65687 =
            let uu____65694 =
              let uu____65699 = type_of ea  in as_arg uu____65699  in
            [uu____65694]  in
          uu____65681 :: uu____65687  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____65680
         in
      mk_emb em un uu____65679 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65752 =
          let uu____65760 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____65760, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65752  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____65792  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____65794 =
                   let uu____65795 =
                     let uu____65800 = embed ea cb a  in as_arg uu____65800
                      in
                   let uu____65801 =
                     let uu____65808 =
                       let uu____65813 = type_of eb  in as_iarg uu____65813
                        in
                     let uu____65814 =
                       let uu____65821 =
                         let uu____65826 = type_of ea  in as_iarg uu____65826
                          in
                       [uu____65821]  in
                     uu____65808 :: uu____65814  in
                   uu____65795 :: uu____65801  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65794
             | FStar_Util.Inr b ->
                 let uu____65844 =
                   let uu____65845 =
                     let uu____65850 = embed eb cb b  in as_arg uu____65850
                      in
                   let uu____65851 =
                     let uu____65858 =
                       let uu____65863 = type_of eb  in as_iarg uu____65863
                        in
                     let uu____65864 =
                       let uu____65871 =
                         let uu____65876 = type_of ea  in as_iarg uu____65876
                          in
                       [uu____65871]  in
                     uu____65858 :: uu____65864  in
                   uu____65845 :: uu____65851  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65844)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____65938)::uu____65939::uu____65940::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____65975 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65975
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____65991)::uu____65992::uu____65993::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____66028 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____66028
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____66041 -> FStar_Pervasives_Native.None)
         in
      let uu____66046 =
        let uu____66047 =
          let uu____66048 =
            let uu____66053 = type_of eb  in as_arg uu____66053  in
          let uu____66054 =
            let uu____66061 =
              let uu____66066 = type_of ea  in as_arg uu____66066  in
            [uu____66061]  in
          uu____66048 :: uu____66054  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____66047
         in
      mk_emb em un uu____66046 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____66115 -> FStar_Pervasives_Native.None  in
  let uu____66116 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____66121 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____66116 uu____66121 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____66142 =
        let uu____66150 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____66150, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____66142  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____66177  ->
           let typ = let uu____66179 = type_of ea  in as_iarg uu____66179  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____66200 =
               let uu____66201 = as_arg tl1  in
               let uu____66206 =
                 let uu____66213 =
                   let uu____66218 = embed ea cb hd1  in as_arg uu____66218
                    in
                 [uu____66213; typ]  in
               uu____66201 :: uu____66206  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____66200
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____66266,uu____66267) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____66287,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____66290,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____66291))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66319 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66319
                 (fun hd2  ->
                    let uu____66327 = un cb tl1  in
                    FStar_Util.bind_opt uu____66327
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____66343,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66368 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66368
                 (fun hd2  ->
                    let uu____66376 = un cb tl1  in
                    FStar_Util.bind_opt uu____66376
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____66391 -> FStar_Pervasives_Native.None)
       in
    let uu____66394 =
      let uu____66395 =
        let uu____66396 = let uu____66401 = type_of ea  in as_arg uu____66401
           in
        [uu____66396]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____66395
       in
    mk_emb em un uu____66394 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____66474  ->
             Lam
               ((fun tas  ->
                   let uu____66504 =
                     let uu____66507 = FStar_List.hd tas  in
                     unembed ea cb uu____66507  in
                   match uu____66504 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____66509 = f a  in embed eb cb uu____66509
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____66522  ->
                     let uu____66525 = type_of eb  in as_arg uu____66525)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____66583 =
                 let uu____66586 =
                   let uu____66587 =
                     let uu____66588 =
                       let uu____66593 = embed ea cb x  in as_arg uu____66593
                        in
                     [uu____66588]  in
                   cb.iapp lam1 uu____66587  in
                 unembed eb cb uu____66586  in
               match uu____66583 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____66607 =
        let uu____66608 = type_of ea  in
        let uu____66609 =
          let uu____66610 = type_of eb  in as_iarg uu____66610  in
        make_arrow1 uu____66608 uu____66609  in
      mk_emb em un uu____66607 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____66628 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66628 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____66633 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66633 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____66638 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66638 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____66643 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66643 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____66648 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66648 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____66653 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66653 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____66658 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66658 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____66663 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66663 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____66668 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66668 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____66677 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66678 =
          let uu____66679 =
            let uu____66684 =
              let uu____66685 = e_list e_string  in embed uu____66685 cb l
               in
            as_arg uu____66684  in
          [uu____66679]  in
        mkFV uu____66677 [] uu____66678
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____66707 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66708 =
          let uu____66709 =
            let uu____66714 =
              let uu____66715 = e_list e_string  in embed uu____66715 cb l
               in
            as_arg uu____66714  in
          [uu____66709]  in
        mkFV uu____66707 [] uu____66708
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____66737 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66738 =
          let uu____66739 =
            let uu____66744 =
              let uu____66745 = e_list e_string  in embed uu____66745 cb l
               in
            as_arg uu____66744  in
          [uu____66739]  in
        mkFV uu____66737 [] uu____66738
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____66779,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____66795,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____66811,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____66827,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____66843,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____66859,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____66875,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____66891,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____66907,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____66923,(l,uu____66925)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____66944 =
          let uu____66950 = e_list e_string  in unembed uu____66950 cb l  in
        FStar_Util.bind_opt uu____66944
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66970  -> FStar_Pervasives_Native.Some _66970)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____66972,(l,uu____66974)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____66993 =
          let uu____66999 = e_list e_string  in unembed uu____66999 cb l  in
        FStar_Util.bind_opt uu____66993
          (fun ss  ->
             FStar_All.pipe_left
               (fun _67019  -> FStar_Pervasives_Native.Some _67019)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____67021,(l,uu____67023)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____67042 =
          let uu____67048 = e_list e_string  in unembed uu____67048 cb l  in
        FStar_Util.bind_opt uu____67042
          (fun ss  ->
             FStar_All.pipe_left
               (fun _67068  -> FStar_Pervasives_Native.Some _67068)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____67069 ->
        ((let uu____67071 =
            let uu____67077 =
              let uu____67079 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____67079
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67077)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67071);
         FStar_Pervasives_Native.None)
     in
  let uu____67083 =
    let uu____67084 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____67084 [] []  in
  let uu____67089 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____67083 uu____67089 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____67098  -> failwith "bogus_cbs translate")
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
      let uu____67175 =
        let uu____67184 = e_list e  in unembed uu____67184 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67175
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____67206  ->
    match uu____67206 with
    | (a,uu____67214) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____67229)::[]) when
             let uu____67246 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____67246 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____67253 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____67296 = let uu____67303 = as_arg c  in [uu____67303]  in
      int_to_t2 uu____67296
  
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
          let uu____67357 = f a  in FStar_Pervasives_Native.Some uu____67357
      | uu____67358 -> FStar_Pervasives_Native.None
  
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
          let uu____67412 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____67412
      | uu____67413 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67457 = FStar_List.map as_a args  in
        lift_unary f uu____67457
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67512 = FStar_List.map as_a args  in
        lift_binary f uu____67512
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____67542 = f x  in embed e_int bogus_cbs uu____67542)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____67569 = f x y  in embed e_int bogus_cbs uu____67569)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____67595 = f x  in embed e_bool bogus_cbs uu____67595)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____67633 = f x y  in embed e_bool bogus_cbs uu____67633)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____67671 = f x y  in embed e_string bogus_cbs uu____67671)
  
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
                let uu____67776 =
                  let uu____67785 = as_a a  in
                  let uu____67788 = as_b b  in (uu____67785, uu____67788)  in
                (match uu____67776 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____67803 =
                       let uu____67804 = f a1 b1  in embed_c uu____67804  in
                     FStar_Pervasives_Native.Some uu____67803
                 | uu____67805 -> FStar_Pervasives_Native.None)
            | uu____67814 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____67823 = e_list e_char  in
    let uu____67830 = FStar_String.list_of_string s  in
    embed uu____67823 bogus_cbs uu____67830
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____67869 =
        let uu____67870 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____67870  in
      embed e_int bogus_cbs uu____67869
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____67904 = arg_as_string a1  in
        (match uu____67904 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____67913 = arg_as_list e_string a2  in
             (match uu____67913 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____67931 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____67931
              | uu____67933 -> FStar_Pervasives_Native.None)
         | uu____67939 -> FStar_Pervasives_Native.None)
    | uu____67943 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____67950 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____67950
  
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
      | (_typ,uu____68012)::(a1,uu____68014)::(a2,uu____68016)::[] ->
          let uu____68033 = eq_t a1 a2  in
          (match uu____68033 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____68042 -> FStar_Pervasives_Native.None)
      | uu____68043 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68058)::(_typ,uu____68060)::(a1,uu____68062)::(a2,uu____68064)::[]
        ->
        let uu____68085 = eq_t a1 a2  in
        (match uu____68085 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68088 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68088
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68091 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68091
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68094 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68109)::(_v,uu____68111)::(t1,uu____68113)::(t2,uu____68115)::
        (a1,uu____68117)::(a2,uu____68119)::[] ->
        let uu____68148 =
          let uu____68149 = eq_t t1 t2  in
          let uu____68150 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____68149 uu____68150  in
        (match uu____68148 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68153 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68153
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68156 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68156
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68159 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____68178 =
        let uu____68180 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____68180  in
      failwith uu____68178
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____68196)::[] ->
        let uu____68205 = unembed e_range bogus_cbs a1  in
        (match uu____68205 with
         | FStar_Pervasives_Native.Some r ->
             let uu____68211 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68211
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____68212 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68248 = arg_as_list e_char a1  in
        (match uu____68248 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68264 = arg_as_string a2  in
             (match uu____68264 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68277 =
                    let uu____68278 = e_list e_string  in
                    embed uu____68278 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____68277
              | uu____68288 -> FStar_Pervasives_Native.None)
         | uu____68292 -> FStar_Pervasives_Native.None)
    | uu____68298 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68331 =
          let uu____68341 = arg_as_string a1  in
          let uu____68345 = arg_as_int a2  in (uu____68341, uu____68345)  in
        (match uu____68331 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_68369  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68374 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68374) ()
              with | uu___1496_68377 -> FStar_Pervasives_Native.None)
         | uu____68380 -> FStar_Pervasives_Native.None)
    | uu____68390 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68423 =
          let uu____68434 = arg_as_string a1  in
          let uu____68438 = arg_as_char a2  in (uu____68434, uu____68438)  in
        (match uu____68423 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_68467  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68471 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68471) ()
              with | uu___1514_68473 -> FStar_Pervasives_Native.None)
         | uu____68476 -> FStar_Pervasives_Native.None)
    | uu____68487 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____68529 =
          let uu____68543 = arg_as_string a1  in
          let uu____68547 = arg_as_int a2  in
          let uu____68550 = arg_as_int a3  in
          (uu____68543, uu____68547, uu____68550)  in
        (match uu____68529 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_68583  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68588 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68588) ()
              with | uu___1537_68591 -> FStar_Pervasives_Native.None)
         | uu____68594 -> FStar_Pervasives_Native.None)
    | uu____68608 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68668 =
          let uu____68690 = arg_as_string fn  in
          let uu____68694 = arg_as_int from_line  in
          let uu____68697 = arg_as_int from_col  in
          let uu____68700 = arg_as_int to_line  in
          let uu____68703 = arg_as_int to_col  in
          (uu____68690, uu____68694, uu____68697, uu____68700, uu____68703)
           in
        (match uu____68668 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68738 =
                 let uu____68739 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68741 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68739 uu____68741  in
               let uu____68743 =
                 let uu____68744 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68746 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68744 uu____68746  in
               FStar_Range.mk_range fn1 uu____68738 uu____68743  in
             let uu____68748 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68748
         | uu____68749 -> FStar_Pervasives_Native.None)
    | uu____68771 -> FStar_Pervasives_Native.None
  
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
                let uu____68861 = FStar_List.splitAt n_tvars args  in
                match uu____68861 with
                | (_tvar_args,rest_args) ->
                    let uu____68910 = FStar_List.hd rest_args  in
                    (match uu____68910 with
                     | (x,uu____68922) ->
                         let uu____68923 = unembed ea cb x  in
                         FStar_Util.map_opt uu____68923
                           (fun x1  ->
                              let uu____68929 = f x1  in
                              embed eb cb uu____68929))
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
                  let uu____69038 = FStar_List.splitAt n_tvars args  in
                  match uu____69038 with
                  | (_tvar_args,rest_args) ->
                      let uu____69087 = FStar_List.hd rest_args  in
                      (match uu____69087 with
                       | (x,uu____69099) ->
                           let uu____69100 =
                             let uu____69105 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____69105  in
                           (match uu____69100 with
                            | (y,uu____69123) ->
                                let uu____69124 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____69124
                                  (fun x1  ->
                                     let uu____69130 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____69130
                                       (fun y1  ->
                                          let uu____69136 =
                                            let uu____69137 = f x1 y1  in
                                            embed ec cb uu____69137  in
                                          FStar_Pervasives_Native.Some
                                            uu____69136))))
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
                    let uu____69265 = FStar_List.splitAt n_tvars args  in
                    match uu____69265 with
                    | (_tvar_args,rest_args) ->
                        let uu____69314 = FStar_List.hd rest_args  in
                        (match uu____69314 with
                         | (x,uu____69326) ->
                             let uu____69327 =
                               let uu____69332 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____69332  in
                             (match uu____69327 with
                              | (y,uu____69350) ->
                                  let uu____69351 =
                                    let uu____69356 =
                                      let uu____69363 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____69363  in
                                    FStar_List.hd uu____69356  in
                                  (match uu____69351 with
                                   | (z,uu____69385) ->
                                       let uu____69386 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____69386
                                         (fun x1  ->
                                            let uu____69392 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____69392
                                              (fun y1  ->
                                                 let uu____69398 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____69398
                                                   (fun z1  ->
                                                      let uu____69404 =
                                                        let uu____69405 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____69405
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____69404))))))
                     in
                  f_wrapped
  