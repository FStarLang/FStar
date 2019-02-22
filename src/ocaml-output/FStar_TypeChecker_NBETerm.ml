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
    match projectee with | Unit  -> true | uu____60647 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____60660 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____60683 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____60708 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____60744 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____60767 -> false
  
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
    match projectee with | Var _0 -> true | uu____61150 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____61187 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____61288 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____61408 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____61472 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____61548 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____61610 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____61630 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____61650 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____61669 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____61701 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____61795 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____61857 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____61881 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____61927 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____62025 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____62159 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____62203 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____62241 -> false
  
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
    match projectee with | TOTAL  -> true | uu____62371 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____62382 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____62393 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____62404 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____62415 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____62426 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____62437 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____62448 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____62459 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____62471 -> false
  
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
    match trm with | Accu uu____62548 -> true | uu____62560 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____62570,uu____62571) -> false
    | uu____62585 -> true
  
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
  fun uu___516_62721  ->
    if uu___516_62721
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_62732  ->
    if uu___517_62732
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
      | (FStar_Syntax_Util.NotEqual ,uu____62748) ->
          FStar_Syntax_Util.NotEqual
      | (uu____62749,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____62750) -> FStar_Syntax_Util.Unknown
      | (uu____62751,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____62768 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____62788),String (s2,uu____62790)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____62803,uu____62804) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____62840,Lam uu____62841) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____62930 = eq_atom a1 a2  in
          eq_and uu____62930 (fun uu____62932  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____62971 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____62971
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____62987 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____63044  ->
                        match uu____63044 with
                        | ((a1,uu____63058),(a2,uu____63060)) ->
                            let uu____63069 = eq_t a1 a2  in
                            eq_inj acc uu____63069) FStar_Syntax_Util.Equal)
                uu____62987))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____63110 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63110
          then
            let uu____63113 =
              let uu____63114 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____63114  in
            eq_and uu____63113 (fun uu____63117  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____63124 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63124
      | (Univ u1,Univ u2) ->
          let uu____63128 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63128
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____63175 =
            let uu____63176 =
              let uu____63177 = t11 ()  in
              FStar_Pervasives_Native.fst uu____63177  in
            let uu____63182 =
              let uu____63183 = t21 ()  in
              FStar_Pervasives_Native.fst uu____63183  in
            eq_t uu____63176 uu____63182  in
          eq_and uu____63175
            (fun uu____63191  ->
               let uu____63192 =
                 let uu____63193 = mkAccuVar x  in r1 uu____63193  in
               let uu____63194 =
                 let uu____63195 = mkAccuVar x  in r2 uu____63195  in
               eq_t uu____63192 uu____63194)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____63196,uu____63197) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____63202,uu____63203) -> FStar_Syntax_Util.Unknown

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
          let uu____63284 = eq_arg x y  in
          eq_and uu____63284 (fun uu____63286  -> eq_args xs ys)
      | (uu____63287,uu____63288) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____63335) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____63340 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____63340
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____63369) ->
        let uu____63414 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____63425 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____63414 uu____63425
    | Accu (a,l) ->
        let uu____63442 =
          let uu____63444 = atom_to_string a  in
          let uu____63446 =
            let uu____63448 =
              let uu____63450 =
                let uu____63452 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____63452  in
              FStar_String.op_Hat uu____63450 ")"  in
            FStar_String.op_Hat ") (" uu____63448  in
          FStar_String.op_Hat uu____63444 uu____63446  in
        FStar_String.op_Hat "Accu (" uu____63442
    | Construct (fv,us,l) ->
        let uu____63490 =
          let uu____63492 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63494 =
            let uu____63496 =
              let uu____63498 =
                let uu____63500 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63500  in
              let uu____63506 =
                let uu____63508 =
                  let uu____63510 =
                    let uu____63512 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63512  in
                  FStar_String.op_Hat uu____63510 "]"  in
                FStar_String.op_Hat "] [" uu____63508  in
              FStar_String.op_Hat uu____63498 uu____63506  in
            FStar_String.op_Hat ") [" uu____63496  in
          FStar_String.op_Hat uu____63492 uu____63494  in
        FStar_String.op_Hat "Construct (" uu____63490
    | FV (fv,us,l) ->
        let uu____63551 =
          let uu____63553 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63555 =
            let uu____63557 =
              let uu____63559 =
                let uu____63561 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63561  in
              let uu____63567 =
                let uu____63569 =
                  let uu____63571 =
                    let uu____63573 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63573  in
                  FStar_String.op_Hat uu____63571 "]"  in
                FStar_String.op_Hat "] [" uu____63569  in
              FStar_String.op_Hat uu____63559 uu____63567  in
            FStar_String.op_Hat ") [" uu____63557  in
          FStar_String.op_Hat uu____63553 uu____63555  in
        FStar_String.op_Hat "FV (" uu____63551
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____63595 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____63595
    | Type_t u ->
        let uu____63599 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____63599
    | Arrow uu____63602 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____63648 = t ()  in FStar_Pervasives_Native.fst uu____63648
           in
        let uu____63653 =
          let uu____63655 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____63657 =
            let uu____63659 =
              let uu____63661 = t_to_string t1  in
              let uu____63663 =
                let uu____63665 =
                  let uu____63667 =
                    let uu____63669 =
                      let uu____63670 = mkAccuVar x1  in f uu____63670  in
                    t_to_string uu____63669  in
                  FStar_String.op_Hat uu____63667 "}"  in
                FStar_String.op_Hat "{" uu____63665  in
              FStar_String.op_Hat uu____63661 uu____63663  in
            FStar_String.op_Hat ":" uu____63659  in
          FStar_String.op_Hat uu____63655 uu____63657  in
        FStar_String.op_Hat "Refinement " uu____63653
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____63677 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____63677
    | Quote uu____63680 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____63687) ->
        let uu____63704 =
          let uu____63706 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____63706  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____63704
    | Lazy (FStar_Util.Inr (uu____63708,et),uu____63710) ->
        let uu____63727 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____63727
    | Rec
        (uu____63730,uu____63731,l,uu____63733,uu____63734,uu____63735,uu____63736)
        ->
        let uu____63781 =
          let uu____63783 =
            let uu____63785 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____63785  in
          FStar_String.op_Hat uu____63783 ")"  in
        FStar_String.op_Hat "Rec (" uu____63781

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____63796 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____63796
    | Match (t,uu____63800,uu____63801) ->
        let uu____63824 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____63824

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____63828 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____63828 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____63835 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____63835 (FStar_String.concat " ")

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
        let uu____64306 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____64306 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____64327 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____64327 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____64368  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____64383  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____64426 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____64426
         then
           let uu____64450 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____64450
         else ());
        (let uu____64455 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____64455
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____64489 = FStar_Dyn.mkdyn x  in (uu____64489, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____64557 'a .
    'Auu____64557 ->
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
              let uu____64608 = FStar_Common.force_thunk thunk1  in
              f uu____64608
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____64668 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____64668
              then
                let res =
                  let uu____64697 = FStar_Common.force_thunk thunk1  in
                  f uu____64697  in
                ((let uu____64739 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64739
                  then
                    let uu____64763 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____64765 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____64763
                      uu____64765
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____64774 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64774
                  then
                    let uu____64798 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____64798
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____64803 ->
              let aopt = f x  in
              ((let uu____64808 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____64808
                then
                  let uu____64832 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____64832
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
  let uu____64900 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____64900 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____64934 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____64939 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____64934 uu____64939 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____64980 -> FStar_Pervasives_Native.None  in
  let uu____64982 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____64987 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____64982 uu____64987 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____65029 -> FStar_Pervasives_Native.None  in
  let uu____65031 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____65036 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____65031 uu____65036 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____65078)) -> FStar_Pervasives_Native.Some s1
    | uu____65082 -> FStar_Pervasives_Native.None  in
  let uu____65084 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____65089 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____65084 uu____65089 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____65124 -> FStar_Pervasives_Native.None  in
  let uu____65125 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____65130 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____65125 uu____65130 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____65151 =
        let uu____65159 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____65159, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____65151  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____65184  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____65185 =
                 let uu____65186 =
                   let uu____65191 = type_of ea  in as_iarg uu____65191  in
                 [uu____65186]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65185
           | FStar_Pervasives_Native.Some x ->
               let uu____65201 =
                 let uu____65202 =
                   let uu____65207 = embed ea cb x  in as_arg uu____65207  in
                 let uu____65208 =
                   let uu____65215 =
                     let uu____65220 = type_of ea  in as_iarg uu____65220  in
                   [uu____65215]  in
                 uu____65202 :: uu____65208  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65201)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____65287)::uu____65288::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____65315 = unembed ea cb a  in
               FStar_Util.bind_opt uu____65315
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____65324 -> FStar_Pervasives_Native.None)
       in
    let uu____65327 =
      let uu____65328 =
        let uu____65329 = let uu____65334 = type_of ea  in as_arg uu____65334
           in
        [uu____65329]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____65328
       in
    mk_emb em un uu____65327 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65381 =
          let uu____65389 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____65389, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65381  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____65420  ->
             let uu____65421 =
               let uu____65422 =
                 let uu____65427 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____65427  in
               let uu____65428 =
                 let uu____65435 =
                   let uu____65440 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____65440  in
                 let uu____65441 =
                   let uu____65448 =
                     let uu____65453 = type_of eb  in as_iarg uu____65453  in
                   let uu____65454 =
                     let uu____65461 =
                       let uu____65466 = type_of ea  in as_iarg uu____65466
                        in
                     [uu____65461]  in
                   uu____65448 :: uu____65454  in
                 uu____65435 :: uu____65441  in
               uu____65422 :: uu____65428  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____65421)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____65534)::(a,uu____65536)::uu____65537::uu____65538::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____65577 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65577
                   (fun a1  ->
                      let uu____65587 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____65587
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____65600 -> FStar_Pervasives_Native.None)
         in
      let uu____65605 =
        let uu____65606 =
          let uu____65607 =
            let uu____65612 = type_of eb  in as_arg uu____65612  in
          let uu____65613 =
            let uu____65620 =
              let uu____65625 = type_of ea  in as_arg uu____65625  in
            [uu____65620]  in
          uu____65607 :: uu____65613  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____65606
         in
      mk_emb em un uu____65605 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65678 =
          let uu____65686 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____65686, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65678  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____65718  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____65720 =
                   let uu____65721 =
                     let uu____65726 = embed ea cb a  in as_arg uu____65726
                      in
                   let uu____65727 =
                     let uu____65734 =
                       let uu____65739 = type_of eb  in as_iarg uu____65739
                        in
                     let uu____65740 =
                       let uu____65747 =
                         let uu____65752 = type_of ea  in as_iarg uu____65752
                          in
                       [uu____65747]  in
                     uu____65734 :: uu____65740  in
                   uu____65721 :: uu____65727  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65720
             | FStar_Util.Inr b ->
                 let uu____65770 =
                   let uu____65771 =
                     let uu____65776 = embed eb cb b  in as_arg uu____65776
                      in
                   let uu____65777 =
                     let uu____65784 =
                       let uu____65789 = type_of eb  in as_iarg uu____65789
                        in
                     let uu____65790 =
                       let uu____65797 =
                         let uu____65802 = type_of ea  in as_iarg uu____65802
                          in
                       [uu____65797]  in
                     uu____65784 :: uu____65790  in
                   uu____65771 :: uu____65777  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65770)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____65864)::uu____65865::uu____65866::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____65901 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65901
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____65917)::uu____65918::uu____65919::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____65954 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____65954
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____65967 -> FStar_Pervasives_Native.None)
         in
      let uu____65972 =
        let uu____65973 =
          let uu____65974 =
            let uu____65979 = type_of eb  in as_arg uu____65979  in
          let uu____65980 =
            let uu____65987 =
              let uu____65992 = type_of ea  in as_arg uu____65992  in
            [uu____65987]  in
          uu____65974 :: uu____65980  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____65973
         in
      mk_emb em un uu____65972 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____66041 -> FStar_Pervasives_Native.None  in
  let uu____66042 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____66047 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____66042 uu____66047 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____66068 =
        let uu____66076 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____66076, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____66068  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____66103  ->
           let typ = let uu____66105 = type_of ea  in as_iarg uu____66105  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____66126 =
               let uu____66127 = as_arg tl1  in
               let uu____66132 =
                 let uu____66139 =
                   let uu____66144 = embed ea cb hd1  in as_arg uu____66144
                    in
                 [uu____66139; typ]  in
               uu____66127 :: uu____66132  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____66126
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____66192,uu____66193) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____66213,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____66216,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____66217))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66245 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66245
                 (fun hd2  ->
                    let uu____66253 = un cb tl1  in
                    FStar_Util.bind_opt uu____66253
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____66269,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66294 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66294
                 (fun hd2  ->
                    let uu____66302 = un cb tl1  in
                    FStar_Util.bind_opt uu____66302
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____66317 -> FStar_Pervasives_Native.None)
       in
    let uu____66320 =
      let uu____66321 =
        let uu____66322 = let uu____66327 = type_of ea  in as_arg uu____66327
           in
        [uu____66322]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____66321
       in
    mk_emb em un uu____66320 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____66400  ->
             Lam
               ((fun tas  ->
                   let uu____66430 =
                     let uu____66433 = FStar_List.hd tas  in
                     unembed ea cb uu____66433  in
                   match uu____66430 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____66435 = f a  in embed eb cb uu____66435
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____66448  ->
                     let uu____66451 = type_of eb  in as_arg uu____66451)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____66509 =
                 let uu____66512 =
                   let uu____66513 =
                     let uu____66514 =
                       let uu____66519 = embed ea cb x  in as_arg uu____66519
                        in
                     [uu____66514]  in
                   cb.iapp lam1 uu____66513  in
                 unembed eb cb uu____66512  in
               match uu____66509 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____66533 =
        let uu____66534 = type_of ea  in
        let uu____66535 =
          let uu____66536 = type_of eb  in as_iarg uu____66536  in
        make_arrow1 uu____66534 uu____66535  in
      mk_emb em un uu____66533 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____66554 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66554 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____66559 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66559 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____66564 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66564 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____66569 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66569 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____66574 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66574 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____66579 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66579 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____66584 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66584 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____66589 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66589 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____66594 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66594 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____66603 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66604 =
          let uu____66605 =
            let uu____66610 =
              let uu____66611 = e_list e_string  in embed uu____66611 cb l
               in
            as_arg uu____66610  in
          [uu____66605]  in
        mkFV uu____66603 [] uu____66604
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____66633 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66634 =
          let uu____66635 =
            let uu____66640 =
              let uu____66641 = e_list e_string  in embed uu____66641 cb l
               in
            as_arg uu____66640  in
          [uu____66635]  in
        mkFV uu____66633 [] uu____66634
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____66663 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66664 =
          let uu____66665 =
            let uu____66670 =
              let uu____66671 = e_list e_string  in embed uu____66671 cb l
               in
            as_arg uu____66670  in
          [uu____66665]  in
        mkFV uu____66663 [] uu____66664
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____66705,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____66721,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____66737,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____66753,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____66769,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____66785,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____66801,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____66817,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____66833,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____66849,(l,uu____66851)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____66870 =
          let uu____66876 = e_list e_string  in unembed uu____66876 cb l  in
        FStar_Util.bind_opt uu____66870
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66896  -> FStar_Pervasives_Native.Some _66896)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____66898,(l,uu____66900)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____66919 =
          let uu____66925 = e_list e_string  in unembed uu____66925 cb l  in
        FStar_Util.bind_opt uu____66919
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66945  -> FStar_Pervasives_Native.Some _66945)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____66947,(l,uu____66949)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____66968 =
          let uu____66974 = e_list e_string  in unembed uu____66974 cb l  in
        FStar_Util.bind_opt uu____66968
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66994  -> FStar_Pervasives_Native.Some _66994)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____66995 ->
        ((let uu____66997 =
            let uu____67003 =
              let uu____67005 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____67005
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67003)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____66997);
         FStar_Pervasives_Native.None)
     in
  let uu____67009 =
    let uu____67010 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____67010 [] []  in
  let uu____67015 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____67009 uu____67015 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____67024  -> failwith "bogus_cbs translate")
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
      let uu____67101 =
        let uu____67110 = e_list e  in unembed uu____67110 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67101
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____67132  ->
    match uu____67132 with
    | (a,uu____67140) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____67155)::[]) when
             let uu____67172 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____67172 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____67179 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____67222 = let uu____67229 = as_arg c  in [uu____67229]  in
      int_to_t2 uu____67222
  
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
          let uu____67283 = f a  in FStar_Pervasives_Native.Some uu____67283
      | uu____67284 -> FStar_Pervasives_Native.None
  
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
          let uu____67338 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____67338
      | uu____67339 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67383 = FStar_List.map as_a args  in
        lift_unary f uu____67383
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67438 = FStar_List.map as_a args  in
        lift_binary f uu____67438
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____67468 = f x  in embed e_int bogus_cbs uu____67468)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____67495 = f x y  in embed e_int bogus_cbs uu____67495)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____67521 = f x  in embed e_bool bogus_cbs uu____67521)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____67559 = f x y  in embed e_bool bogus_cbs uu____67559)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____67597 = f x y  in embed e_string bogus_cbs uu____67597)
  
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
                let uu____67702 =
                  let uu____67711 = as_a a  in
                  let uu____67714 = as_b b  in (uu____67711, uu____67714)  in
                (match uu____67702 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____67729 =
                       let uu____67730 = f a1 b1  in embed_c uu____67730  in
                     FStar_Pervasives_Native.Some uu____67729
                 | uu____67731 -> FStar_Pervasives_Native.None)
            | uu____67740 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____67749 = e_list e_char  in
    let uu____67756 = FStar_String.list_of_string s  in
    embed uu____67749 bogus_cbs uu____67756
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____67795 =
        let uu____67796 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____67796  in
      embed e_int bogus_cbs uu____67795
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____67830 = arg_as_string a1  in
        (match uu____67830 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____67839 = arg_as_list e_string a2  in
             (match uu____67839 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____67857 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____67857
              | uu____67859 -> FStar_Pervasives_Native.None)
         | uu____67865 -> FStar_Pervasives_Native.None)
    | uu____67869 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____67876 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____67876
  
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
      | (_typ,uu____67938)::(a1,uu____67940)::(a2,uu____67942)::[] ->
          let uu____67959 = eq_t a1 a2  in
          (match uu____67959 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____67968 -> FStar_Pervasives_Native.None)
      | uu____67969 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____67984)::(_typ,uu____67986)::(a1,uu____67988)::(a2,uu____67990)::[]
        ->
        let uu____68011 = eq_t a1 a2  in
        (match uu____68011 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68014 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68014
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68017 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68017
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68020 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68035)::(_v,uu____68037)::(t1,uu____68039)::(t2,uu____68041)::
        (a1,uu____68043)::(a2,uu____68045)::[] ->
        let uu____68074 =
          let uu____68075 = eq_t t1 t2  in
          let uu____68076 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____68075 uu____68076  in
        (match uu____68074 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68079 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68079
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68082 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68082
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68085 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____68104 =
        let uu____68106 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____68106  in
      failwith uu____68104
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____68122)::[] ->
        let uu____68131 = unembed e_range bogus_cbs a1  in
        (match uu____68131 with
         | FStar_Pervasives_Native.Some r ->
             let uu____68137 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68137
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____68138 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68174 = arg_as_list e_char a1  in
        (match uu____68174 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68190 = arg_as_string a2  in
             (match uu____68190 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68203 =
                    let uu____68204 = e_list e_string  in
                    embed uu____68204 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____68203
              | uu____68214 -> FStar_Pervasives_Native.None)
         | uu____68218 -> FStar_Pervasives_Native.None)
    | uu____68224 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68257 =
          let uu____68267 = arg_as_string a1  in
          let uu____68271 = arg_as_int a2  in (uu____68267, uu____68271)  in
        (match uu____68257 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_68295  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68300 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68300) ()
              with | uu___1496_68303 -> FStar_Pervasives_Native.None)
         | uu____68306 -> FStar_Pervasives_Native.None)
    | uu____68316 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68349 =
          let uu____68360 = arg_as_string a1  in
          let uu____68364 = arg_as_char a2  in (uu____68360, uu____68364)  in
        (match uu____68349 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_68393  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68397 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68397) ()
              with | uu___1514_68399 -> FStar_Pervasives_Native.None)
         | uu____68402 -> FStar_Pervasives_Native.None)
    | uu____68413 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____68455 =
          let uu____68469 = arg_as_string a1  in
          let uu____68473 = arg_as_int a2  in
          let uu____68476 = arg_as_int a3  in
          (uu____68469, uu____68473, uu____68476)  in
        (match uu____68455 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_68509  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68514 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68514) ()
              with | uu___1537_68517 -> FStar_Pervasives_Native.None)
         | uu____68520 -> FStar_Pervasives_Native.None)
    | uu____68534 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68594 =
          let uu____68616 = arg_as_string fn  in
          let uu____68620 = arg_as_int from_line  in
          let uu____68623 = arg_as_int from_col  in
          let uu____68626 = arg_as_int to_line  in
          let uu____68629 = arg_as_int to_col  in
          (uu____68616, uu____68620, uu____68623, uu____68626, uu____68629)
           in
        (match uu____68594 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68664 =
                 let uu____68665 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68667 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68665 uu____68667  in
               let uu____68669 =
                 let uu____68670 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68672 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68670 uu____68672  in
               FStar_Range.mk_range fn1 uu____68664 uu____68669  in
             let uu____68674 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68674
         | uu____68675 -> FStar_Pervasives_Native.None)
    | uu____68697 -> FStar_Pervasives_Native.None
  
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
                let uu____68787 = FStar_List.splitAt n_tvars args  in
                match uu____68787 with
                | (_tvar_args,rest_args) ->
                    let uu____68836 = FStar_List.hd rest_args  in
                    (match uu____68836 with
                     | (x,uu____68848) ->
                         let uu____68849 = unembed ea cb x  in
                         FStar_Util.map_opt uu____68849
                           (fun x1  ->
                              let uu____68855 = f x1  in
                              embed eb cb uu____68855))
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
                  let uu____68964 = FStar_List.splitAt n_tvars args  in
                  match uu____68964 with
                  | (_tvar_args,rest_args) ->
                      let uu____69013 = FStar_List.hd rest_args  in
                      (match uu____69013 with
                       | (x,uu____69025) ->
                           let uu____69026 =
                             let uu____69031 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____69031  in
                           (match uu____69026 with
                            | (y,uu____69049) ->
                                let uu____69050 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____69050
                                  (fun x1  ->
                                     let uu____69056 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____69056
                                       (fun y1  ->
                                          let uu____69062 =
                                            let uu____69063 = f x1 y1  in
                                            embed ec cb uu____69063  in
                                          FStar_Pervasives_Native.Some
                                            uu____69062))))
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
                    let uu____69191 = FStar_List.splitAt n_tvars args  in
                    match uu____69191 with
                    | (_tvar_args,rest_args) ->
                        let uu____69240 = FStar_List.hd rest_args  in
                        (match uu____69240 with
                         | (x,uu____69252) ->
                             let uu____69253 =
                               let uu____69258 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____69258  in
                             (match uu____69253 with
                              | (y,uu____69276) ->
                                  let uu____69277 =
                                    let uu____69282 =
                                      let uu____69289 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____69289  in
                                    FStar_List.hd uu____69282  in
                                  (match uu____69277 with
                                   | (z,uu____69311) ->
                                       let uu____69312 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____69312
                                         (fun x1  ->
                                            let uu____69318 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____69318
                                              (fun y1  ->
                                                 let uu____69324 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____69324
                                                   (fun z1  ->
                                                      let uu____69330 =
                                                        let uu____69331 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____69331
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____69330))))))
                     in
                  f_wrapped
  