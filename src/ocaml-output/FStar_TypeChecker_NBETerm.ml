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
    match projectee with | Var _0 -> true | uu____667 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____732 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____851 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____991 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____1057 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____1144 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1214 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1233 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1252 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1270 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1302 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1395 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1456 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1485 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1552 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1682 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1878 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1921 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1963 -> false
  
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
    match projectee with | TOTAL  -> true | uu____2203 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____2214 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____2225 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____2236 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____2247 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____2258 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____2269 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____2280 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____2291 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____2303 -> false
  
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
  fun trm  -> match trm with | Accu uu____2449 -> true | uu____2461 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____2471,uu____2472) -> false | uu____2486 -> true
  
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
  fun uu___0_2662  ->
    if uu___0_2662
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2673  ->
    if uu___1_2673
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
      | (FStar_Syntax_Util.NotEqual ,uu____2689) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2690,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2691) -> FStar_Syntax_Util.Unknown
      | (uu____2692,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2709 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2729),String (s2,uu____2731)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2744,uu____2745) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2781,Lam uu____2782) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2885 = eq_atom a1 a2  in
          eq_and uu____2885 (fun uu____2887  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2938 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2938
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2954 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____3011  ->
                        match uu____3011 with
                        | ((a1,uu____3025),(a2,uu____3027)) ->
                            let uu____3036 = eq_t a1 a2  in
                            eq_inj acc uu____3036) FStar_Syntax_Util.Equal)
                uu____2954))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____3089 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____3089
          then
            let uu____3092 =
              let uu____3093 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____3093  in
            eq_and uu____3092 (fun uu____3096  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____3103 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3103
      | (Univ u1,Univ u2) ->
          let uu____3107 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3107
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____3164 =
            let uu____3165 =
              let uu____3166 = t11 ()  in
              FStar_Pervasives_Native.fst uu____3166  in
            let uu____3171 =
              let uu____3172 = t21 ()  in
              FStar_Pervasives_Native.fst uu____3172  in
            eq_t uu____3165 uu____3171  in
          eq_and uu____3164
            (fun uu____3180  ->
               let uu____3181 =
                 let uu____3182 = mkAccuVar x  in r1 uu____3182  in
               let uu____3183 =
                 let uu____3184 = mkAccuVar x  in r2 uu____3184  in
               eq_t uu____3181 uu____3183)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____3185,uu____3186) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____3201,uu____3202) -> FStar_Syntax_Util.Unknown

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
          let uu____3283 = eq_arg x y  in
          eq_and uu____3283 (fun uu____3285  -> eq_args xs ys)
      | (uu____3286,uu____3287) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____3334) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____3339 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____3339
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____3368) ->
        let uu____3427 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____3438 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____3427 uu____3438
    | Accu (a,l) ->
        let uu____3455 =
          let uu____3457 = atom_to_string a  in
          let uu____3459 =
            let uu____3461 =
              let uu____3463 =
                let uu____3465 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____3465  in
              FStar_String.op_Hat uu____3463 ")"  in
            FStar_String.op_Hat ") (" uu____3461  in
          FStar_String.op_Hat uu____3457 uu____3459  in
        FStar_String.op_Hat "Accu (" uu____3455
    | Construct (fv,us,l) ->
        let uu____3509 =
          let uu____3511 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3513 =
            let uu____3515 =
              let uu____3517 =
                let uu____3519 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3519  in
              let uu____3525 =
                let uu____3527 =
                  let uu____3529 =
                    let uu____3531 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3531  in
                  FStar_String.op_Hat uu____3529 "]"  in
                FStar_String.op_Hat "] [" uu____3527  in
              FStar_String.op_Hat uu____3517 uu____3525  in
            FStar_String.op_Hat ") [" uu____3515  in
          FStar_String.op_Hat uu____3511 uu____3513  in
        FStar_String.op_Hat "Construct (" uu____3509
    | FV (fv,us,l) ->
        let uu____3576 =
          let uu____3578 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3580 =
            let uu____3582 =
              let uu____3584 =
                let uu____3586 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3586  in
              let uu____3592 =
                let uu____3594 =
                  let uu____3596 =
                    let uu____3598 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3598  in
                  FStar_String.op_Hat uu____3596 "]"  in
                FStar_String.op_Hat "] [" uu____3594  in
              FStar_String.op_Hat uu____3584 uu____3592  in
            FStar_String.op_Hat ") [" uu____3582  in
          FStar_String.op_Hat uu____3578 uu____3580  in
        FStar_String.op_Hat "FV (" uu____3576
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3620 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3620
    | Type_t u ->
        let uu____3624 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3624
    | Arrow uu____3627 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3683 = t ()  in FStar_Pervasives_Native.fst uu____3683
           in
        let uu____3688 =
          let uu____3690 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3692 =
            let uu____3694 =
              let uu____3696 = t_to_string t1  in
              let uu____3698 =
                let uu____3700 =
                  let uu____3702 =
                    let uu____3704 =
                      let uu____3705 = mkAccuVar x1  in f uu____3705  in
                    t_to_string uu____3704  in
                  FStar_String.op_Hat uu____3702 "}"  in
                FStar_String.op_Hat "{" uu____3700  in
              FStar_String.op_Hat uu____3696 uu____3698  in
            FStar_String.op_Hat ":" uu____3694  in
          FStar_String.op_Hat uu____3690 uu____3692  in
        FStar_String.op_Hat "Refinement " uu____3688
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____3712 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____3712
    | Quote uu____3715 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3728) ->
        let uu____3757 =
          let uu____3759 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3759  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3757
    | Lazy (FStar_Util.Inr (uu____3769,et),uu____3771) ->
        let uu____3796 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3796
    | Rec
        (uu____3799,uu____3800,l,uu____3802,uu____3803,uu____3804,uu____3805)
        ->
        let uu____3892 =
          let uu____3894 =
            let uu____3896 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____3896  in
          FStar_String.op_Hat uu____3894 ")"  in
        FStar_String.op_Hat "Rec (" uu____3892

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3912 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3912
    | Match (t,uu____3916,uu____3917) ->
        let uu____3948 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3948

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3952 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3952 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3959 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3959 (FStar_String.concat " ")

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
        let uu____4667 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____4667 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____4702 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____4702 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____4749  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____4764  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____4807 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____4807
         then
           let uu____4831 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4831
         else ());
        (let uu____4836 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4836
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li = let uu____4870 = FStar_Dyn.mkdyn x  in (uu____4870, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____4906 'a .
    'Auu____4906 ->
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
              let uu____4969 = FStar_Common.force_thunk thunk1  in
              f uu____4969
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____4997 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4997
              then
                let res =
                  let uu____5026 = FStar_Common.force_thunk thunk1  in
                  f uu____5026  in
                ((let uu____5028 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____5028
                  then
                    let uu____5052 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____5054 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____5052
                      uu____5054
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____5063 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____5063
                  then
                    let uu____5087 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____5087
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____5092 ->
              let aopt = f x  in
              ((let uu____5097 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____5097
                then
                  let uu____5121 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____5121
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
  let uu____5249 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____5249 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____5313 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____5318 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____5313 uu____5318 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____5389 -> FStar_Pervasives_Native.None  in
  let uu____5391 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____5396 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____5391 uu____5396 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____5468 -> FStar_Pervasives_Native.None  in
  let uu____5470 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____5475 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____5470 uu____5475 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____5547)) -> FStar_Pervasives_Native.Some s1
    | uu____5551 -> FStar_Pervasives_Native.None  in
  let uu____5553 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____5558 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____5553 uu____5558 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____5623 -> FStar_Pervasives_Native.None  in
  let uu____5624 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____5629 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____5624 uu____5629 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____5664 =
        let uu____5672 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____5672, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5664  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____5709  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____5710 =
                 let uu____5711 =
                   let uu____5716 = type_of ea  in as_iarg uu____5716  in
                 [uu____5711]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5710
           | FStar_Pervasives_Native.Some x ->
               let uu____5726 =
                 let uu____5727 =
                   let uu____5732 = embed ea cb x  in as_arg uu____5732  in
                 let uu____5733 =
                   let uu____5740 =
                     let uu____5745 = type_of ea  in as_iarg uu____5745  in
                   [uu____5740]  in
                 uu____5727 :: uu____5733  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5726)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____5830)::uu____5831::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____5864 = unembed ea cb a  in
               FStar_Util.bind_opt uu____5864
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____5873 -> FStar_Pervasives_Native.None)
       in
    let uu____5876 =
      let uu____5877 =
        let uu____5878 = let uu____5883 = type_of ea  in as_arg uu____5883
           in
        [uu____5878]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____5877
       in
    mk_emb em un uu____5876 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5951 =
          let uu____5959 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____5959, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5951  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____6002  ->
             let uu____6003 =
               let uu____6004 =
                 let uu____6009 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____6009  in
               let uu____6010 =
                 let uu____6017 =
                   let uu____6022 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____6022  in
                 let uu____6023 =
                   let uu____6030 =
                     let uu____6035 = type_of eb  in as_iarg uu____6035  in
                   let uu____6036 =
                     let uu____6043 =
                       let uu____6048 = type_of ea  in as_iarg uu____6048  in
                     [uu____6043]  in
                   uu____6030 :: uu____6036  in
                 uu____6017 :: uu____6023  in
               uu____6004 :: uu____6010  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____6003)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____6128)::(a,uu____6130)::uu____6131::uu____6132::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____6177 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____6177
                   (fun a1  ->
                      let uu____6187 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____6187
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____6200 -> FStar_Pervasives_Native.None)
         in
      let uu____6205 =
        let uu____6206 =
          let uu____6207 = let uu____6212 = type_of eb  in as_arg uu____6212
             in
          let uu____6213 =
            let uu____6220 =
              let uu____6225 = type_of ea  in as_arg uu____6225  in
            [uu____6220]  in
          uu____6207 :: uu____6213  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____6206
         in
      mk_emb em un uu____6205 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____6299 =
          let uu____6307 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____6307, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____6299  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____6351  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____6353 =
                   let uu____6354 =
                     let uu____6359 = embed ea cb a  in as_arg uu____6359  in
                   let uu____6360 =
                     let uu____6367 =
                       let uu____6372 = type_of eb  in as_iarg uu____6372  in
                     let uu____6373 =
                       let uu____6380 =
                         let uu____6385 = type_of ea  in as_iarg uu____6385
                          in
                       [uu____6380]  in
                     uu____6367 :: uu____6373  in
                   uu____6354 :: uu____6360  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____6353
             | FStar_Util.Inr b ->
                 let uu____6403 =
                   let uu____6404 =
                     let uu____6409 = embed eb cb b  in as_arg uu____6409  in
                   let uu____6410 =
                     let uu____6417 =
                       let uu____6422 = type_of eb  in as_iarg uu____6422  in
                     let uu____6423 =
                       let uu____6430 =
                         let uu____6435 = type_of ea  in as_iarg uu____6435
                          in
                       [uu____6430]  in
                     uu____6417 :: uu____6423  in
                   uu____6404 :: uu____6410  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____6403)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____6509)::uu____6510::uu____6511::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____6552 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____6552
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____6568)::uu____6569::uu____6570::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____6611 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____6611
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____6624 -> FStar_Pervasives_Native.None)
         in
      let uu____6629 =
        let uu____6630 =
          let uu____6631 = let uu____6636 = type_of eb  in as_arg uu____6636
             in
          let uu____6637 =
            let uu____6644 =
              let uu____6649 = type_of ea  in as_arg uu____6649  in
            [uu____6644]  in
          uu____6631 :: uu____6637  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____6630
         in
      mk_emb em un uu____6629 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____6728 -> FStar_Pervasives_Native.None  in
  let uu____6729 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____6734 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____6729 uu____6734 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____6769 =
        let uu____6777 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____6777, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____6769  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____6816  ->
           let typ = let uu____6818 = type_of ea  in as_iarg uu____6818  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____6839 =
               let uu____6840 = as_arg tl1  in
               let uu____6845 =
                 let uu____6852 =
                   let uu____6857 = embed ea cb hd1  in as_arg uu____6857  in
                 [uu____6852; typ]  in
               uu____6840 :: uu____6845  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____6839
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____6917,uu____6918) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____6944,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____6947,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6948))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6982 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____6982
                 (fun hd2  ->
                    let uu____6990 = un cb tl1  in
                    FStar_Util.bind_opt uu____6990
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____7006,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____7037 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____7037
                 (fun hd2  ->
                    let uu____7045 = un cb tl1  in
                    FStar_Util.bind_opt uu____7045
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____7060 -> FStar_Pervasives_Native.None)
       in
    let uu____7063 =
      let uu____7064 =
        let uu____7065 = let uu____7070 = type_of ea  in as_arg uu____7070
           in
        [uu____7065]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____7064
       in
    mk_emb em un uu____7063 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____7179  ->
             Lam
               ((fun tas  ->
                   let uu____7216 =
                     let uu____7219 = FStar_List.hd tas  in
                     unembed ea cb uu____7219  in
                   match uu____7216 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____7221 = f a  in embed eb cb uu____7221
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____7234  ->
                     let uu____7237 = type_of eb  in as_arg uu____7237)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____7310 =
                 let uu____7313 =
                   let uu____7314 =
                     let uu____7315 =
                       let uu____7320 = embed ea cb x  in as_arg uu____7320
                        in
                     [uu____7315]  in
                   cb.iapp lam1 uu____7314  in
                 unembed eb cb uu____7313  in
               match uu____7310 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____7338 =
        let uu____7339 = type_of ea  in
        let uu____7340 = let uu____7341 = type_of eb  in as_iarg uu____7341
           in
        make_arrow1 uu____7339 uu____7340  in
      mk_emb em un uu____7338 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____7374 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____7374 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____7385 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____7385 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____7396 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____7396 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____7407 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____7407 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____7418 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____7418 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____7429 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____7429 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____7440 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____7440 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____7451 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____7451 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____7462 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____7462 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____7477 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____7484 =
          let uu____7485 =
            let uu____7490 =
              let uu____7491 = e_list e_string  in embed uu____7491 cb l  in
            as_arg uu____7490  in
          [uu____7485]  in
        mkFV uu____7477 [] uu____7484
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____7520 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____7527 =
          let uu____7528 =
            let uu____7533 =
              let uu____7534 = e_list e_string  in embed uu____7534 cb l  in
            as_arg uu____7533  in
          [uu____7528]  in
        mkFV uu____7520 [] uu____7527
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____7563 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____7570 =
          let uu____7571 =
            let uu____7576 =
              let uu____7577 = e_list e_string  in embed uu____7577 cb l  in
            as_arg uu____7576  in
          [uu____7571]  in
        mkFV uu____7563 [] uu____7570
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____7626,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____7648,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____7670,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____7692,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____7714,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____7736,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____7758,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____7780,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____7802,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____7824,(l,uu____7826)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____7851 =
          let uu____7857 = e_list e_string  in unembed uu____7857 cb l  in
        FStar_Util.bind_opt uu____7851
          (fun ss  ->
             FStar_All.pipe_left
               (fun _7884  -> FStar_Pervasives_Native.Some _7884)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____7886,(l,uu____7888)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____7913 =
          let uu____7919 = e_list e_string  in unembed uu____7919 cb l  in
        FStar_Util.bind_opt uu____7913
          (fun ss  ->
             FStar_All.pipe_left
               (fun _7946  -> FStar_Pervasives_Native.Some _7946)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____7948,(l,uu____7950)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____7975 =
          let uu____7981 = e_list e_string  in unembed uu____7981 cb l  in
        FStar_Util.bind_opt uu____7975
          (fun ss  ->
             FStar_All.pipe_left
               (fun _8008  -> FStar_Pervasives_Native.Some _8008)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____8009 ->
        ((let uu____8011 =
            let uu____8017 =
              let uu____8019 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____8019
               in
            (FStar_Errors.Warning_NotEmbedded, uu____8017)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____8011);
         FStar_Pervasives_Native.None)
     in
  let uu____8023 =
    let uu____8024 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____8024 [] []  in
  let uu____8035 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____8023 uu____8035 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____8052  -> failwith "bogus_cbs translate")
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
      let uu____8140 =
        let uu____8149 = e_list e  in unembed uu____8149 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____8140
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____8181  ->
    match uu____8181 with
    | (a,uu____8192) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____8213)::[]) when
             let uu____8236 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____8236 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____8253 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____8308 = let uu____8315 = as_arg c  in [uu____8315]  in
      int_to_t2 uu____8308
  
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
          let uu____8369 = f a  in FStar_Pervasives_Native.Some uu____8369
      | uu____8370 -> FStar_Pervasives_Native.None
  
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
          let uu____8424 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____8424
      | uu____8425 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____8469 = FStar_List.map as_a args  in lift_unary f uu____8469
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____8524 = FStar_List.map as_a args  in
        lift_binary f uu____8524
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____8554 = f x  in embed e_int bogus_cbs uu____8554)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____8581 = f x y  in embed e_int bogus_cbs uu____8581)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____8607 = f x  in embed e_bool bogus_cbs uu____8607)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____8645 = f x y  in embed e_bool bogus_cbs uu____8645)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____8683 = f x y  in embed e_string bogus_cbs uu____8683)
  
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
                let uu____8788 =
                  let uu____8797 = as_a a  in
                  let uu____8800 = as_b b  in (uu____8797, uu____8800)  in
                (match uu____8788 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____8815 =
                       let uu____8816 = f a1 b1  in embed_c uu____8816  in
                     FStar_Pervasives_Native.Some uu____8815
                 | uu____8817 -> FStar_Pervasives_Native.None)
            | uu____8826 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____8835 = e_list e_char  in
    let uu____8849 = FStar_String.list_of_string s  in
    embed uu____8835 bogus_cbs uu____8849
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____8888 =
        let uu____8889 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____8889  in
      embed e_int bogus_cbs uu____8888
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____8923 = arg_as_string a1  in
        (match uu____8923 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8932 = arg_as_list e_string a2  in
             (match uu____8932 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____8950 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____8950
              | uu____8952 -> FStar_Pervasives_Native.None)
         | uu____8958 -> FStar_Pervasives_Native.None)
    | uu____8962 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____8969 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____8969
  
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
      | (_typ,uu____9031)::(a1,uu____9033)::(a2,uu____9035)::[] ->
          let uu____9052 = eq_t a1 a2  in
          (match uu____9052 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____9061 -> FStar_Pervasives_Native.None)
      | uu____9062 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____9077)::(_typ,uu____9079)::(a1,uu____9081)::(a2,uu____9083)::[]
        ->
        let uu____9104 = eq_t a1 a2  in
        (match uu____9104 with
         | FStar_Syntax_Util.Equal  ->
             let uu____9107 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____9107
         | FStar_Syntax_Util.NotEqual  ->
             let uu____9110 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____9110
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____9113 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____9128)::(_v,uu____9130)::(t1,uu____9132)::(t2,uu____9134)::
        (a1,uu____9136)::(a2,uu____9138)::[] ->
        let uu____9167 =
          let uu____9168 = eq_t t1 t2  in
          let uu____9169 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____9168 uu____9169  in
        (match uu____9167 with
         | FStar_Syntax_Util.Equal  ->
             let uu____9172 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____9172
         | FStar_Syntax_Util.NotEqual  ->
             let uu____9175 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____9175
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____9178 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____9205 =
        let uu____9207 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____9207  in
      failwith uu____9205
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____9223)::[] ->
        let uu____9232 = unembed e_range bogus_cbs a1  in
        (match uu____9232 with
         | FStar_Pervasives_Native.Some r ->
             let uu____9238 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____9238
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____9239 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____9275 = arg_as_list e_char a1  in
        (match uu____9275 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____9291 = arg_as_string a2  in
             (match uu____9291 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____9304 =
                    let uu____9305 = e_list e_string  in
                    embed uu____9305 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____9304
              | uu____9322 -> FStar_Pervasives_Native.None)
         | uu____9326 -> FStar_Pervasives_Native.None)
    | uu____9332 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____9365 =
          let uu____9375 = arg_as_string a1  in
          let uu____9379 = arg_as_int a2  in (uu____9375, uu____9379)  in
        (match uu____9365 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___981_9403  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____9408 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____9408) ()
              with | uu___980_9411 -> FStar_Pervasives_Native.None)
         | uu____9414 -> FStar_Pervasives_Native.None)
    | uu____9424 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____9457 =
          let uu____9468 = arg_as_string a1  in
          let uu____9472 = arg_as_char a2  in (uu____9468, uu____9472)  in
        (match uu____9457 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___999_9501  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____9505 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____9505) ()
              with | uu___998_9507 -> FStar_Pervasives_Native.None)
         | uu____9510 -> FStar_Pervasives_Native.None)
    | uu____9521 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____9563 =
          let uu____9577 = arg_as_string a1  in
          let uu____9581 = arg_as_int a2  in
          let uu____9584 = arg_as_int a3  in
          (uu____9577, uu____9581, uu____9584)  in
        (match uu____9563 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1022_9617  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____9622 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____9622) ()
              with | uu___1021_9625 -> FStar_Pervasives_Native.None)
         | uu____9628 -> FStar_Pervasives_Native.None)
    | uu____9642 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____9702 =
          let uu____9724 = arg_as_string fn  in
          let uu____9728 = arg_as_int from_line  in
          let uu____9731 = arg_as_int from_col  in
          let uu____9734 = arg_as_int to_line  in
          let uu____9737 = arg_as_int to_col  in
          (uu____9724, uu____9728, uu____9731, uu____9734, uu____9737)  in
        (match uu____9702 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____9772 =
                 let uu____9773 = FStar_BigInt.to_int_fs from_l  in
                 let uu____9775 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____9773 uu____9775  in
               let uu____9777 =
                 let uu____9778 = FStar_BigInt.to_int_fs to_l  in
                 let uu____9780 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____9778 uu____9780  in
               FStar_Range.mk_range fn1 uu____9772 uu____9777  in
             let uu____9782 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____9782
         | uu____9783 -> FStar_Pervasives_Native.None)
    | uu____9805 -> FStar_Pervasives_Native.None
  
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
                let uu____9925 = FStar_List.splitAt n_tvars args  in
                match uu____9925 with
                | (_tvar_args,rest_args) ->
                    let uu____9974 = FStar_List.hd rest_args  in
                    (match uu____9974 with
                     | (x,uu____9986) ->
                         let uu____9987 = unembed ea cb x  in
                         FStar_Util.map_opt uu____9987
                           (fun x1  ->
                              let uu____9993 = f x1  in
                              embed eb cb uu____9993))
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
                  let uu____10139 = FStar_List.splitAt n_tvars args  in
                  match uu____10139 with
                  | (_tvar_args,rest_args) ->
                      let uu____10188 = FStar_List.hd rest_args  in
                      (match uu____10188 with
                       | (x,uu____10200) ->
                           let uu____10201 =
                             let uu____10206 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____10206  in
                           (match uu____10201 with
                            | (y,uu____10224) ->
                                let uu____10225 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____10225
                                  (fun x1  ->
                                     let uu____10231 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____10231
                                       (fun y1  ->
                                          let uu____10237 =
                                            let uu____10238 = f x1 y1  in
                                            embed ec cb uu____10238  in
                                          FStar_Pervasives_Native.Some
                                            uu____10237))))
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
                    let uu____10410 = FStar_List.splitAt n_tvars args  in
                    match uu____10410 with
                    | (_tvar_args,rest_args) ->
                        let uu____10459 = FStar_List.hd rest_args  in
                        (match uu____10459 with
                         | (x,uu____10471) ->
                             let uu____10472 =
                               let uu____10477 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____10477  in
                             (match uu____10472 with
                              | (y,uu____10495) ->
                                  let uu____10496 =
                                    let uu____10501 =
                                      let uu____10508 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____10508  in
                                    FStar_List.hd uu____10501  in
                                  (match uu____10496 with
                                   | (z,uu____10530) ->
                                       let uu____10531 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____10531
                                         (fun x1  ->
                                            let uu____10537 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____10537
                                              (fun y1  ->
                                                 let uu____10543 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____10543
                                                   (fun z1  ->
                                                      let uu____10549 =
                                                        let uu____10550 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____10550
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____10549))))))
                     in
                  f_wrapped
  