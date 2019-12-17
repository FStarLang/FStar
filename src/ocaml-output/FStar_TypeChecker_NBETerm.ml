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
  FStar_Util.either * t FStar_Thunk.t) 
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
    match projectee with | Var _0 -> true | uu____555 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____591 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____691 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____810 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____873 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____948 -> false 
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1009 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1028 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1047 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1065 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1097 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1190 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1251 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1274 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1319 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1416 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1549 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1592 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1629 -> false
  
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
    match projectee with | TOTAL  -> true | uu____1758 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1769 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1780 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1791 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1802 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____1813 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____1824 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1835 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____1846 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1858 -> false
  
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
  fun trm  -> match trm with | Accu uu____1934 -> true | uu____1946 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1956,uu____1957) -> false | uu____1971 -> true
  
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
  fun uu___0_2107  ->
    if uu___0_2107
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2118  ->
    if uu___1_2118
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
      | (FStar_Syntax_Util.NotEqual ,uu____2134) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2135,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2136) -> FStar_Syntax_Util.Unknown
      | (uu____2137,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2154 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2174),String (s2,uu____2176)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2189,uu____2190) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2226,Lam uu____2227) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2316 = eq_atom a1 a2  in
          eq_and uu____2316 (fun uu____2318  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2357 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2357
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2373 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2430  ->
                        match uu____2430 with
                        | ((a1,uu____2444),(a2,uu____2446)) ->
                            let uu____2455 = eq_t a1 a2  in
                            eq_inj acc uu____2455) FStar_Syntax_Util.Equal)
                uu____2373))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2496 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2496
          then
            let uu____2499 =
              let uu____2500 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2500  in
            eq_and uu____2499 (fun uu____2503  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2510 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2510
      | (Univ u1,Univ u2) ->
          let uu____2514 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2514
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2561 =
            let uu____2562 =
              let uu____2563 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2563  in
            let uu____2568 =
              let uu____2569 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2569  in
            eq_t uu____2562 uu____2568  in
          eq_and uu____2561
            (fun uu____2577  ->
               let uu____2578 =
                 let uu____2579 = mkAccuVar x  in r1 uu____2579  in
               let uu____2580 =
                 let uu____2581 = mkAccuVar x  in r2 uu____2581  in
               eq_t uu____2578 uu____2580)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2582,uu____2583) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2588,uu____2589) -> FStar_Syntax_Util.Unknown

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
          let uu____2670 = eq_arg x y  in
          eq_and uu____2670 (fun uu____2672  -> eq_args xs ys)
      | (uu____2673,uu____2674) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2721) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2726 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2726
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2745) ->
        let uu____2790 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2801 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2790 uu____2801
    | Accu (a,l) ->
        let uu____2818 =
          let uu____2820 = atom_to_string a  in
          let uu____2822 =
            let uu____2824 =
              let uu____2826 =
                let uu____2828 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2828  in
              FStar_String.op_Hat uu____2826 ")"  in
            FStar_String.op_Hat ") (" uu____2824  in
          FStar_String.op_Hat uu____2820 uu____2822  in
        FStar_String.op_Hat "Accu (" uu____2818
    | Construct (fv,us,l) ->
        let uu____2866 =
          let uu____2868 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2870 =
            let uu____2872 =
              let uu____2874 =
                let uu____2876 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2876  in
              let uu____2882 =
                let uu____2884 =
                  let uu____2886 =
                    let uu____2888 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2888  in
                  FStar_String.op_Hat uu____2886 "]"  in
                FStar_String.op_Hat "] [" uu____2884  in
              FStar_String.op_Hat uu____2874 uu____2882  in
            FStar_String.op_Hat ") [" uu____2872  in
          FStar_String.op_Hat uu____2868 uu____2870  in
        FStar_String.op_Hat "Construct (" uu____2866
    | FV (fv,us,l) ->
        let uu____2927 =
          let uu____2929 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2931 =
            let uu____2933 =
              let uu____2935 =
                let uu____2937 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2937  in
              let uu____2943 =
                let uu____2945 =
                  let uu____2947 =
                    let uu____2949 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2949  in
                  FStar_String.op_Hat uu____2947 "]"  in
                FStar_String.op_Hat "] [" uu____2945  in
              FStar_String.op_Hat uu____2935 uu____2943  in
            FStar_String.op_Hat ") [" uu____2933  in
          FStar_String.op_Hat uu____2929 uu____2931  in
        FStar_String.op_Hat "FV (" uu____2927
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2971 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____2971
    | Type_t u ->
        let uu____2975 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____2975
    | Arrow uu____2978 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3024 = t ()  in FStar_Pervasives_Native.fst uu____3024
           in
        let uu____3029 =
          let uu____3031 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3033 =
            let uu____3035 =
              let uu____3037 = t_to_string t1  in
              let uu____3039 =
                let uu____3041 =
                  let uu____3043 =
                    let uu____3045 =
                      let uu____3046 = mkAccuVar x1  in f uu____3046  in
                    t_to_string uu____3045  in
                  FStar_String.op_Hat uu____3043 "}"  in
                FStar_String.op_Hat "{" uu____3041  in
              FStar_String.op_Hat uu____3037 uu____3039  in
            FStar_String.op_Hat ":" uu____3035  in
          FStar_String.op_Hat uu____3031 uu____3033  in
        FStar_String.op_Hat "Refinement " uu____3029
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____3053 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____3053
    | Quote uu____3056 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3063) ->
        let uu____3080 =
          let uu____3082 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3082  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3080
    | Lazy (FStar_Util.Inr (uu____3084,et),uu____3086) ->
        let uu____3103 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3103
    | Rec
        (uu____3106,uu____3107,l,uu____3109,uu____3110,uu____3111,uu____3112)
        ->
        let uu____3157 =
          let uu____3159 =
            let uu____3161 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____3161  in
          FStar_String.op_Hat uu____3159 ")"  in
        FStar_String.op_Hat "Rec (" uu____3157

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3172 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3172
    | Match (t,uu____3176,uu____3177) ->
        let uu____3200 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3200

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3210 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3210 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3223 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3223 (FStar_String.concat " ")
  
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
        let uu____3694 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3694 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3715 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3715 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3756  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3771  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____3814 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____3814
         then
           let uu____3838 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3838
         else ());
        (let uu____3843 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____3843
         then f ()
         else
           (let thunk1 = FStar_Thunk.mk f  in
            let li = let uu____3877 = FStar_Dyn.mkdyn x  in (uu____3877, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____3905 'a .
    'Auu____3905 ->
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
              let uu____3956 = FStar_Thunk.force thunk1  in f uu____3956
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____3976 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____3976
              then
                let res =
                  let uu____4005 = FStar_Thunk.force thunk1  in f uu____4005
                   in
                ((let uu____4007 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4007
                  then
                    let uu____4031 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4033 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4031
                      uu____4033
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____4042 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4042
                  then
                    let uu____4066 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4066
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____4071 ->
              let aopt = f x  in
              ((let uu____4076 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4076
                then
                  let uu____4100 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4100
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
  let uu____4168 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4168 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____4202 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4207 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4202 uu____4207 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4248 -> FStar_Pervasives_Native.None  in
  let uu____4250 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____4255 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4250 uu____4255 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4297 -> FStar_Pervasives_Native.None  in
  let uu____4299 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____4304 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____4299 uu____4304 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____4346)) -> FStar_Pervasives_Native.Some s1
    | uu____4350 -> FStar_Pervasives_Native.None  in
  let uu____4352 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____4357 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____4352 uu____4357 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4392 -> FStar_Pervasives_Native.None  in
  let uu____4393 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4398 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4393 uu____4398 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4419 =
        let uu____4427 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4427, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4419  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4452  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4453 =
                 let uu____4454 =
                   let uu____4459 = type_of ea  in as_iarg uu____4459  in
                 [uu____4454]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4453
           | FStar_Pervasives_Native.Some x ->
               let uu____4469 =
                 let uu____4470 =
                   let uu____4475 = embed ea cb x  in as_arg uu____4475  in
                 let uu____4476 =
                   let uu____4483 =
                     let uu____4488 = type_of ea  in as_iarg uu____4488  in
                   [uu____4483]  in
                 uu____4470 :: uu____4476  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4469)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4555)::uu____4556::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4583 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4583
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4592 -> FStar_Pervasives_Native.None)
       in
    let uu____4595 =
      let uu____4596 =
        let uu____4597 = let uu____4602 = type_of ea  in as_arg uu____4602
           in
        [uu____4597]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4596
       in
    mk_emb em un uu____4595 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4649 =
          let uu____4657 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4657, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4649  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4688  ->
             let uu____4689 =
               let uu____4690 =
                 let uu____4695 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4695  in
               let uu____4696 =
                 let uu____4703 =
                   let uu____4708 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4708  in
                 let uu____4709 =
                   let uu____4716 =
                     let uu____4721 = type_of eb  in as_iarg uu____4721  in
                   let uu____4722 =
                     let uu____4729 =
                       let uu____4734 = type_of ea  in as_iarg uu____4734  in
                     [uu____4729]  in
                   uu____4716 :: uu____4722  in
                 uu____4703 :: uu____4709  in
               uu____4690 :: uu____4696  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4689)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____4802)::(a,uu____4804)::uu____4805::uu____4806::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____4845 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4845
                   (fun a1  ->
                      let uu____4855 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____4855
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____4868 -> FStar_Pervasives_Native.None)
         in
      let uu____4873 =
        let uu____4874 =
          let uu____4875 = let uu____4880 = type_of eb  in as_arg uu____4880
             in
          let uu____4881 =
            let uu____4888 =
              let uu____4893 = type_of ea  in as_arg uu____4893  in
            [uu____4888]  in
          uu____4875 :: uu____4881  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4874
         in
      mk_emb em un uu____4873 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4946 =
          let uu____4954 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4954, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4946  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____4986  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____4988 =
                   let uu____4989 =
                     let uu____4994 = embed ea cb a  in as_arg uu____4994  in
                   let uu____4995 =
                     let uu____5002 =
                       let uu____5007 = type_of eb  in as_iarg uu____5007  in
                     let uu____5008 =
                       let uu____5015 =
                         let uu____5020 = type_of ea  in as_iarg uu____5020
                          in
                       [uu____5015]  in
                     uu____5002 :: uu____5008  in
                   uu____4989 :: uu____4995  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____4988
             | FStar_Util.Inr b ->
                 let uu____5038 =
                   let uu____5039 =
                     let uu____5044 = embed eb cb b  in as_arg uu____5044  in
                   let uu____5045 =
                     let uu____5052 =
                       let uu____5057 = type_of eb  in as_iarg uu____5057  in
                     let uu____5058 =
                       let uu____5065 =
                         let uu____5070 = type_of ea  in as_iarg uu____5070
                          in
                       [uu____5065]  in
                     uu____5052 :: uu____5058  in
                   uu____5039 :: uu____5045  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5038)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____5132)::uu____5133::uu____5134::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5169 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5169
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____5185)::uu____5186::uu____5187::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5222 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____5222
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____5235 -> FStar_Pervasives_Native.None)
         in
      let uu____5240 =
        let uu____5241 =
          let uu____5242 = let uu____5247 = type_of eb  in as_arg uu____5247
             in
          let uu____5248 =
            let uu____5255 =
              let uu____5260 = type_of ea  in as_arg uu____5260  in
            [uu____5255]  in
          uu____5242 :: uu____5248  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5241
         in
      mk_emb em un uu____5240 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5309 -> FStar_Pervasives_Native.None  in
  let uu____5310 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5315 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5310 uu____5315 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5336 =
        let uu____5344 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5344, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5336  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5371  ->
           let typ = let uu____5373 = type_of ea  in as_iarg uu____5373  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5394 =
               let uu____5395 = as_arg tl1  in
               let uu____5400 =
                 let uu____5407 =
                   let uu____5412 = embed ea cb hd1  in as_arg uu____5412  in
                 [uu____5407; typ]  in
               uu____5395 :: uu____5400  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5394
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5460,uu____5461) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5481,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5484,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5485))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5513 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5513
                 (fun hd2  ->
                    let uu____5521 = un cb tl1  in
                    FStar_Util.bind_opt uu____5521
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5537,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5562 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5562
                 (fun hd2  ->
                    let uu____5570 = un cb tl1  in
                    FStar_Util.bind_opt uu____5570
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5585 -> FStar_Pervasives_Native.None)
       in
    let uu____5588 =
      let uu____5589 =
        let uu____5590 = let uu____5595 = type_of ea  in as_arg uu____5595
           in
        [uu____5590]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5589
       in
    mk_emb em un uu____5588 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5668  ->
             Lam
               ((fun tas  ->
                   let uu____5698 =
                     let uu____5701 = FStar_List.hd tas  in
                     unembed ea cb uu____5701  in
                   match uu____5698 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5703 = f a  in embed eb cb uu____5703
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____5716  ->
                     let uu____5719 = type_of eb  in as_arg uu____5719)],
                 Prims.int_one, FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____5777 =
                 let uu____5780 =
                   let uu____5781 =
                     let uu____5782 =
                       let uu____5787 = embed ea cb x  in as_arg uu____5787
                        in
                     [uu____5782]  in
                   cb.iapp lam1 uu____5781  in
                 unembed eb cb uu____5780  in
               match uu____5777 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____5801 =
        let uu____5802 = type_of ea  in
        let uu____5803 = let uu____5804 = type_of eb  in as_iarg uu____5804
           in
        make_arrow1 uu____5802 uu____5803  in
      mk_emb em un uu____5801 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5822 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5822 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5827 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5827 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5832 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5832 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5837 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5837 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5842 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5842 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5847 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5847 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5852 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5852 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5857 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5857 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5862 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5862 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5871 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5872 =
          let uu____5873 =
            let uu____5878 =
              let uu____5879 = e_list e_string  in embed uu____5879 cb l  in
            as_arg uu____5878  in
          [uu____5873]  in
        mkFV uu____5871 [] uu____5872
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5901 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5902 =
          let uu____5903 =
            let uu____5908 =
              let uu____5909 = e_list e_string  in embed uu____5909 cb l  in
            as_arg uu____5908  in
          [uu____5903]  in
        mkFV uu____5901 [] uu____5902
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____5931 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5932 =
          let uu____5933 =
            let uu____5938 =
              let uu____5939 = e_list e_string  in embed uu____5939 cb l  in
            as_arg uu____5938  in
          [uu____5933]  in
        mkFV uu____5931 [] uu____5932
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____5973,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____5989,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6005,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6021,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6037,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6053,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6069,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6085,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6101,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6117,(l,uu____6119)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6138 =
          let uu____6144 = e_list e_string  in unembed uu____6144 cb l  in
        FStar_Util.bind_opt uu____6138
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6164  -> FStar_Pervasives_Native.Some _6164)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6166,(l,uu____6168)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6187 =
          let uu____6193 = e_list e_string  in unembed uu____6193 cb l  in
        FStar_Util.bind_opt uu____6187
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6213  -> FStar_Pervasives_Native.Some _6213)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____6215,(l,uu____6217)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6236 =
          let uu____6242 = e_list e_string  in unembed uu____6242 cb l  in
        FStar_Util.bind_opt uu____6236
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6262  -> FStar_Pervasives_Native.Some _6262)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6263 ->
        ((let uu____6265 =
            let uu____6271 =
              let uu____6273 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6273
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6271)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6265);
         FStar_Pervasives_Native.None)
     in
  let uu____6277 =
    let uu____6278 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6278 [] []  in
  let uu____6283 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6277 uu____6283 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____6292  -> failwith "bogus_cbs translate")
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
      let uu____6369 =
        let uu____6378 = e_list e  in unembed uu____6378 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6369
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6400  ->
    match uu____6400 with
    | (a,uu____6408) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6423)::[]) when
             let uu____6440 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6440 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6447 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6490 = let uu____6497 = as_arg c  in [uu____6497]  in
      int_to_t2 uu____6490
  
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
          let uu____6551 = f a  in FStar_Pervasives_Native.Some uu____6551
      | uu____6552 -> FStar_Pervasives_Native.None
  
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
          let uu____6606 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6606
      | uu____6607 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6651 = FStar_List.map as_a args  in lift_unary f uu____6651
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6706 = FStar_List.map as_a args  in
        lift_binary f uu____6706
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6736 = f x  in embed e_int bogus_cbs uu____6736)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____6763 = f x y  in embed e_int bogus_cbs uu____6763)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6789 = f x  in embed e_bool bogus_cbs uu____6789)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6827 = f x y  in embed e_bool bogus_cbs uu____6827)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____6865 = f x y  in embed e_string bogus_cbs uu____6865)
  
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
                let uu____6970 =
                  let uu____6979 = as_a a  in
                  let uu____6982 = as_b b  in (uu____6979, uu____6982)  in
                (match uu____6970 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____6997 =
                       let uu____6998 = f a1 b1  in embed_c uu____6998  in
                     FStar_Pervasives_Native.Some uu____6997
                 | uu____6999 -> FStar_Pervasives_Native.None)
            | uu____7008 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7017 = e_list e_char  in
    let uu____7024 = FStar_String.list_of_string s  in
    embed uu____7017 bogus_cbs uu____7024
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7063 =
        let uu____7064 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7064  in
      embed e_int bogus_cbs uu____7063
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7098 = arg_as_string a1  in
        (match uu____7098 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7107 = arg_as_list e_string a2  in
             (match uu____7107 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7125 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7125
              | uu____7127 -> FStar_Pervasives_Native.None)
         | uu____7133 -> FStar_Pervasives_Native.None)
    | uu____7137 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7144 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7144
  
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
      | (_typ,uu____7206)::(a1,uu____7208)::(a2,uu____7210)::[] ->
          let uu____7227 = eq_t a1 a2  in
          (match uu____7227 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7236 -> FStar_Pervasives_Native.None)
      | uu____7237 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7252)::(_typ,uu____7254)::(a1,uu____7256)::(a2,uu____7258)::[]
        ->
        let uu____7279 = eq_t a1 a2  in
        (match uu____7279 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7282 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7282
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7285 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7285
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7288 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7303)::(_v,uu____7305)::(t1,uu____7307)::(t2,uu____7309)::
        (a1,uu____7311)::(a2,uu____7313)::[] ->
        let uu____7342 =
          let uu____7343 = eq_t t1 t2  in
          let uu____7344 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____7343 uu____7344  in
        (match uu____7342 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7347 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7347
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7350 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7350
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7353 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____7372 =
        let uu____7374 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____7374  in
      failwith uu____7372
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____7390)::[] ->
        let uu____7399 = unembed e_range bogus_cbs a1  in
        (match uu____7399 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7405 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7405
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7406 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7442 = arg_as_list e_char a1  in
        (match uu____7442 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7458 = arg_as_string a2  in
             (match uu____7458 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____7471 =
                    let uu____7472 = e_list e_string  in
                    embed uu____7472 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7471
              | uu____7482 -> FStar_Pervasives_Native.None)
         | uu____7486 -> FStar_Pervasives_Native.None)
    | uu____7492 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7525 =
          let uu____7535 = arg_as_string a1  in
          let uu____7539 = arg_as_int a2  in (uu____7535, uu____7539)  in
        (match uu____7525 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___981_7563  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____7568 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7568) ()
              with | uu___980_7571 -> FStar_Pervasives_Native.None)
         | uu____7574 -> FStar_Pervasives_Native.None)
    | uu____7584 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7617 =
          let uu____7628 = arg_as_string a1  in
          let uu____7632 = arg_as_char a2  in (uu____7628, uu____7632)  in
        (match uu____7617 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___999_7661  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____7665 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7665) ()
              with | uu___998_7667 -> FStar_Pervasives_Native.None)
         | uu____7670 -> FStar_Pervasives_Native.None)
    | uu____7681 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____7723 =
          let uu____7737 = arg_as_string a1  in
          let uu____7741 = arg_as_int a2  in
          let uu____7744 = arg_as_int a3  in
          (uu____7737, uu____7741, uu____7744)  in
        (match uu____7723 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1022_7777  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____7782 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7782) ()
              with | uu___1021_7785 -> FStar_Pervasives_Native.None)
         | uu____7788 -> FStar_Pervasives_Native.None)
    | uu____7802 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7862 =
          let uu____7884 = arg_as_string fn  in
          let uu____7888 = arg_as_int from_line  in
          let uu____7891 = arg_as_int from_col  in
          let uu____7894 = arg_as_int to_line  in
          let uu____7897 = arg_as_int to_col  in
          (uu____7884, uu____7888, uu____7891, uu____7894, uu____7897)  in
        (match uu____7862 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7932 =
                 let uu____7933 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7935 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7933 uu____7935  in
               let uu____7937 =
                 let uu____7938 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7940 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7938 uu____7940  in
               FStar_Range.mk_range fn1 uu____7932 uu____7937  in
             let uu____7942 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7942
         | uu____7943 -> FStar_Pervasives_Native.None)
    | uu____7965 -> FStar_Pervasives_Native.None
  
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
                let uu____8055 = FStar_List.splitAt n_tvars args  in
                match uu____8055 with
                | (_tvar_args,rest_args) ->
                    let uu____8104 = FStar_List.hd rest_args  in
                    (match uu____8104 with
                     | (x,uu____8116) ->
                         let uu____8117 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8117
                           (fun x1  ->
                              let uu____8123 = f x1  in
                              embed eb cb uu____8123))
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
                  let uu____8232 = FStar_List.splitAt n_tvars args  in
                  match uu____8232 with
                  | (_tvar_args,rest_args) ->
                      let uu____8281 = FStar_List.hd rest_args  in
                      (match uu____8281 with
                       | (x,uu____8293) ->
                           let uu____8294 =
                             let uu____8299 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8299  in
                           (match uu____8294 with
                            | (y,uu____8317) ->
                                let uu____8318 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____8318
                                  (fun x1  ->
                                     let uu____8324 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____8324
                                       (fun y1  ->
                                          let uu____8330 =
                                            let uu____8331 = f x1 y1  in
                                            embed ec cb uu____8331  in
                                          FStar_Pervasives_Native.Some
                                            uu____8330))))
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
                    let uu____8459 = FStar_List.splitAt n_tvars args  in
                    match uu____8459 with
                    | (_tvar_args,rest_args) ->
                        let uu____8508 = FStar_List.hd rest_args  in
                        (match uu____8508 with
                         | (x,uu____8520) ->
                             let uu____8521 =
                               let uu____8526 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____8526  in
                             (match uu____8521 with
                              | (y,uu____8544) ->
                                  let uu____8545 =
                                    let uu____8550 =
                                      let uu____8557 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____8557  in
                                    FStar_List.hd uu____8550  in
                                  (match uu____8545 with
                                   | (z,uu____8579) ->
                                       let uu____8580 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____8580
                                         (fun x1  ->
                                            let uu____8586 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____8586
                                              (fun y1  ->
                                                 let uu____8592 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____8592
                                                   (fun z1  ->
                                                      let uu____8598 =
                                                        let uu____8599 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____8599
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____8598))))))
                     in
                  f_wrapped
  