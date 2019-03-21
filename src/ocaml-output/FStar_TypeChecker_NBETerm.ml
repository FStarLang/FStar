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
    match projectee with | Unit  -> true | uu____55931 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____55944 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____55966 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____55990 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____56025 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____56047 -> false
  
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
    match projectee with | Var _0 -> true | uu____56429 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____56465 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____56565 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____56684 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____56747 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____56822 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____56883 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____56902 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____56921 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____56939 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____56971 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____57064 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____57125 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____57148 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____57193 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____57290 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____57423 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____57466 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____57503 -> false
  
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
    match projectee with | TOTAL  -> true | uu____57632 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____57643 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____57654 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____57665 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____57676 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____57687 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____57698 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____57709 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____57720 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____57732 -> false
  
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
    match trm with | Accu uu____57808 -> true | uu____57820 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____57830,uu____57831) -> false
    | uu____57845 -> true
  
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
  fun uu___516_57981  ->
    if uu___516_57981
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_57992  ->
    if uu___517_57992
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
      | (FStar_Syntax_Util.NotEqual ,uu____58008) ->
          FStar_Syntax_Util.NotEqual
      | (uu____58009,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____58010) -> FStar_Syntax_Util.Unknown
      | (uu____58011,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____58028 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____58048),String (s2,uu____58050)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____58063,uu____58064) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____58100,Lam uu____58101) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____58190 = eq_atom a1 a2  in
          eq_and uu____58190 (fun uu____58192  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____58231 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58231
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____58247 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____58304  ->
                        match uu____58304 with
                        | ((a1,uu____58318),(a2,uu____58320)) ->
                            let uu____58329 = eq_t a1 a2  in
                            eq_inj acc uu____58329) FStar_Syntax_Util.Equal)
                uu____58247))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____58370 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58370
          then
            let uu____58373 =
              let uu____58374 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____58374  in
            eq_and uu____58373 (fun uu____58377  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____58384 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58384
      | (Univ u1,Univ u2) ->
          let uu____58388 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58388
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____58435 =
            let uu____58436 =
              let uu____58437 = t11 ()  in
              FStar_Pervasives_Native.fst uu____58437  in
            let uu____58442 =
              let uu____58443 = t21 ()  in
              FStar_Pervasives_Native.fst uu____58443  in
            eq_t uu____58436 uu____58442  in
          eq_and uu____58435
            (fun uu____58451  ->
               let uu____58452 =
                 let uu____58453 = mkAccuVar x  in r1 uu____58453  in
               let uu____58454 =
                 let uu____58455 = mkAccuVar x  in r2 uu____58455  in
               eq_t uu____58452 uu____58454)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____58456,uu____58457) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____58462,uu____58463) -> FStar_Syntax_Util.Unknown

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
          let uu____58544 = eq_arg x y  in
          eq_and uu____58544 (fun uu____58546  -> eq_args xs ys)
      | (uu____58547,uu____58548) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____58595) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____58600 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____58600
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____58629) ->
        let uu____58674 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____58685 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____58674 uu____58685
    | Accu (a,l) ->
        let uu____58702 =
          let uu____58704 = atom_to_string a  in
          let uu____58706 =
            let uu____58708 =
              let uu____58710 =
                let uu____58712 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____58712  in
              FStar_String.op_Hat uu____58710 ")"  in
            FStar_String.op_Hat ") (" uu____58708  in
          FStar_String.op_Hat uu____58704 uu____58706  in
        FStar_String.op_Hat "Accu (" uu____58702
    | Construct (fv,us,l) ->
        let uu____58750 =
          let uu____58752 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58754 =
            let uu____58756 =
              let uu____58758 =
                let uu____58760 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58760  in
              let uu____58766 =
                let uu____58768 =
                  let uu____58770 =
                    let uu____58772 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58772  in
                  FStar_String.op_Hat uu____58770 "]"  in
                FStar_String.op_Hat "] [" uu____58768  in
              FStar_String.op_Hat uu____58758 uu____58766  in
            FStar_String.op_Hat ") [" uu____58756  in
          FStar_String.op_Hat uu____58752 uu____58754  in
        FStar_String.op_Hat "Construct (" uu____58750
    | FV (fv,us,l) ->
        let uu____58811 =
          let uu____58813 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58815 =
            let uu____58817 =
              let uu____58819 =
                let uu____58821 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58821  in
              let uu____58827 =
                let uu____58829 =
                  let uu____58831 =
                    let uu____58833 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58833  in
                  FStar_String.op_Hat uu____58831 "]"  in
                FStar_String.op_Hat "] [" uu____58829  in
              FStar_String.op_Hat uu____58819 uu____58827  in
            FStar_String.op_Hat ") [" uu____58817  in
          FStar_String.op_Hat uu____58813 uu____58815  in
        FStar_String.op_Hat "FV (" uu____58811
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____58855 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____58855
    | Type_t u ->
        let uu____58859 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____58859
    | Arrow uu____58862 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____58908 = t ()  in FStar_Pervasives_Native.fst uu____58908
           in
        let uu____58913 =
          let uu____58915 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____58917 =
            let uu____58919 =
              let uu____58921 = t_to_string t1  in
              let uu____58923 =
                let uu____58925 =
                  let uu____58927 =
                    let uu____58929 =
                      let uu____58930 = mkAccuVar x1  in f uu____58930  in
                    t_to_string uu____58929  in
                  FStar_String.op_Hat uu____58927 "}"  in
                FStar_String.op_Hat "{" uu____58925  in
              FStar_String.op_Hat uu____58921 uu____58923  in
            FStar_String.op_Hat ":" uu____58919  in
          FStar_String.op_Hat uu____58915 uu____58917  in
        FStar_String.op_Hat "Refinement " uu____58913
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____58937 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____58937
    | Quote uu____58940 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____58947) ->
        let uu____58964 =
          let uu____58966 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____58966  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____58964
    | Lazy (FStar_Util.Inr (uu____58968,et),uu____58970) ->
        let uu____58987 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____58987
    | Rec
        (uu____58990,uu____58991,l,uu____58993,uu____58994,uu____58995,uu____58996)
        ->
        let uu____59041 =
          let uu____59043 =
            let uu____59045 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____59045  in
          FStar_String.op_Hat uu____59043 ")"  in
        FStar_String.op_Hat "Rec (" uu____59041

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____59056 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____59056
    | Match (t,uu____59060,uu____59061) ->
        let uu____59084 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____59084

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____59088 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____59088 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____59095 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59095 (FStar_String.concat " ")

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
        let uu____59566 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____59566 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____59587 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____59587 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____59628  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____59643  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____59686 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____59686
         then
           let uu____59710 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____59710
         else ());
        (let uu____59715 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____59715
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____59749 = FStar_Dyn.mkdyn x  in (uu____59749, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____59777 'a .
    'Auu____59777 ->
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
              let uu____59828 = FStar_Common.force_thunk thunk1  in
              f uu____59828
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____59848 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____59848
              then
                let res =
                  let uu____59877 = FStar_Common.force_thunk thunk1  in
                  f uu____59877  in
                ((let uu____59879 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59879
                  then
                    let uu____59903 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____59905 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____59903
                      uu____59905
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____59914 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59914
                  then
                    let uu____59938 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____59938
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____59943 ->
              let aopt = f x  in
              ((let uu____59948 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____59948
                then
                  let uu____59972 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____59972
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
  let uu____60040 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____60040 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____60074 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____60079 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60074 uu____60079 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____60120 -> FStar_Pervasives_Native.None  in
  let uu____60122 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____60127 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60122 uu____60127 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____60169 -> FStar_Pervasives_Native.None  in
  let uu____60171 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____60176 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____60171 uu____60176 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____60218)) -> FStar_Pervasives_Native.Some s1
    | uu____60222 -> FStar_Pervasives_Native.None  in
  let uu____60224 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____60229 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____60224 uu____60229 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____60264 -> FStar_Pervasives_Native.None  in
  let uu____60265 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____60270 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____60265 uu____60270 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____60291 =
        let uu____60299 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____60299, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____60291  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____60324  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____60325 =
                 let uu____60326 =
                   let uu____60331 = type_of ea  in as_iarg uu____60331  in
                 [uu____60326]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60325
           | FStar_Pervasives_Native.Some x ->
               let uu____60341 =
                 let uu____60342 =
                   let uu____60347 = embed ea cb x  in as_arg uu____60347  in
                 let uu____60348 =
                   let uu____60355 =
                     let uu____60360 = type_of ea  in as_iarg uu____60360  in
                   [uu____60355]  in
                 uu____60342 :: uu____60348  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60341)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____60427)::uu____60428::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____60455 = unembed ea cb a  in
               FStar_Util.bind_opt uu____60455
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____60464 -> FStar_Pervasives_Native.None)
       in
    let uu____60467 =
      let uu____60468 =
        let uu____60469 = let uu____60474 = type_of ea  in as_arg uu____60474
           in
        [uu____60469]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____60468
       in
    mk_emb em un uu____60467 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60521 =
          let uu____60529 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____60529, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60521  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____60560  ->
             let uu____60561 =
               let uu____60562 =
                 let uu____60567 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____60567  in
               let uu____60568 =
                 let uu____60575 =
                   let uu____60580 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____60580  in
                 let uu____60581 =
                   let uu____60588 =
                     let uu____60593 = type_of eb  in as_iarg uu____60593  in
                   let uu____60594 =
                     let uu____60601 =
                       let uu____60606 = type_of ea  in as_iarg uu____60606
                        in
                     [uu____60601]  in
                   uu____60588 :: uu____60594  in
                 uu____60575 :: uu____60581  in
               uu____60562 :: uu____60568  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____60561)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____60674)::(a,uu____60676)::uu____60677::uu____60678::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____60717 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____60717
                   (fun a1  ->
                      let uu____60727 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____60727
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____60740 -> FStar_Pervasives_Native.None)
         in
      let uu____60745 =
        let uu____60746 =
          let uu____60747 =
            let uu____60752 = type_of eb  in as_arg uu____60752  in
          let uu____60753 =
            let uu____60760 =
              let uu____60765 = type_of ea  in as_arg uu____60765  in
            [uu____60760]  in
          uu____60747 :: uu____60753  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____60746
         in
      mk_emb em un uu____60745 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60818 =
          let uu____60826 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60826, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60818  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____60858  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____60860 =
                   let uu____60861 =
                     let uu____60866 = embed ea cb a  in as_arg uu____60866
                      in
                   let uu____60867 =
                     let uu____60874 =
                       let uu____60879 = type_of eb  in as_iarg uu____60879
                        in
                     let uu____60880 =
                       let uu____60887 =
                         let uu____60892 = type_of ea  in as_iarg uu____60892
                          in
                       [uu____60887]  in
                     uu____60874 :: uu____60880  in
                   uu____60861 :: uu____60867  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60860
             | FStar_Util.Inr b ->
                 let uu____60910 =
                   let uu____60911 =
                     let uu____60916 = embed eb cb b  in as_arg uu____60916
                      in
                   let uu____60917 =
                     let uu____60924 =
                       let uu____60929 = type_of eb  in as_iarg uu____60929
                        in
                     let uu____60930 =
                       let uu____60937 =
                         let uu____60942 = type_of ea  in as_iarg uu____60942
                          in
                       [uu____60937]  in
                     uu____60924 :: uu____60930  in
                   uu____60911 :: uu____60917  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60910)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____61004)::uu____61005::uu____61006::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____61041 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____61041
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____61057)::uu____61058::uu____61059::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____61094 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____61094
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____61107 -> FStar_Pervasives_Native.None)
         in
      let uu____61112 =
        let uu____61113 =
          let uu____61114 =
            let uu____61119 = type_of eb  in as_arg uu____61119  in
          let uu____61120 =
            let uu____61127 =
              let uu____61132 = type_of ea  in as_arg uu____61132  in
            [uu____61127]  in
          uu____61114 :: uu____61120  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____61113
         in
      mk_emb em un uu____61112 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____61181 -> FStar_Pervasives_Native.None  in
  let uu____61182 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____61187 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____61182 uu____61187 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____61208 =
        let uu____61216 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61216, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61208  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____61243  ->
           let typ = let uu____61245 = type_of ea  in as_iarg uu____61245  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____61266 =
               let uu____61267 = as_arg tl1  in
               let uu____61272 =
                 let uu____61279 =
                   let uu____61284 = embed ea cb hd1  in as_arg uu____61284
                    in
                 [uu____61279; typ]  in
               uu____61267 :: uu____61272  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____61266
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____61332,uu____61333) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____61353,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____61356,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____61357))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61385 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61385
                 (fun hd2  ->
                    let uu____61393 = un cb tl1  in
                    FStar_Util.bind_opt uu____61393
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____61409,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61434 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61434
                 (fun hd2  ->
                    let uu____61442 = un cb tl1  in
                    FStar_Util.bind_opt uu____61442
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____61457 -> FStar_Pervasives_Native.None)
       in
    let uu____61460 =
      let uu____61461 =
        let uu____61462 = let uu____61467 = type_of ea  in as_arg uu____61467
           in
        [uu____61462]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____61461
       in
    mk_emb em un uu____61460 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____61540  ->
             Lam
               ((fun tas  ->
                   let uu____61570 =
                     let uu____61573 = FStar_List.hd tas  in
                     unembed ea cb uu____61573  in
                   match uu____61570 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____61575 = f a  in embed eb cb uu____61575
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____61588  ->
                     let uu____61591 = type_of eb  in as_arg uu____61591)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____61649 =
                 let uu____61652 =
                   let uu____61653 =
                     let uu____61654 =
                       let uu____61659 = embed ea cb x  in as_arg uu____61659
                        in
                     [uu____61654]  in
                   cb.iapp lam1 uu____61653  in
                 unembed eb cb uu____61652  in
               match uu____61649 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____61673 =
        let uu____61674 = type_of ea  in
        let uu____61675 =
          let uu____61676 = type_of eb  in as_iarg uu____61676  in
        make_arrow1 uu____61674 uu____61675  in
      mk_emb em un uu____61673 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____61694 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61694 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____61699 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61699 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____61704 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61704 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____61709 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61709 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____61714 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61714 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____61719 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61719 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____61724 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61724 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____61729 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61729 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____61734 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61734 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____61743 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61744 =
          let uu____61745 =
            let uu____61750 =
              let uu____61751 = e_list e_string  in embed uu____61751 cb l
               in
            as_arg uu____61750  in
          [uu____61745]  in
        mkFV uu____61743 [] uu____61744
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____61773 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61774 =
          let uu____61775 =
            let uu____61780 =
              let uu____61781 = e_list e_string  in embed uu____61781 cb l
               in
            as_arg uu____61780  in
          [uu____61775]  in
        mkFV uu____61773 [] uu____61774
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____61803 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61804 =
          let uu____61805 =
            let uu____61810 =
              let uu____61811 = e_list e_string  in embed uu____61811 cb l
               in
            as_arg uu____61810  in
          [uu____61805]  in
        mkFV uu____61803 [] uu____61804
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____61845,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____61861,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____61877,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____61893,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____61909,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____61925,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____61941,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____61957,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____61973,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____61989,(l,uu____61991)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____62010 =
          let uu____62016 = e_list e_string  in unembed uu____62016 cb l  in
        FStar_Util.bind_opt uu____62010
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62036  -> FStar_Pervasives_Native.Some _62036)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____62038,(l,uu____62040)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____62059 =
          let uu____62065 = e_list e_string  in unembed uu____62065 cb l  in
        FStar_Util.bind_opt uu____62059
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62085  -> FStar_Pervasives_Native.Some _62085)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____62087,(l,uu____62089)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____62108 =
          let uu____62114 = e_list e_string  in unembed uu____62114 cb l  in
        FStar_Util.bind_opt uu____62108
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62134  -> FStar_Pervasives_Native.Some _62134)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____62135 ->
        ((let uu____62137 =
            let uu____62143 =
              let uu____62145 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____62145
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62143)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62137);
         FStar_Pervasives_Native.None)
     in
  let uu____62149 =
    let uu____62150 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____62150 [] []  in
  let uu____62155 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____62149 uu____62155 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____62164  -> failwith "bogus_cbs translate")
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
      let uu____62241 =
        let uu____62250 = e_list e  in unembed uu____62250 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62241
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____62272  ->
    match uu____62272 with
    | (a,uu____62280) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____62295)::[]) when
             let uu____62312 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____62312 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____62319 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____62362 = let uu____62369 = as_arg c  in [uu____62369]  in
      int_to_t2 uu____62362
  
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
          let uu____62423 = f a  in FStar_Pervasives_Native.Some uu____62423
      | uu____62424 -> FStar_Pervasives_Native.None
  
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
          let uu____62478 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____62478
      | uu____62479 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62523 = FStar_List.map as_a args  in
        lift_unary f uu____62523
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62578 = FStar_List.map as_a args  in
        lift_binary f uu____62578
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____62608 = f x  in embed e_int bogus_cbs uu____62608)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____62635 = f x y  in embed e_int bogus_cbs uu____62635)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____62661 = f x  in embed e_bool bogus_cbs uu____62661)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____62699 = f x y  in embed e_bool bogus_cbs uu____62699)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____62737 = f x y  in embed e_string bogus_cbs uu____62737)
  
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
                let uu____62842 =
                  let uu____62851 = as_a a  in
                  let uu____62854 = as_b b  in (uu____62851, uu____62854)  in
                (match uu____62842 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____62869 =
                       let uu____62870 = f a1 b1  in embed_c uu____62870  in
                     FStar_Pervasives_Native.Some uu____62869
                 | uu____62871 -> FStar_Pervasives_Native.None)
            | uu____62880 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____62889 = e_list e_char  in
    let uu____62896 = FStar_String.list_of_string s  in
    embed uu____62889 bogus_cbs uu____62896
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____62935 =
        let uu____62936 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____62936  in
      embed e_int bogus_cbs uu____62935
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____62970 = arg_as_string a1  in
        (match uu____62970 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____62979 = arg_as_list e_string a2  in
             (match uu____62979 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____62997 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____62997
              | uu____62999 -> FStar_Pervasives_Native.None)
         | uu____63005 -> FStar_Pervasives_Native.None)
    | uu____63009 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____63016 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____63016
  
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
      | (_typ,uu____63078)::(a1,uu____63080)::(a2,uu____63082)::[] ->
          let uu____63099 = eq_t a1 a2  in
          (match uu____63099 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____63108 -> FStar_Pervasives_Native.None)
      | uu____63109 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63124)::(_typ,uu____63126)::(a1,uu____63128)::(a2,uu____63130)::[]
        ->
        let uu____63151 = eq_t a1 a2  in
        (match uu____63151 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63154 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63154
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63157 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63157
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63160 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63175)::(_v,uu____63177)::(t1,uu____63179)::(t2,uu____63181)::
        (a1,uu____63183)::(a2,uu____63185)::[] ->
        let uu____63214 =
          let uu____63215 = eq_t t1 t2  in
          let uu____63216 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____63215 uu____63216  in
        (match uu____63214 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63219 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63219
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63222 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63222
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63225 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____63244 =
        let uu____63246 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____63246  in
      failwith uu____63244
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____63262)::[] ->
        let uu____63271 = unembed e_range bogus_cbs a1  in
        (match uu____63271 with
         | FStar_Pervasives_Native.Some r ->
             let uu____63277 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63277
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____63278 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63314 = arg_as_list e_char a1  in
        (match uu____63314 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63330 = arg_as_string a2  in
             (match uu____63330 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63343 =
                    let uu____63344 = e_list e_string  in
                    embed uu____63344 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____63343
              | uu____63354 -> FStar_Pervasives_Native.None)
         | uu____63358 -> FStar_Pervasives_Native.None)
    | uu____63364 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63397 =
          let uu____63407 = arg_as_string a1  in
          let uu____63411 = arg_as_int a2  in (uu____63407, uu____63411)  in
        (match uu____63397 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_63435  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63440 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63440) ()
              with | uu___1496_63443 -> FStar_Pervasives_Native.None)
         | uu____63446 -> FStar_Pervasives_Native.None)
    | uu____63456 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63489 =
          let uu____63500 = arg_as_string a1  in
          let uu____63504 = arg_as_char a2  in (uu____63500, uu____63504)  in
        (match uu____63489 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_63533  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63537 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63537) ()
              with | uu___1514_63539 -> FStar_Pervasives_Native.None)
         | uu____63542 -> FStar_Pervasives_Native.None)
    | uu____63553 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____63595 =
          let uu____63609 = arg_as_string a1  in
          let uu____63613 = arg_as_int a2  in
          let uu____63616 = arg_as_int a3  in
          (uu____63609, uu____63613, uu____63616)  in
        (match uu____63595 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_63649  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63654 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63654) ()
              with | uu___1537_63657 -> FStar_Pervasives_Native.None)
         | uu____63660 -> FStar_Pervasives_Native.None)
    | uu____63674 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63734 =
          let uu____63756 = arg_as_string fn  in
          let uu____63760 = arg_as_int from_line  in
          let uu____63763 = arg_as_int from_col  in
          let uu____63766 = arg_as_int to_line  in
          let uu____63769 = arg_as_int to_col  in
          (uu____63756, uu____63760, uu____63763, uu____63766, uu____63769)
           in
        (match uu____63734 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____63804 =
                 let uu____63805 = FStar_BigInt.to_int_fs from_l  in
                 let uu____63807 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____63805 uu____63807  in
               let uu____63809 =
                 let uu____63810 = FStar_BigInt.to_int_fs to_l  in
                 let uu____63812 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____63810 uu____63812  in
               FStar_Range.mk_range fn1 uu____63804 uu____63809  in
             let uu____63814 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63814
         | uu____63815 -> FStar_Pervasives_Native.None)
    | uu____63837 -> FStar_Pervasives_Native.None
  
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
                let uu____63927 = FStar_List.splitAt n_tvars args  in
                match uu____63927 with
                | (_tvar_args,rest_args) ->
                    let uu____63976 = FStar_List.hd rest_args  in
                    (match uu____63976 with
                     | (x,uu____63988) ->
                         let uu____63989 = unembed ea cb x  in
                         FStar_Util.map_opt uu____63989
                           (fun x1  ->
                              let uu____63995 = f x1  in
                              embed eb cb uu____63995))
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
                  let uu____64104 = FStar_List.splitAt n_tvars args  in
                  match uu____64104 with
                  | (_tvar_args,rest_args) ->
                      let uu____64153 = FStar_List.hd rest_args  in
                      (match uu____64153 with
                       | (x,uu____64165) ->
                           let uu____64166 =
                             let uu____64171 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64171  in
                           (match uu____64166 with
                            | (y,uu____64189) ->
                                let uu____64190 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____64190
                                  (fun x1  ->
                                     let uu____64196 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____64196
                                       (fun y1  ->
                                          let uu____64202 =
                                            let uu____64203 = f x1 y1  in
                                            embed ec cb uu____64203  in
                                          FStar_Pervasives_Native.Some
                                            uu____64202))))
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
                    let uu____64331 = FStar_List.splitAt n_tvars args  in
                    match uu____64331 with
                    | (_tvar_args,rest_args) ->
                        let uu____64380 = FStar_List.hd rest_args  in
                        (match uu____64380 with
                         | (x,uu____64392) ->
                             let uu____64393 =
                               let uu____64398 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64398  in
                             (match uu____64393 with
                              | (y,uu____64416) ->
                                  let uu____64417 =
                                    let uu____64422 =
                                      let uu____64429 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64429  in
                                    FStar_List.hd uu____64422  in
                                  (match uu____64417 with
                                   | (z,uu____64451) ->
                                       let uu____64452 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____64452
                                         (fun x1  ->
                                            let uu____64458 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____64458
                                              (fun y1  ->
                                                 let uu____64464 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____64464
                                                   (fun z1  ->
                                                      let uu____64470 =
                                                        let uu____64471 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____64471
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____64470))))))
                     in
                  f_wrapped
  