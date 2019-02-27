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
    match projectee with | Unit  -> true | uu____60652 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____60665 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____60688 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____60713 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____60749 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____60772 -> false
  
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
    match projectee with | Var _0 -> true | uu____61155 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____61192 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____61293 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____61413 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____61477 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____61553 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____61615 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____61635 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____61655 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____61674 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____61706 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____61800 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____61862 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____61886 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____61932 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____62030 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____62164 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____62208 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____62246 -> false
  
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
    match projectee with | TOTAL  -> true | uu____62376 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____62387 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____62398 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____62409 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____62420 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____62431 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____62442 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____62453 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____62464 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____62476 -> false
  
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
    match trm with | Accu uu____62553 -> true | uu____62565 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____62575,uu____62576) -> false
    | uu____62590 -> true
  
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
  fun uu___516_62726  ->
    if uu___516_62726
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_62737  ->
    if uu___517_62737
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
      | (FStar_Syntax_Util.NotEqual ,uu____62753) ->
          FStar_Syntax_Util.NotEqual
      | (uu____62754,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____62755) -> FStar_Syntax_Util.Unknown
      | (uu____62756,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____62773 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____62793),String (s2,uu____62795)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____62808,uu____62809) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____62845,Lam uu____62846) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____62935 = eq_atom a1 a2  in
          eq_and uu____62935 (fun uu____62937  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____62976 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____62976
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____62992 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____63049  ->
                        match uu____63049 with
                        | ((a1,uu____63063),(a2,uu____63065)) ->
                            let uu____63074 = eq_t a1 a2  in
                            eq_inj acc uu____63074) FStar_Syntax_Util.Equal)
                uu____62992))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____63115 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63115
          then
            let uu____63118 =
              let uu____63119 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____63119  in
            eq_and uu____63118 (fun uu____63122  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____63129 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63129
      | (Univ u1,Univ u2) ->
          let uu____63133 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63133
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____63180 =
            let uu____63181 =
              let uu____63182 = t11 ()  in
              FStar_Pervasives_Native.fst uu____63182  in
            let uu____63187 =
              let uu____63188 = t21 ()  in
              FStar_Pervasives_Native.fst uu____63188  in
            eq_t uu____63181 uu____63187  in
          eq_and uu____63180
            (fun uu____63196  ->
               let uu____63197 =
                 let uu____63198 = mkAccuVar x  in r1 uu____63198  in
               let uu____63199 =
                 let uu____63200 = mkAccuVar x  in r2 uu____63200  in
               eq_t uu____63197 uu____63199)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____63201,uu____63202) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____63207,uu____63208) -> FStar_Syntax_Util.Unknown

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
          let uu____63289 = eq_arg x y  in
          eq_and uu____63289 (fun uu____63291  -> eq_args xs ys)
      | (uu____63292,uu____63293) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____63340) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____63345 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____63345
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____63374) ->
        let uu____63419 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____63430 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____63419 uu____63430
    | Accu (a,l) ->
        let uu____63447 =
          let uu____63449 = atom_to_string a  in
          let uu____63451 =
            let uu____63453 =
              let uu____63455 =
                let uu____63457 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____63457  in
              FStar_String.op_Hat uu____63455 ")"  in
            FStar_String.op_Hat ") (" uu____63453  in
          FStar_String.op_Hat uu____63449 uu____63451  in
        FStar_String.op_Hat "Accu (" uu____63447
    | Construct (fv,us,l) ->
        let uu____63495 =
          let uu____63497 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63499 =
            let uu____63501 =
              let uu____63503 =
                let uu____63505 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63505  in
              let uu____63511 =
                let uu____63513 =
                  let uu____63515 =
                    let uu____63517 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63517  in
                  FStar_String.op_Hat uu____63515 "]"  in
                FStar_String.op_Hat "] [" uu____63513  in
              FStar_String.op_Hat uu____63503 uu____63511  in
            FStar_String.op_Hat ") [" uu____63501  in
          FStar_String.op_Hat uu____63497 uu____63499  in
        FStar_String.op_Hat "Construct (" uu____63495
    | FV (fv,us,l) ->
        let uu____63556 =
          let uu____63558 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63560 =
            let uu____63562 =
              let uu____63564 =
                let uu____63566 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63566  in
              let uu____63572 =
                let uu____63574 =
                  let uu____63576 =
                    let uu____63578 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63578  in
                  FStar_String.op_Hat uu____63576 "]"  in
                FStar_String.op_Hat "] [" uu____63574  in
              FStar_String.op_Hat uu____63564 uu____63572  in
            FStar_String.op_Hat ") [" uu____63562  in
          FStar_String.op_Hat uu____63558 uu____63560  in
        FStar_String.op_Hat "FV (" uu____63556
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____63600 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____63600
    | Type_t u ->
        let uu____63604 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____63604
    | Arrow uu____63607 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____63653 = t ()  in FStar_Pervasives_Native.fst uu____63653
           in
        let uu____63658 =
          let uu____63660 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____63662 =
            let uu____63664 =
              let uu____63666 = t_to_string t1  in
              let uu____63668 =
                let uu____63670 =
                  let uu____63672 =
                    let uu____63674 =
                      let uu____63675 = mkAccuVar x1  in f uu____63675  in
                    t_to_string uu____63674  in
                  FStar_String.op_Hat uu____63672 "}"  in
                FStar_String.op_Hat "{" uu____63670  in
              FStar_String.op_Hat uu____63666 uu____63668  in
            FStar_String.op_Hat ":" uu____63664  in
          FStar_String.op_Hat uu____63660 uu____63662  in
        FStar_String.op_Hat "Refinement " uu____63658
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____63682 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____63682
    | Quote uu____63685 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____63692) ->
        let uu____63709 =
          let uu____63711 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____63711  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____63709
    | Lazy (FStar_Util.Inr (uu____63713,et),uu____63715) ->
        let uu____63732 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____63732
    | Rec
        (uu____63735,uu____63736,l,uu____63738,uu____63739,uu____63740,uu____63741)
        ->
        let uu____63786 =
          let uu____63788 =
            let uu____63790 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____63790  in
          FStar_String.op_Hat uu____63788 ")"  in
        FStar_String.op_Hat "Rec (" uu____63786

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____63801 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____63801
    | Match (t,uu____63805,uu____63806) ->
        let uu____63829 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____63829

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____63833 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____63833 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____63840 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____63840 (FStar_String.concat " ")

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
        let uu____64311 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____64311 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____64332 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____64332 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____64373  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____64388  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____64431 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____64431
         then
           let uu____64455 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____64455
         else ());
        (let uu____64460 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____64460
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____64494 = FStar_Dyn.mkdyn x  in (uu____64494, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____64562 'a .
    'Auu____64562 ->
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
              let uu____64613 = FStar_Common.force_thunk thunk1  in
              f uu____64613
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____64673 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____64673
              then
                let res =
                  let uu____64702 = FStar_Common.force_thunk thunk1  in
                  f uu____64702  in
                ((let uu____64744 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64744
                  then
                    let uu____64768 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____64770 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____64768
                      uu____64770
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____64779 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64779
                  then
                    let uu____64803 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____64803
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____64808 ->
              let aopt = f x  in
              ((let uu____64813 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____64813
                then
                  let uu____64837 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____64837
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
  let uu____64905 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____64905 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____64939 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____64944 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____64939 uu____64944 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____64985 -> FStar_Pervasives_Native.None  in
  let uu____64987 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____64992 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____64987 uu____64992 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____65034 -> FStar_Pervasives_Native.None  in
  let uu____65036 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____65041 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____65036 uu____65041 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____65083)) -> FStar_Pervasives_Native.Some s1
    | uu____65087 -> FStar_Pervasives_Native.None  in
  let uu____65089 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____65094 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____65089 uu____65094 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____65129 -> FStar_Pervasives_Native.None  in
  let uu____65130 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____65135 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____65130 uu____65135 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____65156 =
        let uu____65164 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____65164, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____65156  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____65189  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____65190 =
                 let uu____65191 =
                   let uu____65196 = type_of ea  in as_iarg uu____65196  in
                 [uu____65191]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65190
           | FStar_Pervasives_Native.Some x ->
               let uu____65206 =
                 let uu____65207 =
                   let uu____65212 = embed ea cb x  in as_arg uu____65212  in
                 let uu____65213 =
                   let uu____65220 =
                     let uu____65225 = type_of ea  in as_iarg uu____65225  in
                   [uu____65220]  in
                 uu____65207 :: uu____65213  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65206)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____65292)::uu____65293::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____65320 = unembed ea cb a  in
               FStar_Util.bind_opt uu____65320
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____65329 -> FStar_Pervasives_Native.None)
       in
    let uu____65332 =
      let uu____65333 =
        let uu____65334 = let uu____65339 = type_of ea  in as_arg uu____65339
           in
        [uu____65334]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____65333
       in
    mk_emb em un uu____65332 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65386 =
          let uu____65394 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____65394, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65386  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____65425  ->
             let uu____65426 =
               let uu____65427 =
                 let uu____65432 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____65432  in
               let uu____65433 =
                 let uu____65440 =
                   let uu____65445 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____65445  in
                 let uu____65446 =
                   let uu____65453 =
                     let uu____65458 = type_of eb  in as_iarg uu____65458  in
                   let uu____65459 =
                     let uu____65466 =
                       let uu____65471 = type_of ea  in as_iarg uu____65471
                        in
                     [uu____65466]  in
                   uu____65453 :: uu____65459  in
                 uu____65440 :: uu____65446  in
               uu____65427 :: uu____65433  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____65426)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____65539)::(a,uu____65541)::uu____65542::uu____65543::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____65582 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65582
                   (fun a1  ->
                      let uu____65592 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____65592
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____65605 -> FStar_Pervasives_Native.None)
         in
      let uu____65610 =
        let uu____65611 =
          let uu____65612 =
            let uu____65617 = type_of eb  in as_arg uu____65617  in
          let uu____65618 =
            let uu____65625 =
              let uu____65630 = type_of ea  in as_arg uu____65630  in
            [uu____65625]  in
          uu____65612 :: uu____65618  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____65611
         in
      mk_emb em un uu____65610 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65683 =
          let uu____65691 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____65691, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65683  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____65723  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____65725 =
                   let uu____65726 =
                     let uu____65731 = embed ea cb a  in as_arg uu____65731
                      in
                   let uu____65732 =
                     let uu____65739 =
                       let uu____65744 = type_of eb  in as_iarg uu____65744
                        in
                     let uu____65745 =
                       let uu____65752 =
                         let uu____65757 = type_of ea  in as_iarg uu____65757
                          in
                       [uu____65752]  in
                     uu____65739 :: uu____65745  in
                   uu____65726 :: uu____65732  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65725
             | FStar_Util.Inr b ->
                 let uu____65775 =
                   let uu____65776 =
                     let uu____65781 = embed eb cb b  in as_arg uu____65781
                      in
                   let uu____65782 =
                     let uu____65789 =
                       let uu____65794 = type_of eb  in as_iarg uu____65794
                        in
                     let uu____65795 =
                       let uu____65802 =
                         let uu____65807 = type_of ea  in as_iarg uu____65807
                          in
                       [uu____65802]  in
                     uu____65789 :: uu____65795  in
                   uu____65776 :: uu____65782  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65775)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____65869)::uu____65870::uu____65871::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____65906 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65906
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____65922)::uu____65923::uu____65924::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____65959 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____65959
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____65972 -> FStar_Pervasives_Native.None)
         in
      let uu____65977 =
        let uu____65978 =
          let uu____65979 =
            let uu____65984 = type_of eb  in as_arg uu____65984  in
          let uu____65985 =
            let uu____65992 =
              let uu____65997 = type_of ea  in as_arg uu____65997  in
            [uu____65992]  in
          uu____65979 :: uu____65985  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____65978
         in
      mk_emb em un uu____65977 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____66046 -> FStar_Pervasives_Native.None  in
  let uu____66047 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____66052 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____66047 uu____66052 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____66073 =
        let uu____66081 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____66081, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____66073  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____66108  ->
           let typ = let uu____66110 = type_of ea  in as_iarg uu____66110  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____66131 =
               let uu____66132 = as_arg tl1  in
               let uu____66137 =
                 let uu____66144 =
                   let uu____66149 = embed ea cb hd1  in as_arg uu____66149
                    in
                 [uu____66144; typ]  in
               uu____66132 :: uu____66137  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____66131
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____66197,uu____66198) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____66218,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____66221,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____66222))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66250 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66250
                 (fun hd2  ->
                    let uu____66258 = un cb tl1  in
                    FStar_Util.bind_opt uu____66258
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____66274,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66299 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66299
                 (fun hd2  ->
                    let uu____66307 = un cb tl1  in
                    FStar_Util.bind_opt uu____66307
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____66322 -> FStar_Pervasives_Native.None)
       in
    let uu____66325 =
      let uu____66326 =
        let uu____66327 = let uu____66332 = type_of ea  in as_arg uu____66332
           in
        [uu____66327]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____66326
       in
    mk_emb em un uu____66325 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____66405  ->
             Lam
               ((fun tas  ->
                   let uu____66435 =
                     let uu____66438 = FStar_List.hd tas  in
                     unembed ea cb uu____66438  in
                   match uu____66435 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____66440 = f a  in embed eb cb uu____66440
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____66453  ->
                     let uu____66456 = type_of eb  in as_arg uu____66456)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____66514 =
                 let uu____66517 =
                   let uu____66518 =
                     let uu____66519 =
                       let uu____66524 = embed ea cb x  in as_arg uu____66524
                        in
                     [uu____66519]  in
                   cb.iapp lam1 uu____66518  in
                 unembed eb cb uu____66517  in
               match uu____66514 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____66538 =
        let uu____66539 = type_of ea  in
        let uu____66540 =
          let uu____66541 = type_of eb  in as_iarg uu____66541  in
        make_arrow1 uu____66539 uu____66540  in
      mk_emb em un uu____66538 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____66559 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66559 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____66564 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66564 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____66569 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66569 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____66574 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66574 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____66579 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66579 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____66584 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66584 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____66589 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66589 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____66594 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66594 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____66599 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66599 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____66608 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66609 =
          let uu____66610 =
            let uu____66615 =
              let uu____66616 = e_list e_string  in embed uu____66616 cb l
               in
            as_arg uu____66615  in
          [uu____66610]  in
        mkFV uu____66608 [] uu____66609
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____66638 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66639 =
          let uu____66640 =
            let uu____66645 =
              let uu____66646 = e_list e_string  in embed uu____66646 cb l
               in
            as_arg uu____66645  in
          [uu____66640]  in
        mkFV uu____66638 [] uu____66639
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____66668 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66669 =
          let uu____66670 =
            let uu____66675 =
              let uu____66676 = e_list e_string  in embed uu____66676 cb l
               in
            as_arg uu____66675  in
          [uu____66670]  in
        mkFV uu____66668 [] uu____66669
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____66710,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____66726,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____66742,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____66758,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____66774,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____66790,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____66806,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____66822,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____66838,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____66854,(l,uu____66856)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____66875 =
          let uu____66881 = e_list e_string  in unembed uu____66881 cb l  in
        FStar_Util.bind_opt uu____66875
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66901  -> FStar_Pervasives_Native.Some _66901)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____66903,(l,uu____66905)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____66924 =
          let uu____66930 = e_list e_string  in unembed uu____66930 cb l  in
        FStar_Util.bind_opt uu____66924
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66950  -> FStar_Pervasives_Native.Some _66950)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____66952,(l,uu____66954)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____66973 =
          let uu____66979 = e_list e_string  in unembed uu____66979 cb l  in
        FStar_Util.bind_opt uu____66973
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66999  -> FStar_Pervasives_Native.Some _66999)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____67000 ->
        ((let uu____67002 =
            let uu____67008 =
              let uu____67010 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____67010
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67008)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67002);
         FStar_Pervasives_Native.None)
     in
  let uu____67014 =
    let uu____67015 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____67015 [] []  in
  let uu____67020 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____67014 uu____67020 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____67029  -> failwith "bogus_cbs translate")
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
      let uu____67106 =
        let uu____67115 = e_list e  in unembed uu____67115 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67106
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____67137  ->
    match uu____67137 with
    | (a,uu____67145) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____67160)::[]) when
             let uu____67177 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____67177 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____67184 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____67227 = let uu____67234 = as_arg c  in [uu____67234]  in
      int_to_t2 uu____67227
  
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
          let uu____67288 = f a  in FStar_Pervasives_Native.Some uu____67288
      | uu____67289 -> FStar_Pervasives_Native.None
  
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
          let uu____67343 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____67343
      | uu____67344 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67388 = FStar_List.map as_a args  in
        lift_unary f uu____67388
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67443 = FStar_List.map as_a args  in
        lift_binary f uu____67443
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____67473 = f x  in embed e_int bogus_cbs uu____67473)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____67500 = f x y  in embed e_int bogus_cbs uu____67500)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____67526 = f x  in embed e_bool bogus_cbs uu____67526)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____67564 = f x y  in embed e_bool bogus_cbs uu____67564)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____67602 = f x y  in embed e_string bogus_cbs uu____67602)
  
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
                let uu____67707 =
                  let uu____67716 = as_a a  in
                  let uu____67719 = as_b b  in (uu____67716, uu____67719)  in
                (match uu____67707 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____67734 =
                       let uu____67735 = f a1 b1  in embed_c uu____67735  in
                     FStar_Pervasives_Native.Some uu____67734
                 | uu____67736 -> FStar_Pervasives_Native.None)
            | uu____67745 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____67754 = e_list e_char  in
    let uu____67761 = FStar_String.list_of_string s  in
    embed uu____67754 bogus_cbs uu____67761
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____67800 =
        let uu____67801 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____67801  in
      embed e_int bogus_cbs uu____67800
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____67835 = arg_as_string a1  in
        (match uu____67835 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____67844 = arg_as_list e_string a2  in
             (match uu____67844 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____67862 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____67862
              | uu____67864 -> FStar_Pervasives_Native.None)
         | uu____67870 -> FStar_Pervasives_Native.None)
    | uu____67874 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____67881 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____67881
  
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
      | (_typ,uu____67943)::(a1,uu____67945)::(a2,uu____67947)::[] ->
          let uu____67964 = eq_t a1 a2  in
          (match uu____67964 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____67973 -> FStar_Pervasives_Native.None)
      | uu____67974 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____67989)::(_typ,uu____67991)::(a1,uu____67993)::(a2,uu____67995)::[]
        ->
        let uu____68016 = eq_t a1 a2  in
        (match uu____68016 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68019 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68019
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68022 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68022
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68025 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68040)::(_v,uu____68042)::(t1,uu____68044)::(t2,uu____68046)::
        (a1,uu____68048)::(a2,uu____68050)::[] ->
        let uu____68079 =
          let uu____68080 = eq_t t1 t2  in
          let uu____68081 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____68080 uu____68081  in
        (match uu____68079 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68084 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68084
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68087 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68087
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68090 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____68109 =
        let uu____68111 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____68111  in
      failwith uu____68109
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____68127)::[] ->
        let uu____68136 = unembed e_range bogus_cbs a1  in
        (match uu____68136 with
         | FStar_Pervasives_Native.Some r ->
             let uu____68142 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68142
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____68143 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68179 = arg_as_list e_char a1  in
        (match uu____68179 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68195 = arg_as_string a2  in
             (match uu____68195 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68208 =
                    let uu____68209 = e_list e_string  in
                    embed uu____68209 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____68208
              | uu____68219 -> FStar_Pervasives_Native.None)
         | uu____68223 -> FStar_Pervasives_Native.None)
    | uu____68229 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68262 =
          let uu____68272 = arg_as_string a1  in
          let uu____68276 = arg_as_int a2  in (uu____68272, uu____68276)  in
        (match uu____68262 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_68300  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68305 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68305) ()
              with | uu___1496_68308 -> FStar_Pervasives_Native.None)
         | uu____68311 -> FStar_Pervasives_Native.None)
    | uu____68321 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68354 =
          let uu____68365 = arg_as_string a1  in
          let uu____68369 = arg_as_char a2  in (uu____68365, uu____68369)  in
        (match uu____68354 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_68398  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68402 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68402) ()
              with | uu___1514_68404 -> FStar_Pervasives_Native.None)
         | uu____68407 -> FStar_Pervasives_Native.None)
    | uu____68418 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____68460 =
          let uu____68474 = arg_as_string a1  in
          let uu____68478 = arg_as_int a2  in
          let uu____68481 = arg_as_int a3  in
          (uu____68474, uu____68478, uu____68481)  in
        (match uu____68460 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_68514  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68519 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68519) ()
              with | uu___1537_68522 -> FStar_Pervasives_Native.None)
         | uu____68525 -> FStar_Pervasives_Native.None)
    | uu____68539 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68599 =
          let uu____68621 = arg_as_string fn  in
          let uu____68625 = arg_as_int from_line  in
          let uu____68628 = arg_as_int from_col  in
          let uu____68631 = arg_as_int to_line  in
          let uu____68634 = arg_as_int to_col  in
          (uu____68621, uu____68625, uu____68628, uu____68631, uu____68634)
           in
        (match uu____68599 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68669 =
                 let uu____68670 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68672 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68670 uu____68672  in
               let uu____68674 =
                 let uu____68675 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68677 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68675 uu____68677  in
               FStar_Range.mk_range fn1 uu____68669 uu____68674  in
             let uu____68679 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68679
         | uu____68680 -> FStar_Pervasives_Native.None)
    | uu____68702 -> FStar_Pervasives_Native.None
  
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
                let uu____68792 = FStar_List.splitAt n_tvars args  in
                match uu____68792 with
                | (_tvar_args,rest_args) ->
                    let uu____68841 = FStar_List.hd rest_args  in
                    (match uu____68841 with
                     | (x,uu____68853) ->
                         let uu____68854 = unembed ea cb x  in
                         FStar_Util.map_opt uu____68854
                           (fun x1  ->
                              let uu____68860 = f x1  in
                              embed eb cb uu____68860))
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
                  let uu____68969 = FStar_List.splitAt n_tvars args  in
                  match uu____68969 with
                  | (_tvar_args,rest_args) ->
                      let uu____69018 = FStar_List.hd rest_args  in
                      (match uu____69018 with
                       | (x,uu____69030) ->
                           let uu____69031 =
                             let uu____69036 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____69036  in
                           (match uu____69031 with
                            | (y,uu____69054) ->
                                let uu____69055 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____69055
                                  (fun x1  ->
                                     let uu____69061 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____69061
                                       (fun y1  ->
                                          let uu____69067 =
                                            let uu____69068 = f x1 y1  in
                                            embed ec cb uu____69068  in
                                          FStar_Pervasives_Native.Some
                                            uu____69067))))
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
                    let uu____69196 = FStar_List.splitAt n_tvars args  in
                    match uu____69196 with
                    | (_tvar_args,rest_args) ->
                        let uu____69245 = FStar_List.hd rest_args  in
                        (match uu____69245 with
                         | (x,uu____69257) ->
                             let uu____69258 =
                               let uu____69263 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____69263  in
                             (match uu____69258 with
                              | (y,uu____69281) ->
                                  let uu____69282 =
                                    let uu____69287 =
                                      let uu____69294 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____69294  in
                                    FStar_List.hd uu____69287  in
                                  (match uu____69282 with
                                   | (z,uu____69316) ->
                                       let uu____69317 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____69317
                                         (fun x1  ->
                                            let uu____69323 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____69323
                                              (fun y1  ->
                                                 let uu____69329 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____69329
                                                   (fun z1  ->
                                                      let uu____69335 =
                                                        let uu____69336 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____69336
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____69335))))))
                     in
                  f_wrapped
  