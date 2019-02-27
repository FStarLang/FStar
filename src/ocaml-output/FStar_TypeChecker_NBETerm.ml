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
    match projectee with | Unit  -> true | uu____60716 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____60729 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____60752 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____60777 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____60813 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____60836 -> false
  
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
    match projectee with | Var _0 -> true | uu____61219 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____61256 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____61357 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____61477 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____61541 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____61617 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____61679 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____61699 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____61719 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____61738 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____61770 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____61864 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____61926 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____61950 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____61996 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____62094 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____62228 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____62272 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____62310 -> false
  
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
    match projectee with | TOTAL  -> true | uu____62440 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____62451 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____62462 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____62473 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____62484 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____62495 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____62506 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____62517 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____62528 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____62540 -> false
  
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
    match trm with | Accu uu____62617 -> true | uu____62629 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____62639,uu____62640) -> false
    | uu____62654 -> true
  
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
  fun uu___516_62790  ->
    if uu___516_62790
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_62801  ->
    if uu___517_62801
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
      | (FStar_Syntax_Util.NotEqual ,uu____62817) ->
          FStar_Syntax_Util.NotEqual
      | (uu____62818,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____62819) -> FStar_Syntax_Util.Unknown
      | (uu____62820,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____62837 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____62857),String (s2,uu____62859)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____62872,uu____62873) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____62909,Lam uu____62910) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____62999 = eq_atom a1 a2  in
          eq_and uu____62999 (fun uu____63001  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____63040 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63040
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____63056 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____63113  ->
                        match uu____63113 with
                        | ((a1,uu____63127),(a2,uu____63129)) ->
                            let uu____63138 = eq_t a1 a2  in
                            eq_inj acc uu____63138) FStar_Syntax_Util.Equal)
                uu____63056))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____63179 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63179
          then
            let uu____63182 =
              let uu____63183 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____63183  in
            eq_and uu____63182 (fun uu____63186  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____63193 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63193
      | (Univ u1,Univ u2) ->
          let uu____63197 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63197
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____63244 =
            let uu____63245 =
              let uu____63246 = t11 ()  in
              FStar_Pervasives_Native.fst uu____63246  in
            let uu____63251 =
              let uu____63252 = t21 ()  in
              FStar_Pervasives_Native.fst uu____63252  in
            eq_t uu____63245 uu____63251  in
          eq_and uu____63244
            (fun uu____63260  ->
               let uu____63261 =
                 let uu____63262 = mkAccuVar x  in r1 uu____63262  in
               let uu____63263 =
                 let uu____63264 = mkAccuVar x  in r2 uu____63264  in
               eq_t uu____63261 uu____63263)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____63265,uu____63266) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____63271,uu____63272) -> FStar_Syntax_Util.Unknown

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
          let uu____63353 = eq_arg x y  in
          eq_and uu____63353 (fun uu____63355  -> eq_args xs ys)
      | (uu____63356,uu____63357) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____63404) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____63409 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____63409
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____63438) ->
        let uu____63483 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____63494 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____63483 uu____63494
    | Accu (a,l) ->
        let uu____63511 =
          let uu____63513 = atom_to_string a  in
          let uu____63515 =
            let uu____63517 =
              let uu____63519 =
                let uu____63521 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____63521  in
              FStar_String.op_Hat uu____63519 ")"  in
            FStar_String.op_Hat ") (" uu____63517  in
          FStar_String.op_Hat uu____63513 uu____63515  in
        FStar_String.op_Hat "Accu (" uu____63511
    | Construct (fv,us,l) ->
        let uu____63559 =
          let uu____63561 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63563 =
            let uu____63565 =
              let uu____63567 =
                let uu____63569 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63569  in
              let uu____63575 =
                let uu____63577 =
                  let uu____63579 =
                    let uu____63581 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63581  in
                  FStar_String.op_Hat uu____63579 "]"  in
                FStar_String.op_Hat "] [" uu____63577  in
              FStar_String.op_Hat uu____63567 uu____63575  in
            FStar_String.op_Hat ") [" uu____63565  in
          FStar_String.op_Hat uu____63561 uu____63563  in
        FStar_String.op_Hat "Construct (" uu____63559
    | FV (fv,us,l) ->
        let uu____63620 =
          let uu____63622 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63624 =
            let uu____63626 =
              let uu____63628 =
                let uu____63630 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63630  in
              let uu____63636 =
                let uu____63638 =
                  let uu____63640 =
                    let uu____63642 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63642  in
                  FStar_String.op_Hat uu____63640 "]"  in
                FStar_String.op_Hat "] [" uu____63638  in
              FStar_String.op_Hat uu____63628 uu____63636  in
            FStar_String.op_Hat ") [" uu____63626  in
          FStar_String.op_Hat uu____63622 uu____63624  in
        FStar_String.op_Hat "FV (" uu____63620
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____63664 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____63664
    | Type_t u ->
        let uu____63668 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____63668
    | Arrow uu____63671 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____63717 = t ()  in FStar_Pervasives_Native.fst uu____63717
           in
        let uu____63722 =
          let uu____63724 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____63726 =
            let uu____63728 =
              let uu____63730 = t_to_string t1  in
              let uu____63732 =
                let uu____63734 =
                  let uu____63736 =
                    let uu____63738 =
                      let uu____63739 = mkAccuVar x1  in f uu____63739  in
                    t_to_string uu____63738  in
                  FStar_String.op_Hat uu____63736 "}"  in
                FStar_String.op_Hat "{" uu____63734  in
              FStar_String.op_Hat uu____63730 uu____63732  in
            FStar_String.op_Hat ":" uu____63728  in
          FStar_String.op_Hat uu____63724 uu____63726  in
        FStar_String.op_Hat "Refinement " uu____63722
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____63746 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____63746
    | Quote uu____63749 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____63756) ->
        let uu____63773 =
          let uu____63775 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____63775  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____63773
    | Lazy (FStar_Util.Inr (uu____63777,et),uu____63779) ->
        let uu____63796 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____63796
    | Rec
        (uu____63799,uu____63800,l,uu____63802,uu____63803,uu____63804,uu____63805)
        ->
        let uu____63850 =
          let uu____63852 =
            let uu____63854 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____63854  in
          FStar_String.op_Hat uu____63852 ")"  in
        FStar_String.op_Hat "Rec (" uu____63850

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____63865 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____63865
    | Match (t,uu____63869,uu____63870) ->
        let uu____63893 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____63893

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____63897 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____63897 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____63904 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____63904 (FStar_String.concat " ")

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
        let uu____64375 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____64375 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____64396 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____64396 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____64437  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____64452  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____64495 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____64495
         then
           let uu____64519 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____64519
         else ());
        (let uu____64524 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____64524
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____64558 = FStar_Dyn.mkdyn x  in (uu____64558, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____64626 'a .
    'Auu____64626 ->
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
              let uu____64677 = FStar_Common.force_thunk thunk1  in
              f uu____64677
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____64737 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____64737
              then
                let res =
                  let uu____64766 = FStar_Common.force_thunk thunk1  in
                  f uu____64766  in
                ((let uu____64808 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64808
                  then
                    let uu____64832 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____64834 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____64832
                      uu____64834
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____64843 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64843
                  then
                    let uu____64867 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____64867
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____64872 ->
              let aopt = f x  in
              ((let uu____64877 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____64877
                then
                  let uu____64901 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____64901
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
  let uu____64969 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____64969 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____65003 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____65008 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____65003 uu____65008 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____65049 -> FStar_Pervasives_Native.None  in
  let uu____65051 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____65056 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____65051 uu____65056 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____65098 -> FStar_Pervasives_Native.None  in
  let uu____65100 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____65105 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____65100 uu____65105 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____65147)) -> FStar_Pervasives_Native.Some s1
    | uu____65151 -> FStar_Pervasives_Native.None  in
  let uu____65153 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____65158 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____65153 uu____65158 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____65193 -> FStar_Pervasives_Native.None  in
  let uu____65194 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____65199 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____65194 uu____65199 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____65220 =
        let uu____65228 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____65228, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____65220  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____65253  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____65254 =
                 let uu____65255 =
                   let uu____65260 = type_of ea  in as_iarg uu____65260  in
                 [uu____65255]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65254
           | FStar_Pervasives_Native.Some x ->
               let uu____65270 =
                 let uu____65271 =
                   let uu____65276 = embed ea cb x  in as_arg uu____65276  in
                 let uu____65277 =
                   let uu____65284 =
                     let uu____65289 = type_of ea  in as_iarg uu____65289  in
                   [uu____65284]  in
                 uu____65271 :: uu____65277  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65270)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____65356)::uu____65357::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____65384 = unembed ea cb a  in
               FStar_Util.bind_opt uu____65384
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____65393 -> FStar_Pervasives_Native.None)
       in
    let uu____65396 =
      let uu____65397 =
        let uu____65398 = let uu____65403 = type_of ea  in as_arg uu____65403
           in
        [uu____65398]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____65397
       in
    mk_emb em un uu____65396 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65450 =
          let uu____65458 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____65458, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65450  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____65489  ->
             let uu____65490 =
               let uu____65491 =
                 let uu____65496 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____65496  in
               let uu____65497 =
                 let uu____65504 =
                   let uu____65509 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____65509  in
                 let uu____65510 =
                   let uu____65517 =
                     let uu____65522 = type_of eb  in as_iarg uu____65522  in
                   let uu____65523 =
                     let uu____65530 =
                       let uu____65535 = type_of ea  in as_iarg uu____65535
                        in
                     [uu____65530]  in
                   uu____65517 :: uu____65523  in
                 uu____65504 :: uu____65510  in
               uu____65491 :: uu____65497  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____65490)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____65603)::(a,uu____65605)::uu____65606::uu____65607::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____65646 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65646
                   (fun a1  ->
                      let uu____65656 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____65656
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____65669 -> FStar_Pervasives_Native.None)
         in
      let uu____65674 =
        let uu____65675 =
          let uu____65676 =
            let uu____65681 = type_of eb  in as_arg uu____65681  in
          let uu____65682 =
            let uu____65689 =
              let uu____65694 = type_of ea  in as_arg uu____65694  in
            [uu____65689]  in
          uu____65676 :: uu____65682  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____65675
         in
      mk_emb em un uu____65674 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65747 =
          let uu____65755 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____65755, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65747  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____65787  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____65789 =
                   let uu____65790 =
                     let uu____65795 = embed ea cb a  in as_arg uu____65795
                      in
                   let uu____65796 =
                     let uu____65803 =
                       let uu____65808 = type_of eb  in as_iarg uu____65808
                        in
                     let uu____65809 =
                       let uu____65816 =
                         let uu____65821 = type_of ea  in as_iarg uu____65821
                          in
                       [uu____65816]  in
                     uu____65803 :: uu____65809  in
                   uu____65790 :: uu____65796  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65789
             | FStar_Util.Inr b ->
                 let uu____65839 =
                   let uu____65840 =
                     let uu____65845 = embed eb cb b  in as_arg uu____65845
                      in
                   let uu____65846 =
                     let uu____65853 =
                       let uu____65858 = type_of eb  in as_iarg uu____65858
                        in
                     let uu____65859 =
                       let uu____65866 =
                         let uu____65871 = type_of ea  in as_iarg uu____65871
                          in
                       [uu____65866]  in
                     uu____65853 :: uu____65859  in
                   uu____65840 :: uu____65846  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65839)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____65933)::uu____65934::uu____65935::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____65970 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65970
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____65986)::uu____65987::uu____65988::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____66023 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____66023
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____66036 -> FStar_Pervasives_Native.None)
         in
      let uu____66041 =
        let uu____66042 =
          let uu____66043 =
            let uu____66048 = type_of eb  in as_arg uu____66048  in
          let uu____66049 =
            let uu____66056 =
              let uu____66061 = type_of ea  in as_arg uu____66061  in
            [uu____66056]  in
          uu____66043 :: uu____66049  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____66042
         in
      mk_emb em un uu____66041 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____66110 -> FStar_Pervasives_Native.None  in
  let uu____66111 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____66116 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____66111 uu____66116 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____66137 =
        let uu____66145 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____66145, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____66137  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____66172  ->
           let typ = let uu____66174 = type_of ea  in as_iarg uu____66174  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____66195 =
               let uu____66196 = as_arg tl1  in
               let uu____66201 =
                 let uu____66208 =
                   let uu____66213 = embed ea cb hd1  in as_arg uu____66213
                    in
                 [uu____66208; typ]  in
               uu____66196 :: uu____66201  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____66195
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____66261,uu____66262) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____66282,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____66285,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____66286))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66314 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66314
                 (fun hd2  ->
                    let uu____66322 = un cb tl1  in
                    FStar_Util.bind_opt uu____66322
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____66338,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66363 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66363
                 (fun hd2  ->
                    let uu____66371 = un cb tl1  in
                    FStar_Util.bind_opt uu____66371
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____66386 -> FStar_Pervasives_Native.None)
       in
    let uu____66389 =
      let uu____66390 =
        let uu____66391 = let uu____66396 = type_of ea  in as_arg uu____66396
           in
        [uu____66391]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____66390
       in
    mk_emb em un uu____66389 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____66469  ->
             Lam
               ((fun tas  ->
                   let uu____66499 =
                     let uu____66502 = FStar_List.hd tas  in
                     unembed ea cb uu____66502  in
                   match uu____66499 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____66504 = f a  in embed eb cb uu____66504
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____66517  ->
                     let uu____66520 = type_of eb  in as_arg uu____66520)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____66578 =
                 let uu____66581 =
                   let uu____66582 =
                     let uu____66583 =
                       let uu____66588 = embed ea cb x  in as_arg uu____66588
                        in
                     [uu____66583]  in
                   cb.iapp lam1 uu____66582  in
                 unembed eb cb uu____66581  in
               match uu____66578 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____66602 =
        let uu____66603 = type_of ea  in
        let uu____66604 =
          let uu____66605 = type_of eb  in as_iarg uu____66605  in
        make_arrow1 uu____66603 uu____66604  in
      mk_emb em un uu____66602 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____66623 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66623 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____66628 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66628 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____66633 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66633 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____66638 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66638 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____66643 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66643 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____66648 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66648 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____66653 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66653 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____66658 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66658 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____66663 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66663 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____66672 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66673 =
          let uu____66674 =
            let uu____66679 =
              let uu____66680 = e_list e_string  in embed uu____66680 cb l
               in
            as_arg uu____66679  in
          [uu____66674]  in
        mkFV uu____66672 [] uu____66673
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____66702 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66703 =
          let uu____66704 =
            let uu____66709 =
              let uu____66710 = e_list e_string  in embed uu____66710 cb l
               in
            as_arg uu____66709  in
          [uu____66704]  in
        mkFV uu____66702 [] uu____66703
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____66732 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66733 =
          let uu____66734 =
            let uu____66739 =
              let uu____66740 = e_list e_string  in embed uu____66740 cb l
               in
            as_arg uu____66739  in
          [uu____66734]  in
        mkFV uu____66732 [] uu____66733
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____66774,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____66790,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____66806,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____66822,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____66838,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____66854,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____66870,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____66886,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____66902,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____66918,(l,uu____66920)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____66939 =
          let uu____66945 = e_list e_string  in unembed uu____66945 cb l  in
        FStar_Util.bind_opt uu____66939
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66965  -> FStar_Pervasives_Native.Some _66965)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____66967,(l,uu____66969)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____66988 =
          let uu____66994 = e_list e_string  in unembed uu____66994 cb l  in
        FStar_Util.bind_opt uu____66988
          (fun ss  ->
             FStar_All.pipe_left
               (fun _67014  -> FStar_Pervasives_Native.Some _67014)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____67016,(l,uu____67018)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____67037 =
          let uu____67043 = e_list e_string  in unembed uu____67043 cb l  in
        FStar_Util.bind_opt uu____67037
          (fun ss  ->
             FStar_All.pipe_left
               (fun _67063  -> FStar_Pervasives_Native.Some _67063)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____67064 ->
        ((let uu____67066 =
            let uu____67072 =
              let uu____67074 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____67074
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67072)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67066);
         FStar_Pervasives_Native.None)
     in
  let uu____67078 =
    let uu____67079 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____67079 [] []  in
  let uu____67084 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____67078 uu____67084 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____67093  -> failwith "bogus_cbs translate")
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
      let uu____67170 =
        let uu____67179 = e_list e  in unembed uu____67179 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67170
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____67201  ->
    match uu____67201 with
    | (a,uu____67209) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____67224)::[]) when
             let uu____67241 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____67241 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____67248 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____67291 = let uu____67298 = as_arg c  in [uu____67298]  in
      int_to_t2 uu____67291
  
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
          let uu____67352 = f a  in FStar_Pervasives_Native.Some uu____67352
      | uu____67353 -> FStar_Pervasives_Native.None
  
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
          let uu____67407 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____67407
      | uu____67408 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67452 = FStar_List.map as_a args  in
        lift_unary f uu____67452
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67507 = FStar_List.map as_a args  in
        lift_binary f uu____67507
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____67537 = f x  in embed e_int bogus_cbs uu____67537)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____67564 = f x y  in embed e_int bogus_cbs uu____67564)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____67590 = f x  in embed e_bool bogus_cbs uu____67590)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____67628 = f x y  in embed e_bool bogus_cbs uu____67628)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____67666 = f x y  in embed e_string bogus_cbs uu____67666)
  
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
                let uu____67771 =
                  let uu____67780 = as_a a  in
                  let uu____67783 = as_b b  in (uu____67780, uu____67783)  in
                (match uu____67771 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____67798 =
                       let uu____67799 = f a1 b1  in embed_c uu____67799  in
                     FStar_Pervasives_Native.Some uu____67798
                 | uu____67800 -> FStar_Pervasives_Native.None)
            | uu____67809 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____67818 = e_list e_char  in
    let uu____67825 = FStar_String.list_of_string s  in
    embed uu____67818 bogus_cbs uu____67825
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____67864 =
        let uu____67865 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____67865  in
      embed e_int bogus_cbs uu____67864
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____67899 = arg_as_string a1  in
        (match uu____67899 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____67908 = arg_as_list e_string a2  in
             (match uu____67908 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____67926 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____67926
              | uu____67928 -> FStar_Pervasives_Native.None)
         | uu____67934 -> FStar_Pervasives_Native.None)
    | uu____67938 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____67945 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____67945
  
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
      | (_typ,uu____68007)::(a1,uu____68009)::(a2,uu____68011)::[] ->
          let uu____68028 = eq_t a1 a2  in
          (match uu____68028 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____68037 -> FStar_Pervasives_Native.None)
      | uu____68038 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68053)::(_typ,uu____68055)::(a1,uu____68057)::(a2,uu____68059)::[]
        ->
        let uu____68080 = eq_t a1 a2  in
        (match uu____68080 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68083 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68083
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68086 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68086
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68089 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68104)::(_v,uu____68106)::(t1,uu____68108)::(t2,uu____68110)::
        (a1,uu____68112)::(a2,uu____68114)::[] ->
        let uu____68143 =
          let uu____68144 = eq_t t1 t2  in
          let uu____68145 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____68144 uu____68145  in
        (match uu____68143 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68148 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68148
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68151 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68151
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68154 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____68173 =
        let uu____68175 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____68175  in
      failwith uu____68173
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____68191)::[] ->
        let uu____68200 = unembed e_range bogus_cbs a1  in
        (match uu____68200 with
         | FStar_Pervasives_Native.Some r ->
             let uu____68206 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68206
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____68207 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68243 = arg_as_list e_char a1  in
        (match uu____68243 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68259 = arg_as_string a2  in
             (match uu____68259 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68272 =
                    let uu____68273 = e_list e_string  in
                    embed uu____68273 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____68272
              | uu____68283 -> FStar_Pervasives_Native.None)
         | uu____68287 -> FStar_Pervasives_Native.None)
    | uu____68293 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68326 =
          let uu____68336 = arg_as_string a1  in
          let uu____68340 = arg_as_int a2  in (uu____68336, uu____68340)  in
        (match uu____68326 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_68364  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68369 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68369) ()
              with | uu___1496_68372 -> FStar_Pervasives_Native.None)
         | uu____68375 -> FStar_Pervasives_Native.None)
    | uu____68385 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68418 =
          let uu____68429 = arg_as_string a1  in
          let uu____68433 = arg_as_char a2  in (uu____68429, uu____68433)  in
        (match uu____68418 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_68462  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68466 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68466) ()
              with | uu___1514_68468 -> FStar_Pervasives_Native.None)
         | uu____68471 -> FStar_Pervasives_Native.None)
    | uu____68482 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____68524 =
          let uu____68538 = arg_as_string a1  in
          let uu____68542 = arg_as_int a2  in
          let uu____68545 = arg_as_int a3  in
          (uu____68538, uu____68542, uu____68545)  in
        (match uu____68524 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_68578  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68583 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68583) ()
              with | uu___1537_68586 -> FStar_Pervasives_Native.None)
         | uu____68589 -> FStar_Pervasives_Native.None)
    | uu____68603 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68663 =
          let uu____68685 = arg_as_string fn  in
          let uu____68689 = arg_as_int from_line  in
          let uu____68692 = arg_as_int from_col  in
          let uu____68695 = arg_as_int to_line  in
          let uu____68698 = arg_as_int to_col  in
          (uu____68685, uu____68689, uu____68692, uu____68695, uu____68698)
           in
        (match uu____68663 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68733 =
                 let uu____68734 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68736 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68734 uu____68736  in
               let uu____68738 =
                 let uu____68739 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68741 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68739 uu____68741  in
               FStar_Range.mk_range fn1 uu____68733 uu____68738  in
             let uu____68743 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68743
         | uu____68744 -> FStar_Pervasives_Native.None)
    | uu____68766 -> FStar_Pervasives_Native.None
  
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
                let uu____68856 = FStar_List.splitAt n_tvars args  in
                match uu____68856 with
                | (_tvar_args,rest_args) ->
                    let uu____68905 = FStar_List.hd rest_args  in
                    (match uu____68905 with
                     | (x,uu____68917) ->
                         let uu____68918 = unembed ea cb x  in
                         FStar_Util.map_opt uu____68918
                           (fun x1  ->
                              let uu____68924 = f x1  in
                              embed eb cb uu____68924))
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
                  let uu____69033 = FStar_List.splitAt n_tvars args  in
                  match uu____69033 with
                  | (_tvar_args,rest_args) ->
                      let uu____69082 = FStar_List.hd rest_args  in
                      (match uu____69082 with
                       | (x,uu____69094) ->
                           let uu____69095 =
                             let uu____69100 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____69100  in
                           (match uu____69095 with
                            | (y,uu____69118) ->
                                let uu____69119 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____69119
                                  (fun x1  ->
                                     let uu____69125 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____69125
                                       (fun y1  ->
                                          let uu____69131 =
                                            let uu____69132 = f x1 y1  in
                                            embed ec cb uu____69132  in
                                          FStar_Pervasives_Native.Some
                                            uu____69131))))
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
                    let uu____69260 = FStar_List.splitAt n_tvars args  in
                    match uu____69260 with
                    | (_tvar_args,rest_args) ->
                        let uu____69309 = FStar_List.hd rest_args  in
                        (match uu____69309 with
                         | (x,uu____69321) ->
                             let uu____69322 =
                               let uu____69327 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____69327  in
                             (match uu____69322 with
                              | (y,uu____69345) ->
                                  let uu____69346 =
                                    let uu____69351 =
                                      let uu____69358 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____69358  in
                                    FStar_List.hd uu____69351  in
                                  (match uu____69346 with
                                   | (z,uu____69380) ->
                                       let uu____69381 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____69381
                                         (fun x1  ->
                                            let uu____69387 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____69387
                                              (fun y1  ->
                                                 let uu____69393 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____69393
                                                   (fun z1  ->
                                                      let uu____69399 =
                                                        let uu____69400 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____69400
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____69399))))))
                     in
                  f_wrapped
  