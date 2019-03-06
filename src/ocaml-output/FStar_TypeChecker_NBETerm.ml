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
    match projectee with | Unit  -> true | uu____56642 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____56655 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____56678 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____56703 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____56739 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____56762 -> false
  
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
    match projectee with | Var _0 -> true | uu____57145 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____57182 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____57283 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____57403 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____57467 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____57543 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____57605 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____57625 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____57645 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____57664 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____57696 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____57790 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____57852 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____57876 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____57922 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____58020 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____58154 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____58198 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____58236 -> false
  
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
    match projectee with | TOTAL  -> true | uu____58366 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____58377 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____58388 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____58399 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____58410 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____58421 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____58432 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____58443 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____58454 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____58466 -> false
  
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
    match trm with | Accu uu____58543 -> true | uu____58555 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____58565,uu____58566) -> false
    | uu____58580 -> true
  
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
  fun uu___516_58716  ->
    if uu___516_58716
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_58727  ->
    if uu___517_58727
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
      | (FStar_Syntax_Util.NotEqual ,uu____58743) ->
          FStar_Syntax_Util.NotEqual
      | (uu____58744,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____58745) -> FStar_Syntax_Util.Unknown
      | (uu____58746,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____58763 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____58783),String (s2,uu____58785)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____58798,uu____58799) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____58835,Lam uu____58836) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____58925 = eq_atom a1 a2  in
          eq_and uu____58925 (fun uu____58927  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____58966 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58966
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____58982 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____59039  ->
                        match uu____59039 with
                        | ((a1,uu____59053),(a2,uu____59055)) ->
                            let uu____59064 = eq_t a1 a2  in
                            eq_inj acc uu____59064) FStar_Syntax_Util.Equal)
                uu____58982))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____59105 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____59105
          then
            let uu____59108 =
              let uu____59109 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____59109  in
            eq_and uu____59108 (fun uu____59112  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____59119 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____59119
      | (Univ u1,Univ u2) ->
          let uu____59123 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____59123
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____59170 =
            let uu____59171 =
              let uu____59172 = t11 ()  in
              FStar_Pervasives_Native.fst uu____59172  in
            let uu____59177 =
              let uu____59178 = t21 ()  in
              FStar_Pervasives_Native.fst uu____59178  in
            eq_t uu____59171 uu____59177  in
          eq_and uu____59170
            (fun uu____59186  ->
               let uu____59187 =
                 let uu____59188 = mkAccuVar x  in r1 uu____59188  in
               let uu____59189 =
                 let uu____59190 = mkAccuVar x  in r2 uu____59190  in
               eq_t uu____59187 uu____59189)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____59191,uu____59192) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____59197,uu____59198) -> FStar_Syntax_Util.Unknown

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
          let uu____59279 = eq_arg x y  in
          eq_and uu____59279 (fun uu____59281  -> eq_args xs ys)
      | (uu____59282,uu____59283) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____59330) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____59335 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____59335
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____59364) ->
        let uu____59409 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____59420 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____59409 uu____59420
    | Accu (a,l) ->
        let uu____59437 =
          let uu____59439 = atom_to_string a  in
          let uu____59441 =
            let uu____59443 =
              let uu____59445 =
                let uu____59447 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____59447  in
              FStar_String.op_Hat uu____59445 ")"  in
            FStar_String.op_Hat ") (" uu____59443  in
          FStar_String.op_Hat uu____59439 uu____59441  in
        FStar_String.op_Hat "Accu (" uu____59437
    | Construct (fv,us,l) ->
        let uu____59485 =
          let uu____59487 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____59489 =
            let uu____59491 =
              let uu____59493 =
                let uu____59495 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____59495  in
              let uu____59501 =
                let uu____59503 =
                  let uu____59505 =
                    let uu____59507 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____59507  in
                  FStar_String.op_Hat uu____59505 "]"  in
                FStar_String.op_Hat "] [" uu____59503  in
              FStar_String.op_Hat uu____59493 uu____59501  in
            FStar_String.op_Hat ") [" uu____59491  in
          FStar_String.op_Hat uu____59487 uu____59489  in
        FStar_String.op_Hat "Construct (" uu____59485
    | FV (fv,us,l) ->
        let uu____59546 =
          let uu____59548 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____59550 =
            let uu____59552 =
              let uu____59554 =
                let uu____59556 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____59556  in
              let uu____59562 =
                let uu____59564 =
                  let uu____59566 =
                    let uu____59568 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____59568  in
                  FStar_String.op_Hat uu____59566 "]"  in
                FStar_String.op_Hat "] [" uu____59564  in
              FStar_String.op_Hat uu____59554 uu____59562  in
            FStar_String.op_Hat ") [" uu____59552  in
          FStar_String.op_Hat uu____59548 uu____59550  in
        FStar_String.op_Hat "FV (" uu____59546
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____59590 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____59590
    | Type_t u ->
        let uu____59594 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____59594
    | Arrow uu____59597 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____59643 = t ()  in FStar_Pervasives_Native.fst uu____59643
           in
        let uu____59648 =
          let uu____59650 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____59652 =
            let uu____59654 =
              let uu____59656 = t_to_string t1  in
              let uu____59658 =
                let uu____59660 =
                  let uu____59662 =
                    let uu____59664 =
                      let uu____59665 = mkAccuVar x1  in f uu____59665  in
                    t_to_string uu____59664  in
                  FStar_String.op_Hat uu____59662 "}"  in
                FStar_String.op_Hat "{" uu____59660  in
              FStar_String.op_Hat uu____59656 uu____59658  in
            FStar_String.op_Hat ":" uu____59654  in
          FStar_String.op_Hat uu____59650 uu____59652  in
        FStar_String.op_Hat "Refinement " uu____59648
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____59672 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____59672
    | Quote uu____59675 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____59682) ->
        let uu____59699 =
          let uu____59701 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____59701  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____59699
    | Lazy (FStar_Util.Inr (uu____59703,et),uu____59705) ->
        let uu____59722 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____59722
    | Rec
        (uu____59725,uu____59726,l,uu____59728,uu____59729,uu____59730,uu____59731)
        ->
        let uu____59776 =
          let uu____59778 =
            let uu____59780 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____59780  in
          FStar_String.op_Hat uu____59778 ")"  in
        FStar_String.op_Hat "Rec (" uu____59776

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____59791 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____59791
    | Match (t,uu____59795,uu____59796) ->
        let uu____59819 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____59819

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____59823 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____59823 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____59830 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59830 (FStar_String.concat " ")

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
        let uu____60301 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____60301 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____60322 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____60322 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____60363  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____60378  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____60421 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____60421
         then
           let uu____60445 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____60445
         else ());
        (let uu____60450 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____60450
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____60484 = FStar_Dyn.mkdyn x  in (uu____60484, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____60512 'a .
    'Auu____60512 ->
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
              let uu____60563 = FStar_Common.force_thunk thunk1  in
              f uu____60563
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____60583 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____60583
              then
                let res =
                  let uu____60612 = FStar_Common.force_thunk thunk1  in
                  f uu____60612  in
                ((let uu____60614 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____60614
                  then
                    let uu____60638 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____60640 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____60638
                      uu____60640
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____60649 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____60649
                  then
                    let uu____60673 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____60673
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____60678 ->
              let aopt = f x  in
              ((let uu____60683 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____60683
                then
                  let uu____60707 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____60707
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
  let uu____60775 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____60775 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____60809 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____60814 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60809 uu____60814 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____60855 -> FStar_Pervasives_Native.None  in
  let uu____60857 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____60862 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60857 uu____60862 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____60904 -> FStar_Pervasives_Native.None  in
  let uu____60906 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____60911 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____60906 uu____60911 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____60953)) -> FStar_Pervasives_Native.Some s1
    | uu____60957 -> FStar_Pervasives_Native.None  in
  let uu____60959 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____60964 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____60959 uu____60964 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____60999 -> FStar_Pervasives_Native.None  in
  let uu____61000 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____61005 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____61000 uu____61005 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____61026 =
        let uu____61034 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____61034, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61026  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____61059  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____61060 =
                 let uu____61061 =
                   let uu____61066 = type_of ea  in as_iarg uu____61066  in
                 [uu____61061]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____61060
           | FStar_Pervasives_Native.Some x ->
               let uu____61076 =
                 let uu____61077 =
                   let uu____61082 = embed ea cb x  in as_arg uu____61082  in
                 let uu____61083 =
                   let uu____61090 =
                     let uu____61095 = type_of ea  in as_iarg uu____61095  in
                   [uu____61090]  in
                 uu____61077 :: uu____61083  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____61076)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____61162)::uu____61163::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____61190 = unembed ea cb a  in
               FStar_Util.bind_opt uu____61190
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____61199 -> FStar_Pervasives_Native.None)
       in
    let uu____61202 =
      let uu____61203 =
        let uu____61204 = let uu____61209 = type_of ea  in as_arg uu____61209
           in
        [uu____61204]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____61203
       in
    mk_emb em un uu____61202 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____61256 =
          let uu____61264 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____61264, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____61256  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____61295  ->
             let uu____61296 =
               let uu____61297 =
                 let uu____61302 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____61302  in
               let uu____61303 =
                 let uu____61310 =
                   let uu____61315 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____61315  in
                 let uu____61316 =
                   let uu____61323 =
                     let uu____61328 = type_of eb  in as_iarg uu____61328  in
                   let uu____61329 =
                     let uu____61336 =
                       let uu____61341 = type_of ea  in as_iarg uu____61341
                        in
                     [uu____61336]  in
                   uu____61323 :: uu____61329  in
                 uu____61310 :: uu____61316  in
               uu____61297 :: uu____61303  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____61296)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____61409)::(a,uu____61411)::uu____61412::uu____61413::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____61452 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____61452
                   (fun a1  ->
                      let uu____61462 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____61462
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____61475 -> FStar_Pervasives_Native.None)
         in
      let uu____61480 =
        let uu____61481 =
          let uu____61482 =
            let uu____61487 = type_of eb  in as_arg uu____61487  in
          let uu____61488 =
            let uu____61495 =
              let uu____61500 = type_of ea  in as_arg uu____61500  in
            [uu____61495]  in
          uu____61482 :: uu____61488  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____61481
         in
      mk_emb em un uu____61480 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____61553 =
          let uu____61561 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____61561, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____61553  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____61593  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____61595 =
                   let uu____61596 =
                     let uu____61601 = embed ea cb a  in as_arg uu____61601
                      in
                   let uu____61602 =
                     let uu____61609 =
                       let uu____61614 = type_of eb  in as_iarg uu____61614
                        in
                     let uu____61615 =
                       let uu____61622 =
                         let uu____61627 = type_of ea  in as_iarg uu____61627
                          in
                       [uu____61622]  in
                     uu____61609 :: uu____61615  in
                   uu____61596 :: uu____61602  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____61595
             | FStar_Util.Inr b ->
                 let uu____61645 =
                   let uu____61646 =
                     let uu____61651 = embed eb cb b  in as_arg uu____61651
                      in
                   let uu____61652 =
                     let uu____61659 =
                       let uu____61664 = type_of eb  in as_iarg uu____61664
                        in
                     let uu____61665 =
                       let uu____61672 =
                         let uu____61677 = type_of ea  in as_iarg uu____61677
                          in
                       [uu____61672]  in
                     uu____61659 :: uu____61665  in
                   uu____61646 :: uu____61652  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____61645)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____61739)::uu____61740::uu____61741::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____61776 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____61776
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____61792)::uu____61793::uu____61794::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____61829 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____61829
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____61842 -> FStar_Pervasives_Native.None)
         in
      let uu____61847 =
        let uu____61848 =
          let uu____61849 =
            let uu____61854 = type_of eb  in as_arg uu____61854  in
          let uu____61855 =
            let uu____61862 =
              let uu____61867 = type_of ea  in as_arg uu____61867  in
            [uu____61862]  in
          uu____61849 :: uu____61855  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____61848
         in
      mk_emb em un uu____61847 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____61916 -> FStar_Pervasives_Native.None  in
  let uu____61917 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____61922 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____61917 uu____61922 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____61943 =
        let uu____61951 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61951, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61943  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____61978  ->
           let typ = let uu____61980 = type_of ea  in as_iarg uu____61980  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____62001 =
               let uu____62002 = as_arg tl1  in
               let uu____62007 =
                 let uu____62014 =
                   let uu____62019 = embed ea cb hd1  in as_arg uu____62019
                    in
                 [uu____62014; typ]  in
               uu____62002 :: uu____62007  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____62001
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____62067,uu____62068) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____62088,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____62091,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____62092))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____62120 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____62120
                 (fun hd2  ->
                    let uu____62128 = un cb tl1  in
                    FStar_Util.bind_opt uu____62128
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____62144,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____62169 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____62169
                 (fun hd2  ->
                    let uu____62177 = un cb tl1  in
                    FStar_Util.bind_opt uu____62177
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____62192 -> FStar_Pervasives_Native.None)
       in
    let uu____62195 =
      let uu____62196 =
        let uu____62197 = let uu____62202 = type_of ea  in as_arg uu____62202
           in
        [uu____62197]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____62196
       in
    mk_emb em un uu____62195 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____62275  ->
             Lam
               ((fun tas  ->
                   let uu____62305 =
                     let uu____62308 = FStar_List.hd tas  in
                     unembed ea cb uu____62308  in
                   match uu____62305 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____62310 = f a  in embed eb cb uu____62310
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____62323  ->
                     let uu____62326 = type_of eb  in as_arg uu____62326)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____62384 =
                 let uu____62387 =
                   let uu____62388 =
                     let uu____62389 =
                       let uu____62394 = embed ea cb x  in as_arg uu____62394
                        in
                     [uu____62389]  in
                   cb.iapp lam1 uu____62388  in
                 unembed eb cb uu____62387  in
               match uu____62384 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____62408 =
        let uu____62409 = type_of ea  in
        let uu____62410 =
          let uu____62411 = type_of eb  in as_iarg uu____62411  in
        make_arrow1 uu____62409 uu____62410  in
      mk_emb em un uu____62408 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____62429 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____62429 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____62434 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____62434 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____62439 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____62439 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____62444 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____62444 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____62449 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____62449 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____62454 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____62454 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____62459 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____62459 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____62464 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____62464 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____62469 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____62469 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____62478 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____62479 =
          let uu____62480 =
            let uu____62485 =
              let uu____62486 = e_list e_string  in embed uu____62486 cb l
               in
            as_arg uu____62485  in
          [uu____62480]  in
        mkFV uu____62478 [] uu____62479
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____62508 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____62509 =
          let uu____62510 =
            let uu____62515 =
              let uu____62516 = e_list e_string  in embed uu____62516 cb l
               in
            as_arg uu____62515  in
          [uu____62510]  in
        mkFV uu____62508 [] uu____62509
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____62538 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____62539 =
          let uu____62540 =
            let uu____62545 =
              let uu____62546 = e_list e_string  in embed uu____62546 cb l
               in
            as_arg uu____62545  in
          [uu____62540]  in
        mkFV uu____62538 [] uu____62539
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____62580,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____62596,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____62612,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____62628,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____62644,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____62660,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____62676,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____62692,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____62708,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____62724,(l,uu____62726)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____62745 =
          let uu____62751 = e_list e_string  in unembed uu____62751 cb l  in
        FStar_Util.bind_opt uu____62745
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62771  -> FStar_Pervasives_Native.Some _62771)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____62773,(l,uu____62775)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____62794 =
          let uu____62800 = e_list e_string  in unembed uu____62800 cb l  in
        FStar_Util.bind_opt uu____62794
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62820  -> FStar_Pervasives_Native.Some _62820)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____62822,(l,uu____62824)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____62843 =
          let uu____62849 = e_list e_string  in unembed uu____62849 cb l  in
        FStar_Util.bind_opt uu____62843
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62869  -> FStar_Pervasives_Native.Some _62869)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____62870 ->
        ((let uu____62872 =
            let uu____62878 =
              let uu____62880 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____62880
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62878)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62872);
         FStar_Pervasives_Native.None)
     in
  let uu____62884 =
    let uu____62885 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____62885 [] []  in
  let uu____62890 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____62884 uu____62890 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____62899  -> failwith "bogus_cbs translate")
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
      let uu____62976 =
        let uu____62985 = e_list e  in unembed uu____62985 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62976
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____63007  ->
    match uu____63007 with
    | (a,uu____63015) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____63030)::[]) when
             let uu____63047 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____63047 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____63054 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____63097 = let uu____63104 = as_arg c  in [uu____63104]  in
      int_to_t2 uu____63097
  
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
          let uu____63158 = f a  in FStar_Pervasives_Native.Some uu____63158
      | uu____63159 -> FStar_Pervasives_Native.None
  
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
          let uu____63213 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____63213
      | uu____63214 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____63258 = FStar_List.map as_a args  in
        lift_unary f uu____63258
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____63313 = FStar_List.map as_a args  in
        lift_binary f uu____63313
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____63343 = f x  in embed e_int bogus_cbs uu____63343)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____63370 = f x y  in embed e_int bogus_cbs uu____63370)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____63396 = f x  in embed e_bool bogus_cbs uu____63396)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____63434 = f x y  in embed e_bool bogus_cbs uu____63434)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____63472 = f x y  in embed e_string bogus_cbs uu____63472)
  
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
                let uu____63577 =
                  let uu____63586 = as_a a  in
                  let uu____63589 = as_b b  in (uu____63586, uu____63589)  in
                (match uu____63577 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____63604 =
                       let uu____63605 = f a1 b1  in embed_c uu____63605  in
                     FStar_Pervasives_Native.Some uu____63604
                 | uu____63606 -> FStar_Pervasives_Native.None)
            | uu____63615 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____63624 = e_list e_char  in
    let uu____63631 = FStar_String.list_of_string s  in
    embed uu____63624 bogus_cbs uu____63631
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____63670 =
        let uu____63671 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____63671  in
      embed e_int bogus_cbs uu____63670
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63705 = arg_as_string a1  in
        (match uu____63705 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63714 = arg_as_list e_string a2  in
             (match uu____63714 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____63732 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____63732
              | uu____63734 -> FStar_Pervasives_Native.None)
         | uu____63740 -> FStar_Pervasives_Native.None)
    | uu____63744 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____63751 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____63751
  
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
      | (_typ,uu____63813)::(a1,uu____63815)::(a2,uu____63817)::[] ->
          let uu____63834 = eq_t a1 a2  in
          (match uu____63834 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____63843 -> FStar_Pervasives_Native.None)
      | uu____63844 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63859)::(_typ,uu____63861)::(a1,uu____63863)::(a2,uu____63865)::[]
        ->
        let uu____63886 = eq_t a1 a2  in
        (match uu____63886 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63889 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63889
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63892 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63892
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63895 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63910)::(_v,uu____63912)::(t1,uu____63914)::(t2,uu____63916)::
        (a1,uu____63918)::(a2,uu____63920)::[] ->
        let uu____63949 =
          let uu____63950 = eq_t t1 t2  in
          let uu____63951 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____63950 uu____63951  in
        (match uu____63949 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63954 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63954
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63957 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63957
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63960 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____63979 =
        let uu____63981 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____63981  in
      failwith uu____63979
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____63997)::[] ->
        let uu____64006 = unembed e_range bogus_cbs a1  in
        (match uu____64006 with
         | FStar_Pervasives_Native.Some r ->
             let uu____64012 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____64012
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____64013 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____64049 = arg_as_list e_char a1  in
        (match uu____64049 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____64065 = arg_as_string a2  in
             (match uu____64065 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____64078 =
                    let uu____64079 = e_list e_string  in
                    embed uu____64079 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____64078
              | uu____64089 -> FStar_Pervasives_Native.None)
         | uu____64093 -> FStar_Pervasives_Native.None)
    | uu____64099 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____64132 =
          let uu____64142 = arg_as_string a1  in
          let uu____64146 = arg_as_int a2  in (uu____64142, uu____64146)  in
        (match uu____64132 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_64170  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____64175 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____64175) ()
              with | uu___1496_64178 -> FStar_Pervasives_Native.None)
         | uu____64181 -> FStar_Pervasives_Native.None)
    | uu____64191 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____64224 =
          let uu____64235 = arg_as_string a1  in
          let uu____64239 = arg_as_char a2  in (uu____64235, uu____64239)  in
        (match uu____64224 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_64268  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____64272 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____64272) ()
              with | uu___1514_64274 -> FStar_Pervasives_Native.None)
         | uu____64277 -> FStar_Pervasives_Native.None)
    | uu____64288 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____64330 =
          let uu____64344 = arg_as_string a1  in
          let uu____64348 = arg_as_int a2  in
          let uu____64351 = arg_as_int a3  in
          (uu____64344, uu____64348, uu____64351)  in
        (match uu____64330 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_64384  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____64389 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____64389) ()
              with | uu___1537_64392 -> FStar_Pervasives_Native.None)
         | uu____64395 -> FStar_Pervasives_Native.None)
    | uu____64409 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____64469 =
          let uu____64491 = arg_as_string fn  in
          let uu____64495 = arg_as_int from_line  in
          let uu____64498 = arg_as_int from_col  in
          let uu____64501 = arg_as_int to_line  in
          let uu____64504 = arg_as_int to_col  in
          (uu____64491, uu____64495, uu____64498, uu____64501, uu____64504)
           in
        (match uu____64469 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____64539 =
                 let uu____64540 = FStar_BigInt.to_int_fs from_l  in
                 let uu____64542 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____64540 uu____64542  in
               let uu____64544 =
                 let uu____64545 = FStar_BigInt.to_int_fs to_l  in
                 let uu____64547 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____64545 uu____64547  in
               FStar_Range.mk_range fn1 uu____64539 uu____64544  in
             let uu____64549 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____64549
         | uu____64550 -> FStar_Pervasives_Native.None)
    | uu____64572 -> FStar_Pervasives_Native.None
  
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
                let uu____64662 = FStar_List.splitAt n_tvars args  in
                match uu____64662 with
                | (_tvar_args,rest_args) ->
                    let uu____64711 = FStar_List.hd rest_args  in
                    (match uu____64711 with
                     | (x,uu____64723) ->
                         let uu____64724 = unembed ea cb x  in
                         FStar_Util.map_opt uu____64724
                           (fun x1  ->
                              let uu____64730 = f x1  in
                              embed eb cb uu____64730))
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
                  let uu____64839 = FStar_List.splitAt n_tvars args  in
                  match uu____64839 with
                  | (_tvar_args,rest_args) ->
                      let uu____64888 = FStar_List.hd rest_args  in
                      (match uu____64888 with
                       | (x,uu____64900) ->
                           let uu____64901 =
                             let uu____64906 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64906  in
                           (match uu____64901 with
                            | (y,uu____64924) ->
                                let uu____64925 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____64925
                                  (fun x1  ->
                                     let uu____64931 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____64931
                                       (fun y1  ->
                                          let uu____64937 =
                                            let uu____64938 = f x1 y1  in
                                            embed ec cb uu____64938  in
                                          FStar_Pervasives_Native.Some
                                            uu____64937))))
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
                    let uu____65066 = FStar_List.splitAt n_tvars args  in
                    match uu____65066 with
                    | (_tvar_args,rest_args) ->
                        let uu____65115 = FStar_List.hd rest_args  in
                        (match uu____65115 with
                         | (x,uu____65127) ->
                             let uu____65128 =
                               let uu____65133 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____65133  in
                             (match uu____65128 with
                              | (y,uu____65151) ->
                                  let uu____65152 =
                                    let uu____65157 =
                                      let uu____65164 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____65164  in
                                    FStar_List.hd uu____65157  in
                                  (match uu____65152 with
                                   | (z,uu____65186) ->
                                       let uu____65187 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____65187
                                         (fun x1  ->
                                            let uu____65193 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____65193
                                              (fun y1  ->
                                                 let uu____65199 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____65199
                                                   (fun z1  ->
                                                      let uu____65205 =
                                                        let uu____65206 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____65206
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____65205))))))
                     in
                  f_wrapped
  