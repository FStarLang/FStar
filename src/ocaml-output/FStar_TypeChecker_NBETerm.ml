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
    match projectee with | Unit  -> true | uu____60749 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____60762 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____60785 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____60810 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____60846 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____60869 -> false
  
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
    match projectee with | Var _0 -> true | uu____61252 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____61289 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____61390 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____61510 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____61574 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____61650 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____61712 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____61732 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____61752 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____61771 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____61803 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____61897 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____61959 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____61983 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____62029 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____62127 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____62261 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____62305 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____62343 -> false
  
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
    match projectee with | TOTAL  -> true | uu____62473 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____62484 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____62495 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____62506 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____62517 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____62528 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____62539 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____62550 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____62561 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____62573 -> false
  
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
    match trm with | Accu uu____62650 -> true | uu____62662 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____62672,uu____62673) -> false
    | uu____62687 -> true
  
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
  fun uu___516_62823  ->
    if uu___516_62823
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_62834  ->
    if uu___517_62834
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
      | (FStar_Syntax_Util.NotEqual ,uu____62850) ->
          FStar_Syntax_Util.NotEqual
      | (uu____62851,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____62852) -> FStar_Syntax_Util.Unknown
      | (uu____62853,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____62870 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____62890),String (s2,uu____62892)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____62905,uu____62906) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____62942,Lam uu____62943) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____63032 = eq_atom a1 a2  in
          eq_and uu____63032 (fun uu____63034  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____63073 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63073
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____63089 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____63146  ->
                        match uu____63146 with
                        | ((a1,uu____63160),(a2,uu____63162)) ->
                            let uu____63171 = eq_t a1 a2  in
                            eq_inj acc uu____63171) FStar_Syntax_Util.Equal)
                uu____63089))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____63212 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63212
          then
            let uu____63215 =
              let uu____63216 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____63216  in
            eq_and uu____63215 (fun uu____63219  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____63226 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63226
      | (Univ u1,Univ u2) ->
          let uu____63230 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63230
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____63277 =
            let uu____63278 =
              let uu____63279 = t11 ()  in
              FStar_Pervasives_Native.fst uu____63279  in
            let uu____63284 =
              let uu____63285 = t21 ()  in
              FStar_Pervasives_Native.fst uu____63285  in
            eq_t uu____63278 uu____63284  in
          eq_and uu____63277
            (fun uu____63293  ->
               let uu____63294 =
                 let uu____63295 = mkAccuVar x  in r1 uu____63295  in
               let uu____63296 =
                 let uu____63297 = mkAccuVar x  in r2 uu____63297  in
               eq_t uu____63294 uu____63296)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____63298,uu____63299) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____63304,uu____63305) -> FStar_Syntax_Util.Unknown

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
          let uu____63386 = eq_arg x y  in
          eq_and uu____63386 (fun uu____63388  -> eq_args xs ys)
      | (uu____63389,uu____63390) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____63437) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____63442 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____63442
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____63471) ->
        let uu____63516 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____63527 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____63516 uu____63527
    | Accu (a,l) ->
        let uu____63544 =
          let uu____63546 = atom_to_string a  in
          let uu____63548 =
            let uu____63550 =
              let uu____63552 =
                let uu____63554 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____63554  in
              FStar_String.op_Hat uu____63552 ")"  in
            FStar_String.op_Hat ") (" uu____63550  in
          FStar_String.op_Hat uu____63546 uu____63548  in
        FStar_String.op_Hat "Accu (" uu____63544
    | Construct (fv,us,l) ->
        let uu____63592 =
          let uu____63594 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63596 =
            let uu____63598 =
              let uu____63600 =
                let uu____63602 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63602  in
              let uu____63608 =
                let uu____63610 =
                  let uu____63612 =
                    let uu____63614 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63614  in
                  FStar_String.op_Hat uu____63612 "]"  in
                FStar_String.op_Hat "] [" uu____63610  in
              FStar_String.op_Hat uu____63600 uu____63608  in
            FStar_String.op_Hat ") [" uu____63598  in
          FStar_String.op_Hat uu____63594 uu____63596  in
        FStar_String.op_Hat "Construct (" uu____63592
    | FV (fv,us,l) ->
        let uu____63653 =
          let uu____63655 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63657 =
            let uu____63659 =
              let uu____63661 =
                let uu____63663 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63663  in
              let uu____63669 =
                let uu____63671 =
                  let uu____63673 =
                    let uu____63675 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63675  in
                  FStar_String.op_Hat uu____63673 "]"  in
                FStar_String.op_Hat "] [" uu____63671  in
              FStar_String.op_Hat uu____63661 uu____63669  in
            FStar_String.op_Hat ") [" uu____63659  in
          FStar_String.op_Hat uu____63655 uu____63657  in
        FStar_String.op_Hat "FV (" uu____63653
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____63697 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____63697
    | Type_t u ->
        let uu____63701 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____63701
    | Arrow uu____63704 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____63750 = t ()  in FStar_Pervasives_Native.fst uu____63750
           in
        let uu____63755 =
          let uu____63757 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____63759 =
            let uu____63761 =
              let uu____63763 = t_to_string t1  in
              let uu____63765 =
                let uu____63767 =
                  let uu____63769 =
                    let uu____63771 =
                      let uu____63772 = mkAccuVar x1  in f uu____63772  in
                    t_to_string uu____63771  in
                  FStar_String.op_Hat uu____63769 "}"  in
                FStar_String.op_Hat "{" uu____63767  in
              FStar_String.op_Hat uu____63763 uu____63765  in
            FStar_String.op_Hat ":" uu____63761  in
          FStar_String.op_Hat uu____63757 uu____63759  in
        FStar_String.op_Hat "Refinement " uu____63755
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____63779 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____63779
    | Quote uu____63782 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____63789) ->
        let uu____63806 =
          let uu____63808 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____63808  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____63806
    | Lazy (FStar_Util.Inr (uu____63810,et),uu____63812) ->
        let uu____63829 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____63829
    | Rec
        (uu____63832,uu____63833,l,uu____63835,uu____63836,uu____63837,uu____63838)
        ->
        let uu____63883 =
          let uu____63885 =
            let uu____63887 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____63887  in
          FStar_String.op_Hat uu____63885 ")"  in
        FStar_String.op_Hat "Rec (" uu____63883

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____63898 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____63898
    | Match (t,uu____63902,uu____63903) ->
        let uu____63926 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____63926

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____63930 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____63930 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____63937 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____63937 (FStar_String.concat " ")

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
        let uu____64408 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____64408 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____64429 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____64429 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____64470  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____64485  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____64528 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____64528
         then
           let uu____64552 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____64552
         else ());
        (let uu____64557 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____64557
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____64591 = FStar_Dyn.mkdyn x  in (uu____64591, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____64659 'a .
    'Auu____64659 ->
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
              let uu____64710 = FStar_Common.force_thunk thunk1  in
              f uu____64710
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____64770 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____64770
              then
                let res =
                  let uu____64799 = FStar_Common.force_thunk thunk1  in
                  f uu____64799  in
                ((let uu____64841 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64841
                  then
                    let uu____64865 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____64867 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____64865
                      uu____64867
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____64876 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64876
                  then
                    let uu____64900 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____64900
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____64905 ->
              let aopt = f x  in
              ((let uu____64910 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____64910
                then
                  let uu____64934 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____64934
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
  let uu____65002 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____65002 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____65036 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____65041 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____65036 uu____65041 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____65082 -> FStar_Pervasives_Native.None  in
  let uu____65084 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____65089 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____65084 uu____65089 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____65131 -> FStar_Pervasives_Native.None  in
  let uu____65133 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____65138 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____65133 uu____65138 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____65180)) -> FStar_Pervasives_Native.Some s1
    | uu____65184 -> FStar_Pervasives_Native.None  in
  let uu____65186 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____65191 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____65186 uu____65191 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____65226 -> FStar_Pervasives_Native.None  in
  let uu____65227 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____65232 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____65227 uu____65232 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____65253 =
        let uu____65261 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____65261, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____65253  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____65286  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____65287 =
                 let uu____65288 =
                   let uu____65293 = type_of ea  in as_iarg uu____65293  in
                 [uu____65288]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65287
           | FStar_Pervasives_Native.Some x ->
               let uu____65303 =
                 let uu____65304 =
                   let uu____65309 = embed ea cb x  in as_arg uu____65309  in
                 let uu____65310 =
                   let uu____65317 =
                     let uu____65322 = type_of ea  in as_iarg uu____65322  in
                   [uu____65317]  in
                 uu____65304 :: uu____65310  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65303)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____65389)::uu____65390::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____65417 = unembed ea cb a  in
               FStar_Util.bind_opt uu____65417
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____65426 -> FStar_Pervasives_Native.None)
       in
    let uu____65429 =
      let uu____65430 =
        let uu____65431 = let uu____65436 = type_of ea  in as_arg uu____65436
           in
        [uu____65431]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____65430
       in
    mk_emb em un uu____65429 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65483 =
          let uu____65491 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____65491, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65483  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____65522  ->
             let uu____65523 =
               let uu____65524 =
                 let uu____65529 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____65529  in
               let uu____65530 =
                 let uu____65537 =
                   let uu____65542 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____65542  in
                 let uu____65543 =
                   let uu____65550 =
                     let uu____65555 = type_of eb  in as_iarg uu____65555  in
                   let uu____65556 =
                     let uu____65563 =
                       let uu____65568 = type_of ea  in as_iarg uu____65568
                        in
                     [uu____65563]  in
                   uu____65550 :: uu____65556  in
                 uu____65537 :: uu____65543  in
               uu____65524 :: uu____65530  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____65523)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____65636)::(a,uu____65638)::uu____65639::uu____65640::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____65679 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65679
                   (fun a1  ->
                      let uu____65689 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____65689
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____65702 -> FStar_Pervasives_Native.None)
         in
      let uu____65707 =
        let uu____65708 =
          let uu____65709 =
            let uu____65714 = type_of eb  in as_arg uu____65714  in
          let uu____65715 =
            let uu____65722 =
              let uu____65727 = type_of ea  in as_arg uu____65727  in
            [uu____65722]  in
          uu____65709 :: uu____65715  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____65708
         in
      mk_emb em un uu____65707 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65780 =
          let uu____65788 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____65788, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65780  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____65820  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____65822 =
                   let uu____65823 =
                     let uu____65828 = embed ea cb a  in as_arg uu____65828
                      in
                   let uu____65829 =
                     let uu____65836 =
                       let uu____65841 = type_of eb  in as_iarg uu____65841
                        in
                     let uu____65842 =
                       let uu____65849 =
                         let uu____65854 = type_of ea  in as_iarg uu____65854
                          in
                       [uu____65849]  in
                     uu____65836 :: uu____65842  in
                   uu____65823 :: uu____65829  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65822
             | FStar_Util.Inr b ->
                 let uu____65872 =
                   let uu____65873 =
                     let uu____65878 = embed eb cb b  in as_arg uu____65878
                      in
                   let uu____65879 =
                     let uu____65886 =
                       let uu____65891 = type_of eb  in as_iarg uu____65891
                        in
                     let uu____65892 =
                       let uu____65899 =
                         let uu____65904 = type_of ea  in as_iarg uu____65904
                          in
                       [uu____65899]  in
                     uu____65886 :: uu____65892  in
                   uu____65873 :: uu____65879  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65872)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____65966)::uu____65967::uu____65968::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____66003 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____66003
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____66019)::uu____66020::uu____66021::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____66056 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____66056
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____66069 -> FStar_Pervasives_Native.None)
         in
      let uu____66074 =
        let uu____66075 =
          let uu____66076 =
            let uu____66081 = type_of eb  in as_arg uu____66081  in
          let uu____66082 =
            let uu____66089 =
              let uu____66094 = type_of ea  in as_arg uu____66094  in
            [uu____66089]  in
          uu____66076 :: uu____66082  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____66075
         in
      mk_emb em un uu____66074 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____66143 -> FStar_Pervasives_Native.None  in
  let uu____66144 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____66149 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____66144 uu____66149 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____66170 =
        let uu____66178 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____66178, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____66170  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____66205  ->
           let typ = let uu____66207 = type_of ea  in as_iarg uu____66207  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____66228 =
               let uu____66229 = as_arg tl1  in
               let uu____66234 =
                 let uu____66241 =
                   let uu____66246 = embed ea cb hd1  in as_arg uu____66246
                    in
                 [uu____66241; typ]  in
               uu____66229 :: uu____66234  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____66228
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____66294,uu____66295) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____66315,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____66318,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____66319))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66347 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66347
                 (fun hd2  ->
                    let uu____66355 = un cb tl1  in
                    FStar_Util.bind_opt uu____66355
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____66371,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66396 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66396
                 (fun hd2  ->
                    let uu____66404 = un cb tl1  in
                    FStar_Util.bind_opt uu____66404
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____66419 -> FStar_Pervasives_Native.None)
       in
    let uu____66422 =
      let uu____66423 =
        let uu____66424 = let uu____66429 = type_of ea  in as_arg uu____66429
           in
        [uu____66424]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____66423
       in
    mk_emb em un uu____66422 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____66502  ->
             Lam
               ((fun tas  ->
                   let uu____66532 =
                     let uu____66535 = FStar_List.hd tas  in
                     unembed ea cb uu____66535  in
                   match uu____66532 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____66537 = f a  in embed eb cb uu____66537
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____66550  ->
                     let uu____66553 = type_of eb  in as_arg uu____66553)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____66611 =
                 let uu____66614 =
                   let uu____66615 =
                     let uu____66616 =
                       let uu____66621 = embed ea cb x  in as_arg uu____66621
                        in
                     [uu____66616]  in
                   cb.iapp lam1 uu____66615  in
                 unembed eb cb uu____66614  in
               match uu____66611 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____66635 =
        let uu____66636 = type_of ea  in
        let uu____66637 =
          let uu____66638 = type_of eb  in as_iarg uu____66638  in
        make_arrow1 uu____66636 uu____66637  in
      mk_emb em un uu____66635 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____66656 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66656 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____66661 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66661 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____66666 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66666 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____66671 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66671 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____66676 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66676 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____66681 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66681 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____66686 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66686 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____66691 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66691 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____66696 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66696 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____66705 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66706 =
          let uu____66707 =
            let uu____66712 =
              let uu____66713 = e_list e_string  in embed uu____66713 cb l
               in
            as_arg uu____66712  in
          [uu____66707]  in
        mkFV uu____66705 [] uu____66706
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____66735 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66736 =
          let uu____66737 =
            let uu____66742 =
              let uu____66743 = e_list e_string  in embed uu____66743 cb l
               in
            as_arg uu____66742  in
          [uu____66737]  in
        mkFV uu____66735 [] uu____66736
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____66765 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66766 =
          let uu____66767 =
            let uu____66772 =
              let uu____66773 = e_list e_string  in embed uu____66773 cb l
               in
            as_arg uu____66772  in
          [uu____66767]  in
        mkFV uu____66765 [] uu____66766
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____66807,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____66823,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____66839,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____66855,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____66871,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____66887,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____66903,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____66919,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____66935,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____66951,(l,uu____66953)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____66972 =
          let uu____66978 = e_list e_string  in unembed uu____66978 cb l  in
        FStar_Util.bind_opt uu____66972
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66998  -> FStar_Pervasives_Native.Some _66998)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____67000,(l,uu____67002)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____67021 =
          let uu____67027 = e_list e_string  in unembed uu____67027 cb l  in
        FStar_Util.bind_opt uu____67021
          (fun ss  ->
             FStar_All.pipe_left
               (fun _67047  -> FStar_Pervasives_Native.Some _67047)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____67049,(l,uu____67051)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____67070 =
          let uu____67076 = e_list e_string  in unembed uu____67076 cb l  in
        FStar_Util.bind_opt uu____67070
          (fun ss  ->
             FStar_All.pipe_left
               (fun _67096  -> FStar_Pervasives_Native.Some _67096)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____67097 ->
        ((let uu____67099 =
            let uu____67105 =
              let uu____67107 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____67107
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67105)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67099);
         FStar_Pervasives_Native.None)
     in
  let uu____67111 =
    let uu____67112 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____67112 [] []  in
  let uu____67117 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____67111 uu____67117 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____67126  -> failwith "bogus_cbs translate")
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
      let uu____67203 =
        let uu____67212 = e_list e  in unembed uu____67212 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67203
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____67234  ->
    match uu____67234 with
    | (a,uu____67242) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____67257)::[]) when
             let uu____67274 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____67274 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____67281 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____67324 = let uu____67331 = as_arg c  in [uu____67331]  in
      int_to_t2 uu____67324
  
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
          let uu____67385 = f a  in FStar_Pervasives_Native.Some uu____67385
      | uu____67386 -> FStar_Pervasives_Native.None
  
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
          let uu____67440 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____67440
      | uu____67441 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67485 = FStar_List.map as_a args  in
        lift_unary f uu____67485
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67540 = FStar_List.map as_a args  in
        lift_binary f uu____67540
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____67570 = f x  in embed e_int bogus_cbs uu____67570)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____67597 = f x y  in embed e_int bogus_cbs uu____67597)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____67623 = f x  in embed e_bool bogus_cbs uu____67623)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____67661 = f x y  in embed e_bool bogus_cbs uu____67661)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____67699 = f x y  in embed e_string bogus_cbs uu____67699)
  
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
                let uu____67804 =
                  let uu____67813 = as_a a  in
                  let uu____67816 = as_b b  in (uu____67813, uu____67816)  in
                (match uu____67804 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____67831 =
                       let uu____67832 = f a1 b1  in embed_c uu____67832  in
                     FStar_Pervasives_Native.Some uu____67831
                 | uu____67833 -> FStar_Pervasives_Native.None)
            | uu____67842 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____67851 = e_list e_char  in
    let uu____67858 = FStar_String.list_of_string s  in
    embed uu____67851 bogus_cbs uu____67858
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____67897 =
        let uu____67898 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____67898  in
      embed e_int bogus_cbs uu____67897
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____67932 = arg_as_string a1  in
        (match uu____67932 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____67941 = arg_as_list e_string a2  in
             (match uu____67941 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____67959 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____67959
              | uu____67961 -> FStar_Pervasives_Native.None)
         | uu____67967 -> FStar_Pervasives_Native.None)
    | uu____67971 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____67978 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____67978
  
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
      | (_typ,uu____68040)::(a1,uu____68042)::(a2,uu____68044)::[] ->
          let uu____68061 = eq_t a1 a2  in
          (match uu____68061 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____68070 -> FStar_Pervasives_Native.None)
      | uu____68071 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68086)::(_typ,uu____68088)::(a1,uu____68090)::(a2,uu____68092)::[]
        ->
        let uu____68113 = eq_t a1 a2  in
        (match uu____68113 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68116 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68116
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68119 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68119
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68122 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68137)::(_v,uu____68139)::(t1,uu____68141)::(t2,uu____68143)::
        (a1,uu____68145)::(a2,uu____68147)::[] ->
        let uu____68176 =
          let uu____68177 = eq_t t1 t2  in
          let uu____68178 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____68177 uu____68178  in
        (match uu____68176 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68181 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68181
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68184 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68184
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68187 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____68206 =
        let uu____68208 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____68208  in
      failwith uu____68206
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____68224)::[] ->
        let uu____68233 = unembed e_range bogus_cbs a1  in
        (match uu____68233 with
         | FStar_Pervasives_Native.Some r ->
             let uu____68239 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68239
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____68240 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68276 = arg_as_list e_char a1  in
        (match uu____68276 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68292 = arg_as_string a2  in
             (match uu____68292 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68305 =
                    let uu____68306 = e_list e_string  in
                    embed uu____68306 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____68305
              | uu____68316 -> FStar_Pervasives_Native.None)
         | uu____68320 -> FStar_Pervasives_Native.None)
    | uu____68326 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68359 =
          let uu____68369 = arg_as_string a1  in
          let uu____68373 = arg_as_int a2  in (uu____68369, uu____68373)  in
        (match uu____68359 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_68397  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68402 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68402) ()
              with | uu___1496_68405 -> FStar_Pervasives_Native.None)
         | uu____68408 -> FStar_Pervasives_Native.None)
    | uu____68418 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68451 =
          let uu____68462 = arg_as_string a1  in
          let uu____68466 = arg_as_char a2  in (uu____68462, uu____68466)  in
        (match uu____68451 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_68495  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68499 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68499) ()
              with | uu___1514_68501 -> FStar_Pervasives_Native.None)
         | uu____68504 -> FStar_Pervasives_Native.None)
    | uu____68515 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____68557 =
          let uu____68571 = arg_as_string a1  in
          let uu____68575 = arg_as_int a2  in
          let uu____68578 = arg_as_int a3  in
          (uu____68571, uu____68575, uu____68578)  in
        (match uu____68557 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_68611  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68616 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68616) ()
              with | uu___1537_68619 -> FStar_Pervasives_Native.None)
         | uu____68622 -> FStar_Pervasives_Native.None)
    | uu____68636 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68696 =
          let uu____68718 = arg_as_string fn  in
          let uu____68722 = arg_as_int from_line  in
          let uu____68725 = arg_as_int from_col  in
          let uu____68728 = arg_as_int to_line  in
          let uu____68731 = arg_as_int to_col  in
          (uu____68718, uu____68722, uu____68725, uu____68728, uu____68731)
           in
        (match uu____68696 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68766 =
                 let uu____68767 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68769 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68767 uu____68769  in
               let uu____68771 =
                 let uu____68772 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68774 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68772 uu____68774  in
               FStar_Range.mk_range fn1 uu____68766 uu____68771  in
             let uu____68776 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68776
         | uu____68777 -> FStar_Pervasives_Native.None)
    | uu____68799 -> FStar_Pervasives_Native.None
  
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
                let uu____68889 = FStar_List.splitAt n_tvars args  in
                match uu____68889 with
                | (_tvar_args,rest_args) ->
                    let uu____68938 = FStar_List.hd rest_args  in
                    (match uu____68938 with
                     | (x,uu____68950) ->
                         let uu____68951 = unembed ea cb x  in
                         FStar_Util.map_opt uu____68951
                           (fun x1  ->
                              let uu____68957 = f x1  in
                              embed eb cb uu____68957))
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
                  let uu____69066 = FStar_List.splitAt n_tvars args  in
                  match uu____69066 with
                  | (_tvar_args,rest_args) ->
                      let uu____69115 = FStar_List.hd rest_args  in
                      (match uu____69115 with
                       | (x,uu____69127) ->
                           let uu____69128 =
                             let uu____69133 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____69133  in
                           (match uu____69128 with
                            | (y,uu____69151) ->
                                let uu____69152 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____69152
                                  (fun x1  ->
                                     let uu____69158 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____69158
                                       (fun y1  ->
                                          let uu____69164 =
                                            let uu____69165 = f x1 y1  in
                                            embed ec cb uu____69165  in
                                          FStar_Pervasives_Native.Some
                                            uu____69164))))
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
                    let uu____69293 = FStar_List.splitAt n_tvars args  in
                    match uu____69293 with
                    | (_tvar_args,rest_args) ->
                        let uu____69342 = FStar_List.hd rest_args  in
                        (match uu____69342 with
                         | (x,uu____69354) ->
                             let uu____69355 =
                               let uu____69360 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____69360  in
                             (match uu____69355 with
                              | (y,uu____69378) ->
                                  let uu____69379 =
                                    let uu____69384 =
                                      let uu____69391 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____69391  in
                                    FStar_List.hd uu____69384  in
                                  (match uu____69379 with
                                   | (z,uu____69413) ->
                                       let uu____69414 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____69414
                                         (fun x1  ->
                                            let uu____69420 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____69420
                                              (fun y1  ->
                                                 let uu____69426 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____69426
                                                   (fun z1  ->
                                                      let uu____69432 =
                                                        let uu____69433 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____69433
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____69432))))))
                     in
                  f_wrapped
  