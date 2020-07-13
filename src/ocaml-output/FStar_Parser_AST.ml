open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let (uu___is_Un : level -> Prims.bool) =
  fun projectee -> match projectee with | Un -> true | uu____22 -> false
let (uu___is_Expr : level -> Prims.bool) =
  fun projectee -> match projectee with | Expr -> true | uu____28 -> false
let (uu___is_Type_level : level -> Prims.bool) =
  fun projectee ->
    match projectee with | Type_level -> true | uu____34 -> false
let (uu___is_Kind : level -> Prims.bool) =
  fun projectee -> match projectee with | Kind -> true | uu____40 -> false
let (uu___is_Formula : level -> Prims.bool) =
  fun projectee -> match projectee with | Formula -> true | uu____46 -> false
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let (uu___is_NoLetQualifier : let_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | NoLetQualifier -> true | uu____52 -> false
let (uu___is_Rec : let_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Rec -> true | uu____58 -> false
type quote_kind =
  | Static 
  | Dynamic 
let (uu___is_Static : quote_kind -> Prims.bool) =
  fun projectee -> match projectee with | Static -> true | uu____64 -> false
let (uu___is_Dynamic : quote_kind -> Prims.bool) =
  fun projectee -> match projectee with | Dynamic -> true | uu____70 -> false
type term' =
  | Wild 
  | Const of FStar_Const.sconst 
  | Op of (FStar_Ident.ident * term Prims.list) 
  | Tvar of FStar_Ident.ident 
  | Uvar of FStar_Ident.ident 
  | Var of FStar_Ident.lid 
  | Name of FStar_Ident.lid 
  | Projector of (FStar_Ident.lid * FStar_Ident.ident) 
  | Construct of (FStar_Ident.lid * (term * imp) Prims.list) 
  | Abs of (pattern Prims.list * term) 
  | App of (term * term * imp) 
  | Let of (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
  (pattern * term)) Prims.list * term) 
  | LetOpen of (FStar_Ident.lid * term) 
  | Seq of (term * term) 
  | Bind of (FStar_Ident.ident * term * term) 
  | If of (term * term * term) 
  | Match of (term * (pattern * term FStar_Pervasives_Native.option * term)
  Prims.list) 
  | TryWith of (term * (pattern * term FStar_Pervasives_Native.option * term)
  Prims.list) 
  | Ascribed of (term * term * term FStar_Pervasives_Native.option) 
  | Record of (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
  Prims.list) 
  | Project of (term * FStar_Ident.lid) 
  | Product of (binder Prims.list * term) 
  | Sum of ((binder, term) FStar_Util.either Prims.list * term) 
  | QForall of (binder Prims.list * (FStar_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
  | QExists of (binder Prims.list * (FStar_Ident.ident Prims.list * term
  Prims.list Prims.list) * term) 
  | Refine of (binder * term) 
  | NamedTyp of (FStar_Ident.ident * term) 
  | Paren of term 
  | Requires of (term * Prims.string FStar_Pervasives_Native.option) 
  | Ensures of (term * Prims.string FStar_Pervasives_Native.option) 
  | Labeled of (term * Prims.string * Prims.bool) 
  | Discrim of FStar_Ident.lid 
  | Attributes of term Prims.list 
  | Antiquote of term 
  | Quote of (term * quote_kind) 
  | VQuote of term 
  | CalcProof of (term * term * calc_step Prims.list) 
and term = {
  tm: term' ;
  range: FStar_Range.range ;
  level: level }
and calc_step =
  | CalcStep of (term * term * term) 
and binder' =
  | Variable of FStar_Ident.ident 
  | TVariable of FStar_Ident.ident 
  | Annotated of (FStar_Ident.ident * term) 
  | TAnnotated of (FStar_Ident.ident * term) 
  | NoName of term 
and binder =
  {
  b: binder' ;
  brange: FStar_Range.range ;
  blevel: level ;
  aqual: arg_qualifier FStar_Pervasives_Native.option }
and pattern' =
  | PatWild of arg_qualifier FStar_Pervasives_Native.option 
  | PatConst of FStar_Const.sconst 
  | PatApp of (pattern * pattern Prims.list) 
  | PatVar of (FStar_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option) 
  | PatName of FStar_Ident.lid 
  | PatTvar of (FStar_Ident.ident * arg_qualifier
  FStar_Pervasives_Native.option) 
  | PatList of pattern Prims.list 
  | PatTuple of (pattern Prims.list * Prims.bool) 
  | PatRecord of (FStar_Ident.lid * pattern) Prims.list 
  | PatAscribed of (pattern * (term * term FStar_Pervasives_Native.option)) 
  | PatOr of pattern Prims.list 
  | PatOp of FStar_Ident.ident 
and pattern = {
  pat: pattern' ;
  prange: FStar_Range.range }
and arg_qualifier =
  | Implicit 
  | Equality 
  | Meta of arg_qualifier_meta_t 
and arg_qualifier_meta_t =
  | Arg_qualifier_meta_tac of term 
  | Arg_qualifier_meta_attr of term 
and imp =
  | FsTypApp 
  | Hash 
  | UnivApp 
  | HashBrace of term 
  | Infix 
  | Nothing 
let (uu___is_Wild : term' -> Prims.bool) =
  fun projectee -> match projectee with | Wild -> true | uu____689 -> false
let (uu___is_Const : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____696 -> false
let (__proj__Const__item___0 : term' -> FStar_Const.sconst) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee -> match projectee with | Op _0 -> true | uu____715 -> false
let (__proj__Op__item___0 : term' -> (FStar_Ident.ident * term Prims.list)) =
  fun projectee -> match projectee with | Op _0 -> _0
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tvar _0 -> true | uu____746 -> false
let (__proj__Tvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Tvar _0 -> _0
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Uvar _0 -> true | uu____759 -> false
let (__proj__Uvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Uvar _0 -> _0
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu____772 -> false
let (__proj__Var__item___0 : term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Name _0 -> true | uu____785 -> false
let (__proj__Name__item___0 : term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Projector _0 -> true | uu____802 -> false
let (__proj__Projector__item___0 :
  term' -> (FStar_Ident.lid * FStar_Ident.ident)) =
  fun projectee -> match projectee with | Projector _0 -> _0
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Construct _0 -> true | uu____837 -> false
let (__proj__Construct__item___0 :
  term' -> (FStar_Ident.lid * (term * imp) Prims.list)) =
  fun projectee -> match projectee with | Construct _0 -> _0
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee -> match projectee with | Abs _0 -> true | uu____886 -> false
let (__proj__Abs__item___0 : term' -> (pattern Prims.list * term)) =
  fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : term' -> Prims.bool) =
  fun projectee -> match projectee with | App _0 -> true | uu____923 -> false
let (__proj__App__item___0 : term' -> (term * term * imp)) =
  fun projectee -> match projectee with | App _0 -> _0
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee -> match projectee with | Let _0 -> true | uu____974 -> false
let (__proj__Let__item___0 :
  term' ->
    (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
      (pattern * term)) Prims.list * term))
  = fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | LetOpen _0 -> true | uu____1051 -> false
let (__proj__LetOpen__item___0 : term' -> (FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | LetOpen _0 -> _0
let (uu___is_Seq : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Seq _0 -> true | uu____1080 -> false
let (__proj__Seq__item___0 : term' -> (term * term)) =
  fun projectee -> match projectee with | Seq _0 -> _0
let (uu___is_Bind : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Bind _0 -> true | uu____1111 -> false
let (__proj__Bind__item___0 : term' -> (FStar_Ident.ident * term * term)) =
  fun projectee -> match projectee with | Bind _0 -> _0
let (uu___is_If : term' -> Prims.bool) =
  fun projectee -> match projectee with | If _0 -> true | uu____1148 -> false
let (__proj__If__item___0 : term' -> (term * term * term)) =
  fun projectee -> match projectee with | If _0 -> _0
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Match _0 -> true | uu____1193 -> false
let (__proj__Match__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_TryWith : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | TryWith _0 -> true | uu____1262 -> false
let (__proj__TryWith__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee -> match projectee with | TryWith _0 -> _0
let (uu___is_Ascribed : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Ascribed _0 -> true | uu____1325 -> false
let (__proj__Ascribed__item___0 :
  term' -> (term * term * term FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Ascribed _0 -> _0
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Record _0 -> true | uu____1374 -> false
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
      Prims.list))
  = fun projectee -> match projectee with | Record _0 -> _0
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Project _0 -> true | uu____1427 -> false
let (__proj__Project__item___0 : term' -> (term * FStar_Ident.lid)) =
  fun projectee -> match projectee with | Project _0 -> _0
let (uu___is_Product : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Product _0 -> true | uu____1458 -> false
let (__proj__Product__item___0 : term' -> (binder Prims.list * term)) =
  fun projectee -> match projectee with | Product _0 -> _0
let (uu___is_Sum : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sum _0 -> true | uu____1499 -> false
let (__proj__Sum__item___0 :
  term' -> ((binder, term) FStar_Util.either Prims.list * term)) =
  fun projectee -> match projectee with | Sum _0 -> _0
let (uu___is_QForall : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | QForall _0 -> true | uu____1560 -> false
let (__proj__QForall__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee -> match projectee with | QForall _0 -> _0
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | QExists _0 -> true | uu____1645 -> false
let (__proj__QExists__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee -> match projectee with | QExists _0 -> _0
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Refine _0 -> true | uu____1716 -> false
let (__proj__Refine__item___0 : term' -> (binder * term)) =
  fun projectee -> match projectee with | Refine _0 -> _0
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NamedTyp _0 -> true | uu____1745 -> false
let (__proj__NamedTyp__item___0 : term' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | NamedTyp _0 -> _0
let (uu___is_Paren : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Paren _0 -> true | uu____1770 -> false
let (__proj__Paren__item___0 : term' -> term) =
  fun projectee -> match projectee with | Paren _0 -> _0
let (uu___is_Requires : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Requires _0 -> true | uu____1789 -> false
let (__proj__Requires__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Requires _0 -> _0
let (uu___is_Ensures : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Ensures _0 -> true | uu____1826 -> false
let (__proj__Ensures__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Ensures _0 -> _0
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Labeled _0 -> true | uu____1863 -> false
let (__proj__Labeled__item___0 : term' -> (term * Prims.string * Prims.bool))
  = fun projectee -> match projectee with | Labeled _0 -> _0
let (uu___is_Discrim : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Discrim _0 -> true | uu____1894 -> false
let (__proj__Discrim__item___0 : term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Discrim _0 -> _0
let (uu___is_Attributes : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Attributes _0 -> true | uu____1909 -> false
let (__proj__Attributes__item___0 : term' -> term Prims.list) =
  fun projectee -> match projectee with | Attributes _0 -> _0
let (uu___is_Antiquote : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Antiquote _0 -> true | uu____1928 -> false
let (__proj__Antiquote__item___0 : term' -> term) =
  fun projectee -> match projectee with | Antiquote _0 -> _0
let (uu___is_Quote : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Quote _0 -> true | uu____1945 -> false
let (__proj__Quote__item___0 : term' -> (term * quote_kind)) =
  fun projectee -> match projectee with | Quote _0 -> _0
let (uu___is_VQuote : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | VQuote _0 -> true | uu____1970 -> false
let (__proj__VQuote__item___0 : term' -> term) =
  fun projectee -> match projectee with | VQuote _0 -> _0
let (uu___is_CalcProof : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | CalcProof _0 -> true | uu____1991 -> false
let (__proj__CalcProof__item___0 :
  term' -> (term * term * calc_step Prims.list)) =
  fun projectee -> match projectee with | CalcProof _0 -> _0
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee ->
    match projectee with | { tm; range; level = level1;_} -> tm
let (__proj__Mkterm__item__range : term -> FStar_Range.range) =
  fun projectee ->
    match projectee with | { tm; range; level = level1;_} -> range
let (__proj__Mkterm__item__level : term -> level) =
  fun projectee ->
    match projectee with | { tm; range; level = level1;_} -> level1
let (uu___is_CalcStep : calc_step -> Prims.bool) = fun projectee -> true
let (__proj__CalcStep__item___0 : calc_step -> (term * term * term)) =
  fun projectee -> match projectee with | CalcStep _0 -> _0
let (uu___is_Variable : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | Variable _0 -> true | uu____2081 -> false
let (__proj__Variable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Variable _0 -> _0
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | TVariable _0 -> true | uu____2094 -> false
let (__proj__TVariable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | TVariable _0 -> _0
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | Annotated _0 -> true | uu____2111 -> false
let (__proj__Annotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Annotated _0 -> _0
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | TAnnotated _0 -> true | uu____2140 -> false
let (__proj__TAnnotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | TAnnotated _0 -> _0
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | NoName _0 -> true | uu____2165 -> false
let (__proj__NoName__item___0 : binder' -> term) =
  fun projectee -> match projectee with | NoName _0 -> _0
let (__proj__Mkbinder__item__b : binder -> binder') =
  fun projectee -> match projectee with | { b; brange; blevel; aqual;_} -> b
let (__proj__Mkbinder__item__brange : binder -> FStar_Range.range) =
  fun projectee ->
    match projectee with | { b; brange; blevel; aqual;_} -> brange
let (__proj__Mkbinder__item__blevel : binder -> level) =
  fun projectee ->
    match projectee with | { b; brange; blevel; aqual;_} -> blevel
let (__proj__Mkbinder__item__aqual :
  binder -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { b; brange; blevel; aqual;_} -> aqual
let (uu___is_PatWild : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatWild _0 -> true | uu____2228 -> false
let (__proj__PatWild__item___0 :
  pattern' -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | PatWild _0 -> _0
let (uu___is_PatConst : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatConst _0 -> true | uu____2247 -> false
let (__proj__PatConst__item___0 : pattern' -> FStar_Const.sconst) =
  fun projectee -> match projectee with | PatConst _0 -> _0
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatApp _0 -> true | uu____2266 -> false
let (__proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list)) =
  fun projectee -> match projectee with | PatApp _0 -> _0
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatVar _0 -> true | uu____2303 -> false
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | PatVar _0 -> _0
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatName _0 -> true | uu____2334 -> false
let (__proj__PatName__item___0 : pattern' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | PatName _0 -> _0
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatTvar _0 -> true | uu____2353 -> false
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | PatTvar _0 -> _0
let (uu___is_PatList : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatList _0 -> true | uu____2386 -> false
let (__proj__PatList__item___0 : pattern' -> pattern Prims.list) =
  fun projectee -> match projectee with | PatList _0 -> _0
let (uu___is_PatTuple : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatTuple _0 -> true | uu____2411 -> false
let (__proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list * Prims.bool)) =
  fun projectee -> match projectee with | PatTuple _0 -> _0
let (uu___is_PatRecord : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatRecord _0 -> true | uu____2448 -> false
let (__proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list) =
  fun projectee -> match projectee with | PatRecord _0 -> _0
let (uu___is_PatAscribed : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatAscribed _0 -> true | uu____2489 -> false
let (__proj__PatAscribed__item___0 :
  pattern' -> (pattern * (term * term FStar_Pervasives_Native.option))) =
  fun projectee -> match projectee with | PatAscribed _0 -> _0
let (uu___is_PatOr : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatOr _0 -> true | uu____2534 -> false
let (__proj__PatOr__item___0 : pattern' -> pattern Prims.list) =
  fun projectee -> match projectee with | PatOr _0 -> _0
let (uu___is_PatOp : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatOp _0 -> true | uu____2553 -> false
let (__proj__PatOp__item___0 : pattern' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | PatOp _0 -> _0
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee -> match projectee with | { pat; prange;_} -> pat
let (__proj__Mkpattern__item__prange : pattern -> FStar_Range.range) =
  fun projectee -> match projectee with | { pat; prange;_} -> prange
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Implicit -> true | uu____2579 -> false
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Equality -> true | uu____2585 -> false
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____2592 -> false
let (__proj__Meta__item___0 : arg_qualifier -> arg_qualifier_meta_t) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Arg_qualifier_meta_tac : arg_qualifier_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Arg_qualifier_meta_tac _0 -> true
    | uu____2605 -> false
let (__proj__Arg_qualifier_meta_tac__item___0 : arg_qualifier_meta_t -> term)
  = fun projectee -> match projectee with | Arg_qualifier_meta_tac _0 -> _0
let (uu___is_Arg_qualifier_meta_attr : arg_qualifier_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Arg_qualifier_meta_attr _0 -> true
    | uu____2618 -> false
let (__proj__Arg_qualifier_meta_attr__item___0 :
  arg_qualifier_meta_t -> term) =
  fun projectee -> match projectee with | Arg_qualifier_meta_attr _0 -> _0
let (uu___is_FsTypApp : imp -> Prims.bool) =
  fun projectee ->
    match projectee with | FsTypApp -> true | uu____2630 -> false
let (uu___is_Hash : imp -> Prims.bool) =
  fun projectee -> match projectee with | Hash -> true | uu____2636 -> false
let (uu___is_UnivApp : imp -> Prims.bool) =
  fun projectee ->
    match projectee with | UnivApp -> true | uu____2642 -> false
let (uu___is_HashBrace : imp -> Prims.bool) =
  fun projectee ->
    match projectee with | HashBrace _0 -> true | uu____2649 -> false
let (__proj__HashBrace__item___0 : imp -> term) =
  fun projectee -> match projectee with | HashBrace _0 -> _0
let (uu___is_Infix : imp -> Prims.bool) =
  fun projectee -> match projectee with | Infix -> true | uu____2661 -> false
let (uu___is_Nothing : imp -> Prims.bool) =
  fun projectee ->
    match projectee with | Nothing -> true | uu____2667 -> false
type patterns = (FStar_Ident.ident Prims.list * term Prims.list Prims.list)
type attributes_ = term Prims.list
type branch = (pattern * term FStar_Pervasives_Native.option * term)
type aqual = arg_qualifier FStar_Pervasives_Native.option
type knd = term
type typ = term
type expr = term
type tycon =
  | TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option) 
  | TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * term) 
  | TyconRecord of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term) Prims.list) 
  | TyconVariant of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term
  FStar_Pervasives_Native.option * Prims.bool) Prims.list) 
let (uu___is_TyconAbstract : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconAbstract _0 -> true | uu____2788 -> false
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | TyconAbstract _0 -> _0
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconAbbrev _0 -> true | uu____2843 -> false
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * term))
  = fun projectee -> match projectee with | TyconAbbrev _0 -> _0
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconRecord _0 -> true | uu____2910 -> false
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term) Prims.list))
  = fun projectee -> match projectee with | TyconRecord _0 -> _0
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconVariant _0 -> true | uu____2999 -> false
let (__proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term
      FStar_Pervasives_Native.option * Prims.bool) Prims.list))
  = fun projectee -> match projectee with | TyconVariant _0 -> _0
type qualifier =
  | Private 
  | Abstract 
  | Noeq 
  | Unopteq 
  | Assumption 
  | DefaultEffect 
  | TotalEffect 
  | Effect_qual 
  | New 
  | Inline 
  | Visible 
  | Unfold_for_unification_and_vcgen 
  | Inline_for_extraction 
  | Irreducible 
  | NoExtract 
  | Reifiable 
  | Reflectable 
  | Opaque 
  | Logic 
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Private -> true | uu____3077 -> false
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Abstract -> true | uu____3083 -> false
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Noeq -> true | uu____3089 -> false
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Unopteq -> true | uu____3095 -> false
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Assumption -> true | uu____3101 -> false
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | DefaultEffect -> true | uu____3107 -> false
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | TotalEffect -> true | uu____3113 -> false
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Effect_qual -> true | uu____3119 -> false
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | New -> true | uu____3125 -> false
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Inline -> true | uu____3131 -> false
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Visible -> true | uu____3137 -> false
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Unfold_for_unification_and_vcgen -> true
    | uu____3143 -> false
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Inline_for_extraction -> true
    | uu____3149 -> false
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Irreducible -> true | uu____3155 -> false
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | NoExtract -> true | uu____3161 -> false
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reifiable -> true | uu____3167 -> false
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reflectable -> true | uu____3173 -> false
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Opaque -> true | uu____3179 -> false
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Logic -> true | uu____3185 -> false
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee ->
    match projectee with | Qualifier _0 -> true | uu____3206 -> false
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee -> match projectee with | Qualifier _0 -> _0
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee ->
    match projectee with | DeclAttributes _0 -> true | uu____3221 -> false
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee -> match projectee with | DeclAttributes _0 -> _0
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | NonReifiableLift _0 -> true | uu____3259 -> false
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee -> match projectee with | NonReifiableLift _0 -> _0
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | ReifiableLift _0 -> true | uu____3276 -> false
let (__proj__ReifiableLift__item___0 : lift_op -> (term * term)) =
  fun projectee -> match projectee with | ReifiableLift _0 -> _0
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | LiftForFree _0 -> true | uu____3301 -> false
let (__proj__LiftForFree__item___0 : lift_op -> term) =
  fun projectee -> match projectee with | LiftForFree _0 -> _0
type lift =
  {
  msource: FStar_Ident.lid ;
  mdest: FStar_Ident.lid ;
  lift_op: lift_op }
let (__proj__Mklift__item__msource : lift -> FStar_Ident.lid) =
  fun projectee ->
    match projectee with | { msource; mdest; lift_op = lift_op1;_} -> msource
let (__proj__Mklift__item__mdest : lift -> FStar_Ident.lid) =
  fun projectee ->
    match projectee with | { msource; mdest; lift_op = lift_op1;_} -> mdest
let (__proj__Mklift__item__lift_op : lift -> lift_op) =
  fun projectee ->
    match projectee with
    | { msource; mdest; lift_op = lift_op1;_} -> lift_op1
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | RestartSolver 
  | LightOff 
let (uu___is_SetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | SetOptions _0 -> true | uu____3372 -> false
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee -> match projectee with | SetOptions _0 -> _0
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | ResetOptions _0 -> true | uu____3387 -> false
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | ResetOptions _0 -> _0
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PushOptions _0 -> true | uu____3408 -> false
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | PushOptions _0 -> _0
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PopOptions -> true | uu____3426 -> false
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | RestartSolver -> true | uu____3432 -> false
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | LightOff -> true | uu____3438 -> false
type decl' =
  | TopLevelModule of FStar_Ident.lid 
  | Open of FStar_Ident.lid 
  | Friend of FStar_Ident.lid 
  | Include of FStar_Ident.lid 
  | ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid) 
  | TopLevelLet of (let_qualifier * (pattern * term) Prims.list) 
  | Tycon of (Prims.bool * Prims.bool * tycon Prims.list) 
  | Val of (FStar_Ident.ident * term) 
  | Exception of (FStar_Ident.ident * term FStar_Pervasives_Native.option) 
  | NewEffect of effect_decl 
  | LayeredEffect of effect_decl 
  | SubEffect of lift 
  | Polymonadic_bind of (FStar_Ident.lid * FStar_Ident.lid * FStar_Ident.lid
  * term) 
  | Polymonadic_subcomp of (FStar_Ident.lid * FStar_Ident.lid * term) 
  | Pragma of pragma 
  | Assume of (FStar_Ident.ident * term) 
  | Splice of (FStar_Ident.ident Prims.list * term) 
and decl =
  {
  d: decl' ;
  drange: FStar_Range.range ;
  quals: qualifiers ;
  attrs: attributes_ }
and effect_decl =
  | DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl
  Prims.list) 
  | RedefineEffect of (FStar_Ident.ident * binder Prims.list * term) 
let (uu___is_TopLevelModule : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelModule _0 -> true | uu____3636 -> false
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TopLevelModule _0 -> _0
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Open _0 -> true | uu____3649 -> false
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Open _0 -> _0
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Friend _0 -> true | uu____3662 -> false
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Friend _0 -> _0
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Include _0 -> true | uu____3675 -> false
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Include _0 -> _0
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | ModuleAbbrev _0 -> true | uu____3692 -> false
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid)) =
  fun projectee -> match projectee with | ModuleAbbrev _0 -> _0
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelLet _0 -> true | uu____3727 -> false
let (__proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list)) =
  fun projectee -> match projectee with | TopLevelLet _0 -> _0
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tycon _0 -> true | uu____3778 -> false
let (__proj__Tycon__item___0 :
  decl' -> (Prims.bool * Prims.bool * tycon Prims.list)) =
  fun projectee -> match projectee with | Tycon _0 -> _0
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Val _0 -> true | uu____3819 -> false
let (__proj__Val__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Val _0 -> _0
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Exception _0 -> true | uu____3850 -> false
let (__proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Exception _0 -> _0
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | NewEffect _0 -> true | uu____3881 -> false
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee -> match projectee with | NewEffect _0 -> _0
let (uu___is_LayeredEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | LayeredEffect _0 -> true | uu____3894 -> false
let (__proj__LayeredEffect__item___0 : decl' -> effect_decl) =
  fun projectee -> match projectee with | LayeredEffect _0 -> _0
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | SubEffect _0 -> true | uu____3907 -> false
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee -> match projectee with | SubEffect _0 -> _0
let (uu___is_Polymonadic_bind : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Polymonadic_bind _0 -> true | uu____3928 -> false
let (__proj__Polymonadic_bind__item___0 :
  decl' -> (FStar_Ident.lid * FStar_Ident.lid * FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | Polymonadic_bind _0 -> _0
let (uu___is_Polymonadic_subcomp : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Polymonadic_subcomp _0 -> true
    | uu____3971 -> false
let (__proj__Polymonadic_subcomp__item___0 :
  decl' -> (FStar_Ident.lid * FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | Polymonadic_subcomp _0 -> _0
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pragma _0 -> true | uu____4002 -> false
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee -> match projectee with | Pragma _0 -> _0
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Assume _0 -> true | uu____4019 -> false
let (__proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Assume _0 -> _0
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Splice _0 -> true | uu____4050 -> false
let (__proj__Splice__item___0 :
  decl' -> (FStar_Ident.ident Prims.list * term)) =
  fun projectee -> match projectee with | Splice _0 -> _0
let (__proj__Mkdecl__item__d : decl -> decl') =
  fun projectee -> match projectee with | { d; drange; quals; attrs;_} -> d
let (__proj__Mkdecl__item__drange : decl -> FStar_Range.range) =
  fun projectee ->
    match projectee with | { d; drange; quals; attrs;_} -> drange
let (__proj__Mkdecl__item__quals : decl -> qualifiers) =
  fun projectee ->
    match projectee with | { d; drange; quals; attrs;_} -> quals
let (__proj__Mkdecl__item__attrs : decl -> attributes_) =
  fun projectee ->
    match projectee with | { d; drange; quals; attrs;_} -> attrs
let (uu___is_DefineEffect : effect_decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DefineEffect _0 -> true | uu____4129 -> false
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee -> match projectee with | DefineEffect _0 -> _0
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee ->
    match projectee with | RedefineEffect _0 -> true | uu____4186 -> false
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term)) =
  fun projectee -> match projectee with | RedefineEffect _0 -> _0
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee ->
    match projectee with | Module _0 -> true | uu____4253 -> false
let (__proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list))
  = fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee ->
    match projectee with | Interface _0 -> true | uu____4292 -> false
let (__proj__Interface__item___0 :
  modul -> (FStar_Ident.lid * decl Prims.list * Prims.bool)) =
  fun projectee -> match projectee with | Interface _0 -> _0
type file = modul
type inputFragment = (file, decl Prims.list) FStar_Util.either
let (decl_drange : decl -> FStar_Range.range) = fun decl1 -> decl1.drange
let (check_id : FStar_Ident.ident -> unit) =
  fun id ->
    let first_char =
      let uu____4340 = FStar_Ident.string_of_id id in
      FStar_String.substring uu____4340 Prims.int_zero Prims.int_one in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____4342 =
         let uu____4347 =
           let uu____4348 = FStar_Ident.string_of_id id in
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             uu____4348 in
         (FStar_Errors.Fatal_InvalidIdentifier, uu____4347) in
       let uu____4349 = FStar_Ident.range_of_id id in
       FStar_Errors.raise_error uu____4342 uu____4349)
let at_most_one :
  'uuuuuu4358 .
    Prims.string ->
      FStar_Range.range ->
        'uuuuuu4358 Prims.list -> 'uuuuuu4358 FStar_Pervasives_Native.option
  =
  fun s ->
    fun r ->
      fun l ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____4381 ->
            let uu____4384 =
              let uu____4389 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu____4389) in
            FStar_Errors.raise_error uu____4384 r
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d ->
    fun r ->
      fun decorations ->
        let attributes_1 =
          let uu____4416 =
            FStar_List.choose
              (fun uu___0_4425 ->
                 match uu___0_4425 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____4435 -> FStar_Pervasives_Native.None) decorations in
          at_most_one "attribute set" r uu____4416 in
        let attributes_2 = FStar_Util.dflt [] attributes_1 in
        let qualifiers1 =
          FStar_List.choose
            (fun uu___1_4450 ->
               match uu___1_4450 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____4454 -> FStar_Pervasives_Native.None) decorations in
        { d; drange = r; quals = qualifiers1; attrs = attributes_2 }
let (mk_binder :
  binder' ->
    FStar_Range.range ->
      level -> arg_qualifier FStar_Pervasives_Native.option -> binder)
  =
  fun b ->
    fun r -> fun l -> fun i -> { b; brange = r; blevel = l; aqual = i }
let (mk_term : term' -> FStar_Range.range -> level -> term) =
  fun t -> fun r -> fun l -> { tm = t; range = r; level = l }
let (mk_uminus :
  term -> FStar_Range.range -> FStar_Range.range -> level -> term) =
  fun t ->
    fun rminus ->
      fun r ->
        fun l ->
          let t1 =
            match t.tm with
            | Const (FStar_Const.Const_int
                (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, width)))
                ->
                Const
                  (FStar_Const.Const_int
                     ((Prims.op_Hat "-" s),
                       (FStar_Pervasives_Native.Some
                          (FStar_Const.Signed, width))))
            | uu____4537 ->
                let uu____4538 =
                  let uu____4545 = FStar_Ident.mk_ident ("-", rminus) in
                  (uu____4545, [t]) in
                Op uu____4538 in
          mk_term t1 r l
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p -> fun r -> { pat = p; prange = r }
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps ->
    fun body ->
      match body.tm with
      | Abs (p', body') -> Abs ((FStar_List.append ps p'), body')
      | uu____4580 -> Abs (ps, body)
let (mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches ->
    fun r1 ->
      fun r2 ->
        let x = FStar_Ident.gen r1 in
        let uu____4619 =
          let uu____4620 =
            let uu____4627 =
              let uu____4628 =
                let uu____4629 =
                  let uu____4644 =
                    let uu____4645 =
                      let uu____4646 = FStar_Ident.lid_of_ids [x] in
                      Var uu____4646 in
                    mk_term uu____4645 r1 Expr in
                  (uu____4644, branches) in
                Match uu____4629 in
              mk_term uu____4628 r2 Expr in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____4627) in
          Abs uu____4620 in
        mk_term uu____4619 r2 Expr
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p ->
    fun tm ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____4683, Abs (pats, body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____4702 -> FStar_Pervasives_Native.None
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid ->
    fun r ->
      let uu____4721 = FStar_Ident.path_of_lid lid in
      FStar_Ident.lid_of_path uu____4721 r
let (consPat : FStar_Range.range -> pattern -> pattern -> pattern') =
  fun r ->
    fun hd ->
      fun tl ->
        PatApp
          ((mk_pattern (PatName FStar_Parser_Const.cons_lid) r), [hd; tl])
let (consTerm : FStar_Range.range -> term -> term -> term) =
  fun r ->
    fun hd ->
      fun tl ->
        mk_term
          (Construct
             (FStar_Parser_Const.cons_lid, [(hd, Nothing); (tl, Nothing)])) r
          Expr
let (lexConsTerm : FStar_Range.range -> term -> term -> term) =
  fun r ->
    fun hd ->
      fun tl ->
        mk_term
          (Construct
             (FStar_Parser_Const.lexcons_lid, [(hd, Nothing); (tl, Nothing)]))
          r Expr
let (mkConsList : FStar_Range.range -> term Prims.list -> term) =
  fun r ->
    fun elts ->
      let nil = mk_term (Construct (FStar_Parser_Const.nil_lid, [])) r Expr in
      FStar_List.fold_right (fun e -> fun tl -> consTerm r e tl) elts nil
let (mkLexList : FStar_Range.range -> term Prims.list -> term) =
  fun r ->
    fun elts ->
      let nil =
        mk_term (Construct (FStar_Parser_Const.lextop_lid, [])) r Expr in
      FStar_List.fold_right (fun e -> fun tl -> lexConsTerm r e tl) elts nil
let (ml_comp : term -> term) =
  fun t ->
    let ml = mk_term (Name FStar_Parser_Const.effect_ML_lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let (tot_comp : term -> term) =
  fun t ->
    let ml = mk_term (Name FStar_Parser_Const.effect_Tot_lid) t.range Expr in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr in t1
let (mkApp : term -> (term * imp) Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun args ->
      fun r ->
        match args with
        | [] -> t
        | uu____4908 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____4922 ->
                 FStar_List.fold_left
                   (fun t1 ->
                      fun uu____4932 ->
                        match uu____4932 with
                        | (a, imp1) -> mk_term (App (t1, a, imp1)) r Un) t
                   args)
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r ->
    fun elts ->
      let uu____4953 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid) in
      match uu____4953 with
      | (empty_lid, singleton_lid, union_lid, addr_of_lid) ->
          let empty =
            let uu____4967 =
              let uu____4968 = FStar_Ident.set_lid_range empty_lid r in
              Var uu____4968 in
            mk_term uu____4967 r Expr in
          let addr_of =
            let uu____4970 =
              let uu____4971 = FStar_Ident.set_lid_range addr_of_lid r in
              Var uu____4971 in
            mk_term uu____4970 r Expr in
          let singleton =
            let uu____4973 =
              let uu____4974 = FStar_Ident.set_lid_range singleton_lid r in
              Var uu____4974 in
            mk_term uu____4973 r Expr in
          let union =
            let uu____4976 =
              let uu____4977 = FStar_Ident.set_lid_range union_lid r in
              Var uu____4977 in
            mk_term uu____4976 r Expr in
          FStar_List.fold_right
            (fun e ->
               fun tl ->
                 let e1 = mkApp addr_of [(e, Nothing)] r in
                 let single_e = mkApp singleton [(e1, Nothing)] r in
                 mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts
            empty
let (mkExplicitApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun args ->
      fun r ->
        match args with
        | [] -> t
        | uu____5033 ->
            (match t.tm with
             | Name s ->
                 let uu____5037 =
                   let uu____5038 =
                     let uu____5049 =
                       FStar_List.map (fun a -> (a, Nothing)) args in
                     (s, uu____5049) in
                   Construct uu____5038 in
                 mk_term uu____5037 r Un
             | uu____5068 ->
                 FStar_List.fold_left
                   (fun t1 -> fun a -> mk_term (App (t1, a, Nothing)) r Un) t
                   args)
let (unit_const : FStar_Range.range -> term) =
  fun r -> mk_term (Const FStar_Const.Const_unit) r Expr
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r ->
    let admit =
      let admit_name =
        let uu____5085 =
          let uu____5086 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r in
          Var uu____5086 in
        mk_term uu____5085 r Expr in
      mkExplicitApp admit_name [unit_const r] r in
    let magic =
      let magic_name =
        let uu____5089 =
          let uu____5090 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r in
          Var uu____5090 in
        mk_term uu____5089 r Expr in
      mkExplicitApp magic_name [unit_const r] r in
    let admit_magic = mk_term (Seq (admit, magic)) r Expr in admit_magic
let mkWildAdmitMagic :
  'uuuuuu5096 .
    FStar_Range.range ->
      (pattern * 'uuuuuu5096 FStar_Pervasives_Native.option * term)
  =
  fun r ->
    let uu____5110 = mkAdmitMagic r in
    ((mk_pattern (PatWild FStar_Pervasives_Native.None) r),
      FStar_Pervasives_Native.None, uu____5110)
let focusBranches :
  'uuuuuu5119 .
    (Prims.bool * (pattern * 'uuuuuu5119 FStar_Pervasives_Native.option *
      term)) Prims.list ->
      FStar_Range.range ->
        (pattern * 'uuuuuu5119 FStar_Pervasives_Native.option * term)
          Prims.list
  =
  fun branches ->
    fun r ->
      let should_filter =
        FStar_Util.for_some FStar_Pervasives_Native.fst branches in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered, "Focusing on only some cases");
         (let focussed =
            let uu____5211 =
              FStar_List.filter FStar_Pervasives_Native.fst branches in
            FStar_All.pipe_right uu____5211
              (FStar_List.map FStar_Pervasives_Native.snd) in
          let uu____5298 =
            let uu____5309 = mkWildAdmitMagic r in [uu____5309] in
          FStar_List.append focussed uu____5298))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
let focusLetBindings :
  'uuuuuu5401 .
    (Prims.bool * ('uuuuuu5401 * term)) Prims.list ->
      FStar_Range.range -> ('uuuuuu5401 * term) Prims.list
  =
  fun lbs ->
    fun r ->
      let should_filter = FStar_Util.for_some FStar_Pervasives_Native.fst lbs in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____5473 ->
              match uu____5473 with
              | (f, lb) ->
                  if f
                  then lb
                  else
                    (let uu____5501 = mkAdmitMagic r in
                     ((FStar_Pervasives_Native.fst lb), uu____5501))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
let focusAttrLetBindings :
  'uuuuuu5543 'uuuuuu5544 .
    ('uuuuuu5543 * (Prims.bool * ('uuuuuu5544 * term))) Prims.list ->
      FStar_Range.range -> ('uuuuuu5543 * ('uuuuuu5544 * term)) Prims.list
  =
  fun lbs ->
    fun r ->
      let should_filter =
        FStar_Util.for_some
          (fun uu____5610 ->
             match uu____5610 with | (attr, (focus, uu____5625)) -> focus)
          lbs in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____5677 ->
              match uu____5677 with
              | (attr, (f, lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu____5730 =
                       let uu____5735 = mkAdmitMagic r in
                       ((FStar_Pervasives_Native.fst lb), uu____5735) in
                     (attr, uu____5730))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu____5789 ->
                match uu____5789 with
                | (attr, (uu____5811, lb)) -> (attr, lb)))
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun args ->
      fun r ->
        let uu____5852 = FStar_List.map (fun a -> (a, FsTypApp)) args in
        mkApp t uu____5852 r
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args ->
    fun r ->
      let cons =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r in
      let uu____5880 = FStar_List.map (fun x -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu____5880 r
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args ->
    fun r ->
      let cons =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r in
      let uu____5908 = FStar_List.map (fun x -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu____5908 r
let (mkRefinedBinder :
  FStar_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range ->
            arg_qualifier FStar_Pervasives_Native.option -> binder)
  =
  fun id ->
    fun t ->
      fun should_bind_var ->
        fun refopt ->
          fun m ->
            fun implicit ->
              let b = mk_binder (Annotated (id, t)) m Type_level implicit in
              match refopt with
              | FStar_Pervasives_Native.None -> b
              | FStar_Pervasives_Native.Some phi ->
                  if should_bind_var
                  then
                    mk_binder
                      (Annotated
                         (id, (mk_term (Refine (b, phi)) m Type_level))) m
                      Type_level implicit
                  else
                    (let x = FStar_Ident.gen t.range in
                     let b1 =
                       mk_binder (Annotated (x, t)) m Type_level implicit in
                     mk_binder
                       (Annotated
                          (id, (mk_term (Refine (b1, phi)) m Type_level))) m
                       Type_level implicit)
let (mkRefinedPattern :
  pattern ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> FStar_Range.range -> pattern)
  =
  fun pat ->
    fun t ->
      fun should_bind_pat ->
        fun phi_opt ->
          fun t_range ->
            fun range ->
              let t1 =
                match phi_opt with
                | FStar_Pervasives_Native.None -> t
                | FStar_Pervasives_Native.Some phi ->
                    if should_bind_pat
                    then
                      (match pat.pat with
                       | PatVar (x, uu____6001) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____6006 ->
                           let x = FStar_Ident.gen t_range in
                           let phi1 =
                             let x_var =
                               let uu____6010 =
                                 let uu____6011 = FStar_Ident.lid_of_ids [x] in
                                 Var uu____6011 in
                               mk_term uu____6010 phi.range Formula in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi) in
                             let otherwise_branch =
                               let uu____6032 =
                                 let uu____6033 =
                                   let uu____6034 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range in
                                   Name uu____6034 in
                                 mk_term uu____6033 phi.range Formula in
                               ((mk_pattern
                                   (PatWild FStar_Pervasives_Native.None)
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu____6032) in
                             mk_term
                               (Match (x_var, [pat_branch; otherwise_branch]))
                               phi.range Formula in
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi1)) range Type_level)
                    else
                      (let x = FStar_Ident.gen t.range in
                       mk_term
                         (Refine
                            ((mk_binder (Annotated (x, t)) t_range Type_level
                                FStar_Pervasives_Native.None), phi)) range
                         Type_level) in
              mk_pattern
                (PatAscribed (pat, (t1, FStar_Pervasives_Native.None))) range
let rec (extract_named_refinement :
  term ->
    (FStar_Ident.ident * term * term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun t1 ->
    match t1.tm with
    | NamedTyp (x, t) ->
        FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
    | Refine
        ({ b = Annotated (x, t); brange = uu____6120; blevel = uu____6121;
           aqual = uu____6122;_},
         t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____6137 -> FStar_Pervasives_Native.None
let rec (as_mlist :
  ((FStar_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul) =
  fun cur ->
    fun ds ->
      let uu____6180 = cur in
      match uu____6180 with
      | ((m_name, m_decl), cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu____6209 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light ->
    fun light_range ->
      fun ds ->
        let uu____6235 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag in
        match uu____6235 with
        | (d, ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____6272 =
                       mk_decl (Pragma LightOff) light_range [] in
                     uu____6272 :: ds1
                   else ds1 in
                 let m1 = as_mlist ((m, d), []) ds2 in FStar_Util.Inl m1
             | uu____6283 ->
                 let ds2 = d :: ds1 in
                 (FStar_List.iter
                    (fun uu___2_6293 ->
                       match uu___2_6293 with
                       | { d = TopLevelModule uu____6294; drange = r;
                           quals = uu____6296; attrs = uu____6297;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu____6298 -> ()) ds2;
                  FStar_Util.Inr ds2))
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity ->
    fun s ->
      fun r ->
        let name_of_char uu___3_6321 =
          match uu___3_6321 with
          | 38 -> "Amp"
          | 64 -> "At"
          | 43 -> "Plus"
          | 45 when arity = Prims.int_one -> "Minus"
          | 45 -> "Subtraction"
          | 126 -> "Tilde"
          | 47 -> "Slash"
          | 92 -> "Backslash"
          | 60 -> "Less"
          | 61 -> "Equals"
          | 62 -> "Greater"
          | 95 -> "Underscore"
          | 124 -> "Bar"
          | 33 -> "Bang"
          | 94 -> "Hat"
          | 37 -> "Percent"
          | 42 -> "Star"
          | 63 -> "Question"
          | 58 -> "Colon"
          | 36 -> "Dollar"
          | 46 -> "Dot"
          | c ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedOperatorSymbol,
                  (Prims.op_Hat "Unexpected operator symbol: '"
                     (Prims.op_Hat (FStar_Util.string_of_char c) "'"))) r in
        match s with
        | ".[]<-" -> "op_String_Assignment"
        | ".()<-" -> "op_Array_Assignment"
        | ".[||]<-" -> "op_Brack_Lens_Assignment"
        | ".(||)<-" -> "op_Lens_Assignment"
        | ".[]" -> "op_String_Access"
        | ".()" -> "op_Array_Access"
        | ".[||]" -> "op_Brack_Lens_Access"
        | ".(||)" -> "op_Lens_Access"
        | uu____6323 ->
            let uu____6324 =
              let uu____6325 =
                let uu____6328 = FStar_String.list_of_string s in
                FStar_List.map name_of_char uu____6328 in
              FStar_String.concat "_" uu____6325 in
            Prims.op_Hat "op_" uu____6324
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s -> fun r -> compile_op (~- Prims.int_one) s r
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu____6355 ->
    match uu____6355 with
    | (comment, keywords) ->
        let uu____6380 =
          let uu____6381 =
            FStar_List.map
              (fun uu____6391 ->
                 match uu____6391 with
                 | (k, v) -> Prims.op_Hat k (Prims.op_Hat "->" v)) keywords in
          FStar_String.concat "," uu____6381 in
        Prims.op_Hat comment uu____6380
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___4_6402 ->
    match uu___4_6402 with | NoLetQualifier -> "" | Rec -> "rec"
let to_string_l :
  'uuuuuu6411 .
    Prims.string ->
      ('uuuuuu6411 -> Prims.string) -> 'uuuuuu6411 Prims.list -> Prims.string
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu____6436 = FStar_List.map f l in
        FStar_String.concat sep uu____6436
let (imp_to_string : imp -> Prims.string) =
  fun uu___5_6443 -> match uu___5_6443 with | Hash -> "#" | uu____6444 -> ""
let rec (term_to_string : term -> Prims.string) =
  fun x ->
    match x.tm with
    | Wild -> "_"
    | Requires (t, uu____6477) ->
        let uu____6482 = term_to_string t in
        FStar_Util.format1 "(requires %s)" uu____6482
    | Ensures (t, uu____6484) ->
        let uu____6489 = term_to_string t in
        FStar_Util.format1 "(ensures %s)" uu____6489
    | Labeled (t, l, uu____6492) ->
        let uu____6493 = term_to_string t in
        FStar_Util.format2 "(labeled %s %s)" l uu____6493
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s, xs) ->
        let uu____6501 = FStar_Ident.string_of_id s in
        let uu____6502 =
          let uu____6503 =
            FStar_List.map (fun x1 -> FStar_All.pipe_right x1 term_to_string)
              xs in
          FStar_String.concat ", " uu____6503 in
        FStar_Util.format2 "%s(%s)" uu____6501 uu____6502
    | Tvar id -> FStar_Ident.string_of_id id
    | Uvar id -> FStar_Ident.string_of_id id
    | Var l -> FStar_Ident.string_of_lid l
    | Name l -> FStar_Ident.string_of_lid l
    | Projector (rec_lid, field_id) ->
        let uu____6514 = FStar_Ident.string_of_lid rec_lid in
        let uu____6515 = FStar_Ident.string_of_id field_id in
        FStar_Util.format2 "%s?.%s" uu____6514 uu____6515
    | Construct (l, args) ->
        let uu____6530 = FStar_Ident.string_of_lid l in
        let uu____6531 =
          to_string_l " "
            (fun uu____6540 ->
               match uu____6540 with
               | (a, imp1) ->
                   let uu____6547 = term_to_string a in
                   FStar_Util.format2 "%s%s" (imp_to_string imp1) uu____6547)
            args in
        FStar_Util.format2 "(%s %s)" uu____6530 uu____6531
    | Abs (pats, t) ->
        let uu____6554 = to_string_l " " pat_to_string pats in
        let uu____6555 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(fun %s -> %s)" uu____6554 uu____6555
    | App (t1, t2, imp1) ->
        let uu____6559 = FStar_All.pipe_right t1 term_to_string in
        let uu____6560 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format3 "%s %s%s" uu____6559 (imp_to_string imp1)
          uu____6560
    | Let (Rec, (a, (p, b))::lbs, body) ->
        let uu____6618 = attrs_opt_to_string a in
        let uu____6619 =
          let uu____6620 = FStar_All.pipe_right p pat_to_string in
          let uu____6621 = FStar_All.pipe_right b term_to_string in
          FStar_Util.format2 "%s=%s" uu____6620 uu____6621 in
        let uu____6622 =
          to_string_l " "
            (fun uu____6642 ->
               match uu____6642 with
               | (a1, (p1, b1)) ->
                   let uu____6670 = attrs_opt_to_string a1 in
                   let uu____6671 = FStar_All.pipe_right p1 pat_to_string in
                   let uu____6672 = FStar_All.pipe_right b1 term_to_string in
                   FStar_Util.format3 "%sand %s=%s" uu____6670 uu____6671
                     uu____6672) lbs in
        let uu____6673 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format4 "%slet rec %s%s in %s" uu____6618 uu____6619
          uu____6622 uu____6673
    | Let (q, (attrs, (pat, tm))::[], body) ->
        let uu____6729 = attrs_opt_to_string attrs in
        let uu____6730 = FStar_All.pipe_right pat pat_to_string in
        let uu____6731 = FStar_All.pipe_right tm term_to_string in
        let uu____6732 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu____6729
          (string_of_let_qualifier q) uu____6730 uu____6731 uu____6732
    | Let (uu____6733, uu____6734, uu____6735) ->
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_EmptySurfaceLet,
            "Internal error: found an invalid surface Let") x.range
    | LetOpen (lid, t) ->
        let uu____6766 = FStar_Ident.string_of_lid lid in
        let uu____6767 = term_to_string t in
        FStar_Util.format2 "let open %s in %s" uu____6766 uu____6767
    | Seq (t1, t2) ->
        let uu____6770 = FStar_All.pipe_right t1 term_to_string in
        let uu____6771 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "%s; %s" uu____6770 uu____6771
    | Bind (id, t1, t2) ->
        let uu____6775 = FStar_Ident.string_of_id id in
        let uu____6776 = term_to_string t1 in
        let uu____6777 = term_to_string t2 in
        FStar_Util.format3 "%s <- %s; %s" uu____6775 uu____6776 uu____6777
    | If (t1, t2, t3) ->
        let uu____6781 = FStar_All.pipe_right t1 term_to_string in
        let uu____6782 = FStar_All.pipe_right t2 term_to_string in
        let uu____6783 = FStar_All.pipe_right t3 term_to_string in
        FStar_Util.format3 "if %s then %s else %s" uu____6781 uu____6782
          uu____6783
    | Match (t, branches) ->
        let s =
          match x.tm with
          | Match uu____6807 -> "match"
          | TryWith uu____6822 -> "try"
          | uu____6837 -> failwith "impossible" in
        let uu____6838 = FStar_All.pipe_right t term_to_string in
        let uu____6839 =
          to_string_l " | "
            (fun uu____6855 ->
               match uu____6855 with
               | (p, w, e) ->
                   let uu____6871 = FStar_All.pipe_right p pat_to_string in
                   let uu____6872 =
                     match w with
                     | FStar_Pervasives_Native.None -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____6874 = term_to_string e1 in
                         FStar_Util.format1 "when %s" uu____6874 in
                   let uu____6875 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____6871 uu____6872
                     uu____6875) branches in
        FStar_Util.format3 "%s %s with %s" s uu____6838 uu____6839
    | TryWith (t, branches) ->
        let s =
          match x.tm with
          | Match uu____6899 -> "match"
          | TryWith uu____6914 -> "try"
          | uu____6929 -> failwith "impossible" in
        let uu____6930 = FStar_All.pipe_right t term_to_string in
        let uu____6931 =
          to_string_l " | "
            (fun uu____6947 ->
               match uu____6947 with
               | (p, w, e) ->
                   let uu____6963 = FStar_All.pipe_right p pat_to_string in
                   let uu____6964 =
                     match w with
                     | FStar_Pervasives_Native.None -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____6966 = term_to_string e1 in
                         FStar_Util.format1 "when %s" uu____6966 in
                   let uu____6967 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____6963 uu____6964
                     uu____6967) branches in
        FStar_Util.format3 "%s %s with %s" s uu____6930 uu____6931
    | Ascribed (t1, t2, FStar_Pervasives_Native.None) ->
        let uu____6972 = FStar_All.pipe_right t1 term_to_string in
        let uu____6973 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "(%s : %s)" uu____6972 uu____6973
    | Ascribed (t1, t2, FStar_Pervasives_Native.Some tac) ->
        let uu____6979 = FStar_All.pipe_right t1 term_to_string in
        let uu____6980 = FStar_All.pipe_right t2 term_to_string in
        let uu____6981 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s : %s by %s)" uu____6979 uu____6980 uu____6981
    | Record (FStar_Pervasives_Native.Some e, fields) ->
        let uu____6998 = FStar_All.pipe_right e term_to_string in
        let uu____6999 =
          to_string_l " "
            (fun uu____7009 ->
               match uu____7009 with
               | (l, e1) ->
                   let uu____7016 = FStar_Ident.string_of_lid l in
                   let uu____7017 = FStar_All.pipe_right e1 term_to_string in
                   FStar_Util.format2 "%s=%s" uu____7016 uu____7017) fields in
        FStar_Util.format2 "{%s with %s}" uu____6998 uu____6999
    | Record (FStar_Pervasives_Native.None, fields) ->
        let uu____7033 =
          to_string_l " "
            (fun uu____7043 ->
               match uu____7043 with
               | (l, e) ->
                   let uu____7050 = FStar_Ident.string_of_lid l in
                   let uu____7051 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format2 "%s=%s" uu____7050 uu____7051) fields in
        FStar_Util.format1 "{%s}" uu____7033
    | Project (e, l) ->
        let uu____7054 = FStar_All.pipe_right e term_to_string in
        let uu____7055 = FStar_Ident.string_of_lid l in
        FStar_Util.format2 "%s.%s" uu____7054 uu____7055
    | Product ([], t) -> term_to_string t
    | Product (b::hd::tl, t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd :: tl), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[], t) when x.level = Type_level ->
        let uu____7075 = FStar_All.pipe_right b binder_to_string in
        let uu____7076 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s -> %s" uu____7075 uu____7076
    | Product (b::[], t) when x.level = Kind ->
        let uu____7081 = FStar_All.pipe_right b binder_to_string in
        let uu____7082 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s => %s" uu____7081 uu____7082
    | Sum (binders, t) ->
        let uu____7097 =
          FStar_All.pipe_right (FStar_List.append binders [FStar_Util.Inr t])
            (FStar_List.map
               (fun uu___6_7126 ->
                  match uu___6_7126 with
                  | FStar_Util.Inl b -> binder_to_string b
                  | FStar_Util.Inr t1 -> term_to_string t1)) in
        FStar_All.pipe_right uu____7097 (FStar_String.concat " & ")
    | QForall (bs, (uu____7136, pats), t) ->
        let uu____7165 = to_string_l " " binder_to_string bs in
        let uu____7166 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____7169 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____7165 uu____7166
          uu____7169
    | QExists (bs, (uu____7171, pats), t) ->
        let uu____7200 = to_string_l " " binder_to_string bs in
        let uu____7201 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____7204 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____7200 uu____7201
          uu____7204
    | Refine (b, t) ->
        let uu____7207 = FStar_All.pipe_right b binder_to_string in
        let uu____7208 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:{%s}" uu____7207 uu____7208
    | NamedTyp (x1, t) ->
        let uu____7211 = FStar_Ident.string_of_id x1 in
        let uu____7212 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:%s" uu____7211 uu____7212
    | Paren t ->
        let uu____7214 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format1 "(%s)" uu____7214
    | Product (bs, t) ->
        let uu____7221 =
          let uu____7222 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____7222 (FStar_String.concat ",") in
        let uu____7231 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____7221
          uu____7231
    | Discrim lid ->
        let uu____7233 = FStar_Ident.string_of_lid lid in
        FStar_Util.format1 "%s?" uu____7233
    | Attributes ts ->
        let uu____7237 =
          let uu____7238 = FStar_List.map term_to_string ts in
          FStar_All.pipe_left (FStar_String.concat " ") uu____7238 in
        FStar_Util.format1 "(attributes %s)" uu____7237
    | Antiquote t ->
        let uu____7244 = term_to_string t in
        FStar_Util.format1 "(`#%s)" uu____7244
    | Quote (t, Static) ->
        let uu____7246 = term_to_string t in
        FStar_Util.format1 "(`(%s))" uu____7246
    | Quote (t, Dynamic) ->
        let uu____7248 = term_to_string t in
        FStar_Util.format1 "quote (%s)" uu____7248
    | VQuote t ->
        let uu____7250 = term_to_string t in
        FStar_Util.format1 "`%%%s" uu____7250
    | CalcProof (rel, init, steps) ->
        let uu____7258 = term_to_string rel in
        let uu____7259 = term_to_string init in
        let uu____7260 =
          let uu____7261 = FStar_List.map calc_step_to_string steps in
          FStar_All.pipe_left (FStar_String.concat " ") uu____7261 in
        FStar_Util.format3 "calc (%s) { %s %s }" uu____7258 uu____7259
          uu____7260
and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu____7266 ->
    match uu____7266 with
    | CalcStep (rel, just, next) ->
        let uu____7270 = term_to_string rel in
        let uu____7271 = term_to_string just in
        let uu____7272 = term_to_string next in
        FStar_Util.format3 "%s{ %s } %s" uu____7270 uu____7271 uu____7272
and (binder_to_string : binder -> Prims.string) =
  fun x ->
    let s =
      match x.b with
      | Variable i -> FStar_Ident.string_of_id i
      | TVariable i ->
          let uu____7277 = FStar_Ident.string_of_id i in
          FStar_Util.format1 "%s:_" uu____7277
      | TAnnotated (i, t) ->
          let uu____7280 = FStar_Ident.string_of_id i in
          let uu____7281 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" uu____7280 uu____7281
      | Annotated (i, t) ->
          let uu____7284 = FStar_Ident.string_of_id i in
          let uu____7285 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" uu____7284 uu____7285
      | NoName t -> FStar_All.pipe_right t term_to_string in
    let uu____7287 = aqual_to_string x.aqual in
    FStar_Util.format2 "%s%s" uu____7287 s
and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___7_7288 ->
    match uu___7_7288 with
    | FStar_Pervasives_Native.Some (Equality) -> "$"
    | FStar_Pervasives_Native.Some (Implicit) -> "#"
    | FStar_Pervasives_Native.Some (Meta (Arg_qualifier_meta_tac t)) ->
        let uu____7292 =
          let uu____7293 = term_to_string t in Prims.op_Hat uu____7293 "]" in
        Prims.op_Hat "#[" uu____7292
    | FStar_Pervasives_Native.Some (Meta (Arg_qualifier_meta_attr t)) ->
        let uu____7295 =
          let uu____7296 = term_to_string t in Prims.op_Hat uu____7296 "]" in
        Prims.op_Hat "[@@" uu____7295
    | FStar_Pervasives_Native.None -> ""
and (pat_to_string : pattern -> Prims.string) =
  fun x ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None) -> "_"
    | PatWild uu____7298 -> "#_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p, ps) ->
        let uu____7308 = FStar_All.pipe_right p pat_to_string in
        let uu____7309 = to_string_l " " pat_to_string ps in
        FStar_Util.format2 "(%s %s)" uu____7308 uu____7309
    | PatTvar (i, aq) ->
        let uu____7316 = aqual_to_string aq in
        let uu____7317 = FStar_Ident.string_of_id i in
        FStar_Util.format2 "%s%s" uu____7316 uu____7317
    | PatVar (i, aq) ->
        let uu____7324 = aqual_to_string aq in
        let uu____7325 = FStar_Ident.string_of_id i in
        FStar_Util.format2 "%s%s" uu____7324 uu____7325
    | PatName l -> FStar_Ident.string_of_lid l
    | PatList l ->
        let uu____7330 = to_string_l "; " pat_to_string l in
        FStar_Util.format1 "[%s]" uu____7330
    | PatTuple (l, false) ->
        let uu____7336 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(%s)" uu____7336
    | PatTuple (l, true) ->
        let uu____7342 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(|%s|)" uu____7342
    | PatRecord l ->
        let uu____7350 =
          to_string_l "; "
            (fun uu____7360 ->
               match uu____7360 with
               | (f, e) ->
                   let uu____7367 = FStar_Ident.string_of_lid f in
                   let uu____7368 = FStar_All.pipe_right e pat_to_string in
                   FStar_Util.format2 "%s=%s" uu____7367 uu____7368) l in
        FStar_Util.format1 "{%s}" uu____7350
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu____7373 = FStar_Ident.string_of_id op in
        FStar_Util.format1 "(%s)" uu____7373
    | PatAscribed (p, (t, FStar_Pervasives_Native.None)) ->
        let uu____7384 = FStar_All.pipe_right p pat_to_string in
        let uu____7385 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(%s:%s)" uu____7384 uu____7385
    | PatAscribed (p, (t, FStar_Pervasives_Native.Some tac)) ->
        let uu____7397 = FStar_All.pipe_right p pat_to_string in
        let uu____7398 = FStar_All.pipe_right t term_to_string in
        let uu____7399 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s:%s by %s)" uu____7397 uu____7398 uu____7399
and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___8_7400 ->
    match uu___8_7400 with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu____7412 =
          let uu____7413 = FStar_List.map term_to_string attrs in
          FStar_All.pipe_right uu____7413 (FStar_String.concat "; ") in
        FStar_Util.format1 "[@ %s]" uu____7412
let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i, uu____7429) ->
        let uu____7434 = FStar_Ident.lid_of_ids [i] in [uu____7434]
    | PatApp (p1, uu____7436) -> head_id_of_pat p1
    | PatAscribed (p1, uu____7442) -> head_id_of_pat p1
    | uu____7455 -> []
let lids_of_let :
  'uuuuuu7460 .
    (pattern * 'uuuuuu7460) Prims.list -> FStar_Ident.lident Prims.list
  =
  fun defs ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____7495 ->
            match uu____7495 with | (p, uu____7503) -> head_id_of_pat p))
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___9_7508 ->
    match uu___9_7508 with
    | TyconAbstract (i, uu____7510, uu____7511) -> FStar_Ident.string_of_id i
    | TyconAbbrev (i, uu____7521, uu____7522, uu____7523) ->
        FStar_Ident.string_of_id i
    | TyconRecord (i, uu____7533, uu____7534, uu____7535) ->
        FStar_Ident.string_of_id i
    | TyconVariant (i, uu____7557, uu____7558, uu____7559) ->
        FStar_Ident.string_of_id i
let (decl_to_string : decl -> Prims.string) =
  fun d ->
    match d.d with
    | TopLevelModule l ->
        let uu____7594 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "module " uu____7594
    | Open l ->
        let uu____7596 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "open " uu____7596
    | Friend l ->
        let uu____7598 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "friend " uu____7598
    | Include l ->
        let uu____7600 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "include " uu____7600
    | ModuleAbbrev (i, l) ->
        let uu____7603 = FStar_Ident.string_of_id i in
        let uu____7604 = FStar_Ident.string_of_lid l in
        FStar_Util.format2 "module %s = %s" uu____7603 uu____7604
    | TopLevelLet (uu____7605, pats) ->
        let uu____7619 =
          let uu____7620 =
            let uu____7623 = lids_of_let pats in
            FStar_All.pipe_right uu____7623
              (FStar_List.map (fun l -> FStar_Ident.string_of_lid l)) in
          FStar_All.pipe_right uu____7620 (FStar_String.concat ", ") in
        Prims.op_Hat "let " uu____7619
    | Assume (i, uu____7635) ->
        let uu____7636 = FStar_Ident.string_of_id i in
        Prims.op_Hat "assume " uu____7636
    | Tycon (uu____7637, uu____7638, tys) ->
        let uu____7644 =
          let uu____7645 =
            FStar_All.pipe_right tys (FStar_List.map id_of_tycon) in
          FStar_All.pipe_right uu____7645 (FStar_String.concat ", ") in
        Prims.op_Hat "type " uu____7644
    | Val (i, uu____7655) ->
        let uu____7656 = FStar_Ident.string_of_id i in
        Prims.op_Hat "val " uu____7656
    | Exception (i, uu____7658) ->
        let uu____7663 = FStar_Ident.string_of_id i in
        Prims.op_Hat "exception " uu____7663
    | NewEffect (DefineEffect (i, uu____7665, uu____7666, uu____7667)) ->
        let uu____7676 = FStar_Ident.string_of_id i in
        Prims.op_Hat "new_effect " uu____7676
    | NewEffect (RedefineEffect (i, uu____7678, uu____7679)) ->
        let uu____7684 = FStar_Ident.string_of_id i in
        Prims.op_Hat "new_effect " uu____7684
    | LayeredEffect (DefineEffect (i, uu____7686, uu____7687, uu____7688)) ->
        let uu____7697 = FStar_Ident.string_of_id i in
        Prims.op_Hat "layered_effect " uu____7697
    | LayeredEffect (RedefineEffect (i, uu____7699, uu____7700)) ->
        let uu____7705 = FStar_Ident.string_of_id i in
        Prims.op_Hat "layered_effect " uu____7705
    | Polymonadic_bind (l1, l2, l3, uu____7709) ->
        let uu____7710 = FStar_Ident.string_of_lid l1 in
        let uu____7711 = FStar_Ident.string_of_lid l2 in
        let uu____7712 = FStar_Ident.string_of_lid l3 in
        FStar_Util.format3 "polymonadic_bind (%s, %s) |> %s" uu____7710
          uu____7711 uu____7712
    | Polymonadic_subcomp (l1, l2, uu____7715) ->
        let uu____7716 = FStar_Ident.string_of_lid l1 in
        let uu____7717 = FStar_Ident.string_of_lid l2 in
        FStar_Util.format2 "polymonadic_subcomp %s <: %s" uu____7716
          uu____7717
    | Splice (ids, t) ->
        let uu____7724 =
          let uu____7725 =
            let uu____7726 =
              FStar_List.map (fun i -> FStar_Ident.string_of_id i) ids in
            FStar_All.pipe_left (FStar_String.concat ";") uu____7726 in
          let uu____7733 =
            let uu____7734 =
              let uu____7735 = term_to_string t in
              Prims.op_Hat uu____7735 ")" in
            Prims.op_Hat "] (" uu____7734 in
          Prims.op_Hat uu____7725 uu____7733 in
        Prims.op_Hat "splice[" uu____7724
    | SubEffect uu____7736 -> "sub_effect"
    | Pragma uu____7737 -> "pragma"
let (modul_to_string : modul -> Prims.string) =
  fun m ->
    match m with
    | Module (uu____7743, decls) ->
        let uu____7749 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____7749 (FStar_String.concat "\n")
    | Interface (uu____7758, decls, uu____7760) ->
        let uu____7765 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____7765 (FStar_String.concat "\n")
let (decl_is_val : FStar_Ident.ident -> decl -> Prims.bool) =
  fun id ->
    fun decl1 ->
      match decl1.d with
      | Val (id', uu____7785) -> FStar_Ident.ident_equals id id'
      | uu____7786 -> false
let (thunk : term -> term) =
  fun ens ->
    let wildpat = mk_pattern (PatWild FStar_Pervasives_Native.None) ens.range in
    mk_term (Abs ([wildpat], ens)) ens.range Expr
let (idents_of_binders :
  binder Prims.list -> FStar_Range.range -> FStar_Ident.ident Prims.list) =
  fun bs ->
    fun r ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun b ->
              match b.b with
              | Variable i -> i
              | TVariable i -> i
              | Annotated (i, uu____7821) -> i
              | TAnnotated (i, uu____7823) -> i
              | NoName uu____7824 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_MissingQuantifierBinder,
                      "Wildcard binders in quantifiers are not allowed") r))