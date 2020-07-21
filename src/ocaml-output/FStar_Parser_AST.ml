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
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Noeq -> true | uu____3083 -> false
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Unopteq -> true | uu____3089 -> false
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Assumption -> true | uu____3095 -> false
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | DefaultEffect -> true | uu____3101 -> false
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | TotalEffect -> true | uu____3107 -> false
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Effect_qual -> true | uu____3113 -> false
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | New -> true | uu____3119 -> false
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Inline -> true | uu____3125 -> false
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Visible -> true | uu____3131 -> false
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Unfold_for_unification_and_vcgen -> true
    | uu____3137 -> false
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Inline_for_extraction -> true
    | uu____3143 -> false
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Irreducible -> true | uu____3149 -> false
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | NoExtract -> true | uu____3155 -> false
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reifiable -> true | uu____3161 -> false
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reflectable -> true | uu____3167 -> false
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Opaque -> true | uu____3173 -> false
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Logic -> true | uu____3179 -> false
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee ->
    match projectee with | Qualifier _0 -> true | uu____3200 -> false
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee -> match projectee with | Qualifier _0 -> _0
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee ->
    match projectee with | DeclAttributes _0 -> true | uu____3215 -> false
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee -> match projectee with | DeclAttributes _0 -> _0
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | NonReifiableLift _0 -> true | uu____3253 -> false
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee -> match projectee with | NonReifiableLift _0 -> _0
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | ReifiableLift _0 -> true | uu____3270 -> false
let (__proj__ReifiableLift__item___0 : lift_op -> (term * term)) =
  fun projectee -> match projectee with | ReifiableLift _0 -> _0
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | LiftForFree _0 -> true | uu____3295 -> false
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
    match projectee with | SetOptions _0 -> true | uu____3366 -> false
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee -> match projectee with | SetOptions _0 -> _0
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | ResetOptions _0 -> true | uu____3381 -> false
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | ResetOptions _0 -> _0
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PushOptions _0 -> true | uu____3402 -> false
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | PushOptions _0 -> _0
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PopOptions -> true | uu____3420 -> false
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | RestartSolver -> true | uu____3426 -> false
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | LightOff -> true | uu____3432 -> false
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
    match projectee with | TopLevelModule _0 -> true | uu____3630 -> false
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TopLevelModule _0 -> _0
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Open _0 -> true | uu____3643 -> false
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Open _0 -> _0
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Friend _0 -> true | uu____3656 -> false
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Friend _0 -> _0
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Include _0 -> true | uu____3669 -> false
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Include _0 -> _0
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | ModuleAbbrev _0 -> true | uu____3686 -> false
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid)) =
  fun projectee -> match projectee with | ModuleAbbrev _0 -> _0
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelLet _0 -> true | uu____3721 -> false
let (__proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list)) =
  fun projectee -> match projectee with | TopLevelLet _0 -> _0
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tycon _0 -> true | uu____3772 -> false
let (__proj__Tycon__item___0 :
  decl' -> (Prims.bool * Prims.bool * tycon Prims.list)) =
  fun projectee -> match projectee with | Tycon _0 -> _0
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Val _0 -> true | uu____3813 -> false
let (__proj__Val__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Val _0 -> _0
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Exception _0 -> true | uu____3844 -> false
let (__proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Exception _0 -> _0
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | NewEffect _0 -> true | uu____3875 -> false
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee -> match projectee with | NewEffect _0 -> _0
let (uu___is_LayeredEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | LayeredEffect _0 -> true | uu____3888 -> false
let (__proj__LayeredEffect__item___0 : decl' -> effect_decl) =
  fun projectee -> match projectee with | LayeredEffect _0 -> _0
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | SubEffect _0 -> true | uu____3901 -> false
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee -> match projectee with | SubEffect _0 -> _0
let (uu___is_Polymonadic_bind : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Polymonadic_bind _0 -> true | uu____3922 -> false
let (__proj__Polymonadic_bind__item___0 :
  decl' -> (FStar_Ident.lid * FStar_Ident.lid * FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | Polymonadic_bind _0 -> _0
let (uu___is_Polymonadic_subcomp : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Polymonadic_subcomp _0 -> true
    | uu____3965 -> false
let (__proj__Polymonadic_subcomp__item___0 :
  decl' -> (FStar_Ident.lid * FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | Polymonadic_subcomp _0 -> _0
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pragma _0 -> true | uu____3996 -> false
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee -> match projectee with | Pragma _0 -> _0
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Assume _0 -> true | uu____4013 -> false
let (__proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Assume _0 -> _0
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Splice _0 -> true | uu____4044 -> false
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
    match projectee with | DefineEffect _0 -> true | uu____4123 -> false
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee -> match projectee with | DefineEffect _0 -> _0
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee ->
    match projectee with | RedefineEffect _0 -> true | uu____4180 -> false
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term)) =
  fun projectee -> match projectee with | RedefineEffect _0 -> _0
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee ->
    match projectee with | Module _0 -> true | uu____4247 -> false
let (__proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list))
  = fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee ->
    match projectee with | Interface _0 -> true | uu____4286 -> false
let (__proj__Interface__item___0 :
  modul -> (FStar_Ident.lid * decl Prims.list * Prims.bool)) =
  fun projectee -> match projectee with | Interface _0 -> _0
type file = modul
type inputFragment = (file, decl Prims.list) FStar_Util.either
let (decl_drange : decl -> FStar_Range.range) = fun decl1 -> decl1.drange
let (check_id : FStar_Ident.ident -> unit) =
  fun id ->
    let first_char =
      let uu____4334 = FStar_Ident.string_of_id id in
      FStar_String.substring uu____4334 Prims.int_zero Prims.int_one in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____4336 =
         let uu____4341 =
           let uu____4342 = FStar_Ident.string_of_id id in
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             uu____4342 in
         (FStar_Errors.Fatal_InvalidIdentifier, uu____4341) in
       let uu____4343 = FStar_Ident.range_of_id id in
       FStar_Errors.raise_error uu____4336 uu____4343)
let at_most_one :
  'uuuuuu4352 .
    Prims.string ->
      FStar_Range.range ->
        'uuuuuu4352 Prims.list -> 'uuuuuu4352 FStar_Pervasives_Native.option
  =
  fun s ->
    fun r ->
      fun l ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____4375 ->
            let uu____4378 =
              let uu____4383 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu____4383) in
            FStar_Errors.raise_error uu____4378 r
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d ->
    fun r ->
      fun decorations ->
        let attributes_1 =
          let uu____4410 =
            FStar_List.choose
              (fun uu___0_4419 ->
                 match uu___0_4419 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____4429 -> FStar_Pervasives_Native.None) decorations in
          at_most_one "attribute set" r uu____4410 in
        let attributes_2 = FStar_Util.dflt [] attributes_1 in
        let qualifiers1 =
          FStar_List.choose
            (fun uu___1_4444 ->
               match uu___1_4444 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____4448 -> FStar_Pervasives_Native.None) decorations in
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
            | uu____4531 ->
                let uu____4532 =
                  let uu____4539 = FStar_Ident.mk_ident ("-", rminus) in
                  (uu____4539, [t]) in
                Op uu____4532 in
          mk_term t1 r l
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p -> fun r -> { pat = p; prange = r }
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps ->
    fun body ->
      match body.tm with
      | Abs (p', body') -> Abs ((FStar_List.append ps p'), body')
      | uu____4574 -> Abs (ps, body)
let (mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches ->
    fun r1 ->
      fun r2 ->
        let x = FStar_Ident.gen r1 in
        let uu____4613 =
          let uu____4614 =
            let uu____4621 =
              let uu____4622 =
                let uu____4623 =
                  let uu____4638 =
                    let uu____4639 =
                      let uu____4640 = FStar_Ident.lid_of_ids [x] in
                      Var uu____4640 in
                    mk_term uu____4639 r1 Expr in
                  (uu____4638, branches) in
                Match uu____4623 in
              mk_term uu____4622 r2 Expr in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____4621) in
          Abs uu____4614 in
        mk_term uu____4613 r2 Expr
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p ->
    fun tm ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____4677, Abs (pats, body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____4696 -> FStar_Pervasives_Native.None
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid ->
    fun r ->
      let uu____4715 = FStar_Ident.path_of_lid lid in
      FStar_Ident.lid_of_path uu____4715 r
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
        | uu____4902 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____4916 ->
                 FStar_List.fold_left
                   (fun t1 ->
                      fun uu____4926 ->
                        match uu____4926 with
                        | (a, imp1) -> mk_term (App (t1, a, imp1)) r Un) t
                   args)
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r ->
    fun elts ->
      let uu____4947 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid) in
      match uu____4947 with
      | (empty_lid, singleton_lid, union_lid, addr_of_lid) ->
          let empty =
            let uu____4961 =
              let uu____4962 = FStar_Ident.set_lid_range empty_lid r in
              Var uu____4962 in
            mk_term uu____4961 r Expr in
          let addr_of =
            let uu____4964 =
              let uu____4965 = FStar_Ident.set_lid_range addr_of_lid r in
              Var uu____4965 in
            mk_term uu____4964 r Expr in
          let singleton =
            let uu____4967 =
              let uu____4968 = FStar_Ident.set_lid_range singleton_lid r in
              Var uu____4968 in
            mk_term uu____4967 r Expr in
          let union =
            let uu____4970 =
              let uu____4971 = FStar_Ident.set_lid_range union_lid r in
              Var uu____4971 in
            mk_term uu____4970 r Expr in
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
        | uu____5027 ->
            (match t.tm with
             | Name s ->
                 let uu____5031 =
                   let uu____5032 =
                     let uu____5043 =
                       FStar_List.map (fun a -> (a, Nothing)) args in
                     (s, uu____5043) in
                   Construct uu____5032 in
                 mk_term uu____5031 r Un
             | uu____5062 ->
                 FStar_List.fold_left
                   (fun t1 -> fun a -> mk_term (App (t1, a, Nothing)) r Un) t
                   args)
let (unit_const : FStar_Range.range -> term) =
  fun r -> mk_term (Const FStar_Const.Const_unit) r Expr
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r ->
    let admit =
      let admit_name =
        let uu____5079 =
          let uu____5080 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r in
          Var uu____5080 in
        mk_term uu____5079 r Expr in
      mkExplicitApp admit_name [unit_const r] r in
    let magic =
      let magic_name =
        let uu____5083 =
          let uu____5084 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r in
          Var uu____5084 in
        mk_term uu____5083 r Expr in
      mkExplicitApp magic_name [unit_const r] r in
    let admit_magic = mk_term (Seq (admit, magic)) r Expr in admit_magic
let mkWildAdmitMagic :
  'uuuuuu5090 .
    FStar_Range.range ->
      (pattern * 'uuuuuu5090 FStar_Pervasives_Native.option * term)
  =
  fun r ->
    let uu____5104 = mkAdmitMagic r in
    ((mk_pattern (PatWild FStar_Pervasives_Native.None) r),
      FStar_Pervasives_Native.None, uu____5104)
let focusBranches :
  'uuuuuu5113 .
    (Prims.bool * (pattern * 'uuuuuu5113 FStar_Pervasives_Native.option *
      term)) Prims.list ->
      FStar_Range.range ->
        (pattern * 'uuuuuu5113 FStar_Pervasives_Native.option * term)
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
            let uu____5205 =
              FStar_List.filter FStar_Pervasives_Native.fst branches in
            FStar_All.pipe_right uu____5205
              (FStar_List.map FStar_Pervasives_Native.snd) in
          let uu____5292 =
            let uu____5303 = mkWildAdmitMagic r in [uu____5303] in
          FStar_List.append focussed uu____5292))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
let focusLetBindings :
  'uuuuuu5395 .
    (Prims.bool * ('uuuuuu5395 * term)) Prims.list ->
      FStar_Range.range -> ('uuuuuu5395 * term) Prims.list
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
           (fun uu____5467 ->
              match uu____5467 with
              | (f, lb) ->
                  if f
                  then lb
                  else
                    (let uu____5495 = mkAdmitMagic r in
                     ((FStar_Pervasives_Native.fst lb), uu____5495))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
let focusAttrLetBindings :
  'uuuuuu5537 'uuuuuu5538 .
    ('uuuuuu5537 * (Prims.bool * ('uuuuuu5538 * term))) Prims.list ->
      FStar_Range.range -> ('uuuuuu5537 * ('uuuuuu5538 * term)) Prims.list
  =
  fun lbs ->
    fun r ->
      let should_filter =
        FStar_Util.for_some
          (fun uu____5604 ->
             match uu____5604 with | (attr, (focus, uu____5619)) -> focus)
          lbs in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____5671 ->
              match uu____5671 with
              | (attr, (f, lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu____5724 =
                       let uu____5729 = mkAdmitMagic r in
                       ((FStar_Pervasives_Native.fst lb), uu____5729) in
                     (attr, uu____5724))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu____5783 ->
                match uu____5783 with
                | (attr, (uu____5805, lb)) -> (attr, lb)))
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun args ->
      fun r ->
        let uu____5846 = FStar_List.map (fun a -> (a, FsTypApp)) args in
        mkApp t uu____5846 r
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args ->
    fun r ->
      let cons =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r in
      let uu____5874 = FStar_List.map (fun x -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu____5874 r
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args ->
    fun r ->
      let cons =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r in
      let uu____5902 = FStar_List.map (fun x -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu____5902 r
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
                       | PatVar (x, uu____5995) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____6000 ->
                           let x = FStar_Ident.gen t_range in
                           let phi1 =
                             let x_var =
                               let uu____6004 =
                                 let uu____6005 = FStar_Ident.lid_of_ids [x] in
                                 Var uu____6005 in
                               mk_term uu____6004 phi.range Formula in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi) in
                             let otherwise_branch =
                               let uu____6026 =
                                 let uu____6027 =
                                   let uu____6028 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range in
                                   Name uu____6028 in
                                 mk_term uu____6027 phi.range Formula in
                               ((mk_pattern
                                   (PatWild FStar_Pervasives_Native.None)
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu____6026) in
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
        ({ b = Annotated (x, t); brange = uu____6114; blevel = uu____6115;
           aqual = uu____6116;_},
         t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____6131 -> FStar_Pervasives_Native.None
let rec (as_mlist :
  ((FStar_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul) =
  fun cur ->
    fun ds ->
      let uu____6174 = cur in
      match uu____6174 with
      | ((m_name, m_decl), cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu____6203 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light ->
    fun light_range ->
      fun ds ->
        let uu____6229 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag in
        match uu____6229 with
        | (d, ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____6266 =
                       mk_decl (Pragma LightOff) light_range [] in
                     uu____6266 :: ds1
                   else ds1 in
                 let m1 = as_mlist ((m, d), []) ds2 in FStar_Util.Inl m1
             | uu____6277 ->
                 let ds2 = d :: ds1 in
                 (FStar_List.iter
                    (fun uu___2_6287 ->
                       match uu___2_6287 with
                       | { d = TopLevelModule uu____6288; drange = r;
                           quals = uu____6290; attrs = uu____6291;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu____6292 -> ()) ds2;
                  FStar_Util.Inr ds2))
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity ->
    fun s ->
      fun r ->
        let name_of_char uu___3_6315 =
          match uu___3_6315 with
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
        | uu____6317 ->
            let uu____6318 =
              let uu____6319 =
                let uu____6322 = FStar_String.list_of_string s in
                FStar_List.map name_of_char uu____6322 in
              FStar_String.concat "_" uu____6319 in
            Prims.op_Hat "op_" uu____6318
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s -> fun r -> compile_op (~- Prims.int_one) s r
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu____6349 ->
    match uu____6349 with
    | (comment, keywords) ->
        let uu____6374 =
          let uu____6375 =
            FStar_List.map
              (fun uu____6385 ->
                 match uu____6385 with
                 | (k, v) -> Prims.op_Hat k (Prims.op_Hat "->" v)) keywords in
          FStar_String.concat "," uu____6375 in
        Prims.op_Hat comment uu____6374
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___4_6396 ->
    match uu___4_6396 with | NoLetQualifier -> "" | Rec -> "rec"
let to_string_l :
  'uuuuuu6405 .
    Prims.string ->
      ('uuuuuu6405 -> Prims.string) -> 'uuuuuu6405 Prims.list -> Prims.string
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu____6430 = FStar_List.map f l in
        FStar_String.concat sep uu____6430
let (imp_to_string : imp -> Prims.string) =
  fun uu___5_6437 -> match uu___5_6437 with | Hash -> "#" | uu____6438 -> ""
let rec (term_to_string : term -> Prims.string) =
  fun x ->
    match x.tm with
    | Wild -> "_"
    | Requires (t, uu____6471) ->
        let uu____6476 = term_to_string t in
        FStar_Util.format1 "(requires %s)" uu____6476
    | Ensures (t, uu____6478) ->
        let uu____6483 = term_to_string t in
        FStar_Util.format1 "(ensures %s)" uu____6483
    | Labeled (t, l, uu____6486) ->
        let uu____6487 = term_to_string t in
        FStar_Util.format2 "(labeled %s %s)" l uu____6487
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s, xs) ->
        let uu____6495 = FStar_Ident.string_of_id s in
        let uu____6496 =
          let uu____6497 =
            FStar_List.map (fun x1 -> FStar_All.pipe_right x1 term_to_string)
              xs in
          FStar_String.concat ", " uu____6497 in
        FStar_Util.format2 "%s(%s)" uu____6495 uu____6496
    | Tvar id -> FStar_Ident.string_of_id id
    | Uvar id -> FStar_Ident.string_of_id id
    | Var l -> FStar_Ident.string_of_lid l
    | Name l -> FStar_Ident.string_of_lid l
    | Projector (rec_lid, field_id) ->
        let uu____6508 = FStar_Ident.string_of_lid rec_lid in
        let uu____6509 = FStar_Ident.string_of_id field_id in
        FStar_Util.format2 "%s?.%s" uu____6508 uu____6509
    | Construct (l, args) ->
        let uu____6524 = FStar_Ident.string_of_lid l in
        let uu____6525 =
          to_string_l " "
            (fun uu____6534 ->
               match uu____6534 with
               | (a, imp1) ->
                   let uu____6541 = term_to_string a in
                   FStar_Util.format2 "%s%s" (imp_to_string imp1) uu____6541)
            args in
        FStar_Util.format2 "(%s %s)" uu____6524 uu____6525
    | Abs (pats, t) ->
        let uu____6548 = to_string_l " " pat_to_string pats in
        let uu____6549 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(fun %s -> %s)" uu____6548 uu____6549
    | App (t1, t2, imp1) ->
        let uu____6553 = FStar_All.pipe_right t1 term_to_string in
        let uu____6554 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format3 "%s %s%s" uu____6553 (imp_to_string imp1)
          uu____6554
    | Let (Rec, (a, (p, b))::lbs, body) ->
        let uu____6612 = attrs_opt_to_string a in
        let uu____6613 =
          let uu____6614 = FStar_All.pipe_right p pat_to_string in
          let uu____6615 = FStar_All.pipe_right b term_to_string in
          FStar_Util.format2 "%s=%s" uu____6614 uu____6615 in
        let uu____6616 =
          to_string_l " "
            (fun uu____6636 ->
               match uu____6636 with
               | (a1, (p1, b1)) ->
                   let uu____6664 = attrs_opt_to_string a1 in
                   let uu____6665 = FStar_All.pipe_right p1 pat_to_string in
                   let uu____6666 = FStar_All.pipe_right b1 term_to_string in
                   FStar_Util.format3 "%sand %s=%s" uu____6664 uu____6665
                     uu____6666) lbs in
        let uu____6667 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format4 "%slet rec %s%s in %s" uu____6612 uu____6613
          uu____6616 uu____6667
    | Let (q, (attrs, (pat, tm))::[], body) ->
        let uu____6723 = attrs_opt_to_string attrs in
        let uu____6724 = FStar_All.pipe_right pat pat_to_string in
        let uu____6725 = FStar_All.pipe_right tm term_to_string in
        let uu____6726 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu____6723
          (string_of_let_qualifier q) uu____6724 uu____6725 uu____6726
    | Let (uu____6727, uu____6728, uu____6729) ->
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_EmptySurfaceLet,
            "Internal error: found an invalid surface Let") x.range
    | LetOpen (lid, t) ->
        let uu____6760 = FStar_Ident.string_of_lid lid in
        let uu____6761 = term_to_string t in
        FStar_Util.format2 "let open %s in %s" uu____6760 uu____6761
    | Seq (t1, t2) ->
        let uu____6764 = FStar_All.pipe_right t1 term_to_string in
        let uu____6765 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "%s; %s" uu____6764 uu____6765
    | Bind (id, t1, t2) ->
        let uu____6769 = FStar_Ident.string_of_id id in
        let uu____6770 = term_to_string t1 in
        let uu____6771 = term_to_string t2 in
        FStar_Util.format3 "%s <- %s; %s" uu____6769 uu____6770 uu____6771
    | If (t1, t2, t3) ->
        let uu____6775 = FStar_All.pipe_right t1 term_to_string in
        let uu____6776 = FStar_All.pipe_right t2 term_to_string in
        let uu____6777 = FStar_All.pipe_right t3 term_to_string in
        FStar_Util.format3 "if %s then %s else %s" uu____6775 uu____6776
          uu____6777
    | Match (t, branches) ->
        let s =
          match x.tm with
          | Match uu____6801 -> "match"
          | TryWith uu____6816 -> "try"
          | uu____6831 -> failwith "impossible" in
        let uu____6832 = FStar_All.pipe_right t term_to_string in
        let uu____6833 =
          to_string_l " | "
            (fun uu____6849 ->
               match uu____6849 with
               | (p, w, e) ->
                   let uu____6865 = FStar_All.pipe_right p pat_to_string in
                   let uu____6866 =
                     match w with
                     | FStar_Pervasives_Native.None -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____6868 = term_to_string e1 in
                         FStar_Util.format1 "when %s" uu____6868 in
                   let uu____6869 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____6865 uu____6866
                     uu____6869) branches in
        FStar_Util.format3 "%s %s with %s" s uu____6832 uu____6833
    | TryWith (t, branches) ->
        let s =
          match x.tm with
          | Match uu____6893 -> "match"
          | TryWith uu____6908 -> "try"
          | uu____6923 -> failwith "impossible" in
        let uu____6924 = FStar_All.pipe_right t term_to_string in
        let uu____6925 =
          to_string_l " | "
            (fun uu____6941 ->
               match uu____6941 with
               | (p, w, e) ->
                   let uu____6957 = FStar_All.pipe_right p pat_to_string in
                   let uu____6958 =
                     match w with
                     | FStar_Pervasives_Native.None -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____6960 = term_to_string e1 in
                         FStar_Util.format1 "when %s" uu____6960 in
                   let uu____6961 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____6957 uu____6958
                     uu____6961) branches in
        FStar_Util.format3 "%s %s with %s" s uu____6924 uu____6925
    | Ascribed (t1, t2, FStar_Pervasives_Native.None) ->
        let uu____6966 = FStar_All.pipe_right t1 term_to_string in
        let uu____6967 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "(%s : %s)" uu____6966 uu____6967
    | Ascribed (t1, t2, FStar_Pervasives_Native.Some tac) ->
        let uu____6973 = FStar_All.pipe_right t1 term_to_string in
        let uu____6974 = FStar_All.pipe_right t2 term_to_string in
        let uu____6975 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s : %s by %s)" uu____6973 uu____6974 uu____6975
    | Record (FStar_Pervasives_Native.Some e, fields) ->
        let uu____6992 = FStar_All.pipe_right e term_to_string in
        let uu____6993 =
          to_string_l " "
            (fun uu____7003 ->
               match uu____7003 with
               | (l, e1) ->
                   let uu____7010 = FStar_Ident.string_of_lid l in
                   let uu____7011 = FStar_All.pipe_right e1 term_to_string in
                   FStar_Util.format2 "%s=%s" uu____7010 uu____7011) fields in
        FStar_Util.format2 "{%s with %s}" uu____6992 uu____6993
    | Record (FStar_Pervasives_Native.None, fields) ->
        let uu____7027 =
          to_string_l " "
            (fun uu____7037 ->
               match uu____7037 with
               | (l, e) ->
                   let uu____7044 = FStar_Ident.string_of_lid l in
                   let uu____7045 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format2 "%s=%s" uu____7044 uu____7045) fields in
        FStar_Util.format1 "{%s}" uu____7027
    | Project (e, l) ->
        let uu____7048 = FStar_All.pipe_right e term_to_string in
        let uu____7049 = FStar_Ident.string_of_lid l in
        FStar_Util.format2 "%s.%s" uu____7048 uu____7049
    | Product ([], t) -> term_to_string t
    | Product (b::hd::tl, t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd :: tl), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[], t) when x.level = Type_level ->
        let uu____7069 = FStar_All.pipe_right b binder_to_string in
        let uu____7070 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s -> %s" uu____7069 uu____7070
    | Product (b::[], t) when x.level = Kind ->
        let uu____7075 = FStar_All.pipe_right b binder_to_string in
        let uu____7076 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s => %s" uu____7075 uu____7076
    | Sum (binders, t) ->
        let uu____7091 =
          FStar_All.pipe_right (FStar_List.append binders [FStar_Util.Inr t])
            (FStar_List.map
               (fun uu___6_7120 ->
                  match uu___6_7120 with
                  | FStar_Util.Inl b -> binder_to_string b
                  | FStar_Util.Inr t1 -> term_to_string t1)) in
        FStar_All.pipe_right uu____7091 (FStar_String.concat " & ")
    | QForall (bs, (uu____7130, pats), t) ->
        let uu____7159 = to_string_l " " binder_to_string bs in
        let uu____7160 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____7163 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____7159 uu____7160
          uu____7163
    | QExists (bs, (uu____7165, pats), t) ->
        let uu____7194 = to_string_l " " binder_to_string bs in
        let uu____7195 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____7198 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____7194 uu____7195
          uu____7198
    | Refine (b, t) ->
        let uu____7201 = FStar_All.pipe_right b binder_to_string in
        let uu____7202 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:{%s}" uu____7201 uu____7202
    | NamedTyp (x1, t) ->
        let uu____7205 = FStar_Ident.string_of_id x1 in
        let uu____7206 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:%s" uu____7205 uu____7206
    | Paren t ->
        let uu____7208 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format1 "(%s)" uu____7208
    | Product (bs, t) ->
        let uu____7215 =
          let uu____7216 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____7216 (FStar_String.concat ",") in
        let uu____7225 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____7215
          uu____7225
    | Discrim lid ->
        let uu____7227 = FStar_Ident.string_of_lid lid in
        FStar_Util.format1 "%s?" uu____7227
    | Attributes ts ->
        let uu____7231 =
          let uu____7232 = FStar_List.map term_to_string ts in
          FStar_All.pipe_left (FStar_String.concat " ") uu____7232 in
        FStar_Util.format1 "(attributes %s)" uu____7231
    | Antiquote t ->
        let uu____7238 = term_to_string t in
        FStar_Util.format1 "(`#%s)" uu____7238
    | Quote (t, Static) ->
        let uu____7240 = term_to_string t in
        FStar_Util.format1 "(`(%s))" uu____7240
    | Quote (t, Dynamic) ->
        let uu____7242 = term_to_string t in
        FStar_Util.format1 "quote (%s)" uu____7242
    | VQuote t ->
        let uu____7244 = term_to_string t in
        FStar_Util.format1 "`%%%s" uu____7244
    | CalcProof (rel, init, steps) ->
        let uu____7252 = term_to_string rel in
        let uu____7253 = term_to_string init in
        let uu____7254 =
          let uu____7255 = FStar_List.map calc_step_to_string steps in
          FStar_All.pipe_left (FStar_String.concat " ") uu____7255 in
        FStar_Util.format3 "calc (%s) { %s %s }" uu____7252 uu____7253
          uu____7254
and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu____7260 ->
    match uu____7260 with
    | CalcStep (rel, just, next) ->
        let uu____7264 = term_to_string rel in
        let uu____7265 = term_to_string just in
        let uu____7266 = term_to_string next in
        FStar_Util.format3 "%s{ %s } %s" uu____7264 uu____7265 uu____7266
and (binder_to_string : binder -> Prims.string) =
  fun x ->
    let s =
      match x.b with
      | Variable i -> FStar_Ident.string_of_id i
      | TVariable i ->
          let uu____7271 = FStar_Ident.string_of_id i in
          FStar_Util.format1 "%s:_" uu____7271
      | TAnnotated (i, t) ->
          let uu____7274 = FStar_Ident.string_of_id i in
          let uu____7275 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" uu____7274 uu____7275
      | Annotated (i, t) ->
          let uu____7278 = FStar_Ident.string_of_id i in
          let uu____7279 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" uu____7278 uu____7279
      | NoName t -> FStar_All.pipe_right t term_to_string in
    let uu____7281 = aqual_to_string x.aqual in
    FStar_Util.format2 "%s%s" uu____7281 s
and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___7_7282 ->
    match uu___7_7282 with
    | FStar_Pervasives_Native.Some (Equality) -> "$"
    | FStar_Pervasives_Native.Some (Implicit) -> "#"
    | uu____7285 -> ""
and (pat_to_string : pattern -> Prims.string) =
  fun x ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None) -> "_"
    | PatWild uu____7289 -> "#_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p, ps) ->
        let uu____7299 = FStar_All.pipe_right p pat_to_string in
        let uu____7300 = to_string_l " " pat_to_string ps in
        FStar_Util.format2 "(%s %s)" uu____7299 uu____7300
    | PatTvar (i, aq) ->
        let uu____7307 = aqual_to_string aq in
        let uu____7308 = FStar_Ident.string_of_id i in
        FStar_Util.format2 "%s%s" uu____7307 uu____7308
    | PatVar (i, aq) ->
        let uu____7315 = aqual_to_string aq in
        let uu____7316 = FStar_Ident.string_of_id i in
        FStar_Util.format2 "%s%s" uu____7315 uu____7316
    | PatName l -> FStar_Ident.string_of_lid l
    | PatList l ->
        let uu____7321 = to_string_l "; " pat_to_string l in
        FStar_Util.format1 "[%s]" uu____7321
    | PatTuple (l, false) ->
        let uu____7327 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(%s)" uu____7327
    | PatTuple (l, true) ->
        let uu____7333 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(|%s|)" uu____7333
    | PatRecord l ->
        let uu____7341 =
          to_string_l "; "
            (fun uu____7351 ->
               match uu____7351 with
               | (f, e) ->
                   let uu____7358 = FStar_Ident.string_of_lid f in
                   let uu____7359 = FStar_All.pipe_right e pat_to_string in
                   FStar_Util.format2 "%s=%s" uu____7358 uu____7359) l in
        FStar_Util.format1 "{%s}" uu____7341
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu____7364 = FStar_Ident.string_of_id op in
        FStar_Util.format1 "(%s)" uu____7364
    | PatAscribed (p, (t, FStar_Pervasives_Native.None)) ->
        let uu____7375 = FStar_All.pipe_right p pat_to_string in
        let uu____7376 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(%s:%s)" uu____7375 uu____7376
    | PatAscribed (p, (t, FStar_Pervasives_Native.Some tac)) ->
        let uu____7388 = FStar_All.pipe_right p pat_to_string in
        let uu____7389 = FStar_All.pipe_right t term_to_string in
        let uu____7390 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s:%s by %s)" uu____7388 uu____7389 uu____7390
and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___8_7391 ->
    match uu___8_7391 with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu____7403 =
          let uu____7404 = FStar_List.map term_to_string attrs in
          FStar_All.pipe_right uu____7404 (FStar_String.concat "; ") in
        FStar_Util.format1 "[@ %s]" uu____7403
let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i, uu____7420) ->
        let uu____7425 = FStar_Ident.lid_of_ids [i] in [uu____7425]
    | PatApp (p1, uu____7427) -> head_id_of_pat p1
    | PatAscribed (p1, uu____7433) -> head_id_of_pat p1
    | uu____7446 -> []
let lids_of_let :
  'uuuuuu7451 .
    (pattern * 'uuuuuu7451) Prims.list -> FStar_Ident.lident Prims.list
  =
  fun defs ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____7486 ->
            match uu____7486 with | (p, uu____7494) -> head_id_of_pat p))
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___9_7499 ->
    match uu___9_7499 with
    | TyconAbstract (i, uu____7501, uu____7502) -> FStar_Ident.string_of_id i
    | TyconAbbrev (i, uu____7512, uu____7513, uu____7514) ->
        FStar_Ident.string_of_id i
    | TyconRecord (i, uu____7524, uu____7525, uu____7526) ->
        FStar_Ident.string_of_id i
    | TyconVariant (i, uu____7548, uu____7549, uu____7550) ->
        FStar_Ident.string_of_id i
let (decl_to_string : decl -> Prims.string) =
  fun d ->
    match d.d with
    | TopLevelModule l ->
        let uu____7585 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "module " uu____7585
    | Open l ->
        let uu____7587 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "open " uu____7587
    | Friend l ->
        let uu____7589 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "friend " uu____7589
    | Include l ->
        let uu____7591 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "include " uu____7591
    | ModuleAbbrev (i, l) ->
        let uu____7594 = FStar_Ident.string_of_id i in
        let uu____7595 = FStar_Ident.string_of_lid l in
        FStar_Util.format2 "module %s = %s" uu____7594 uu____7595
    | TopLevelLet (uu____7596, pats) ->
        let uu____7610 =
          let uu____7611 =
            let uu____7614 = lids_of_let pats in
            FStar_All.pipe_right uu____7614
              (FStar_List.map (fun l -> FStar_Ident.string_of_lid l)) in
          FStar_All.pipe_right uu____7611 (FStar_String.concat ", ") in
        Prims.op_Hat "let " uu____7610
    | Assume (i, uu____7626) ->
        let uu____7627 = FStar_Ident.string_of_id i in
        Prims.op_Hat "assume " uu____7627
    | Tycon (uu____7628, uu____7629, tys) ->
        let uu____7635 =
          let uu____7636 =
            FStar_All.pipe_right tys (FStar_List.map id_of_tycon) in
          FStar_All.pipe_right uu____7636 (FStar_String.concat ", ") in
        Prims.op_Hat "type " uu____7635
    | Val (i, uu____7646) ->
        let uu____7647 = FStar_Ident.string_of_id i in
        Prims.op_Hat "val " uu____7647
    | Exception (i, uu____7649) ->
        let uu____7654 = FStar_Ident.string_of_id i in
        Prims.op_Hat "exception " uu____7654
    | NewEffect (DefineEffect (i, uu____7656, uu____7657, uu____7658)) ->
        let uu____7667 = FStar_Ident.string_of_id i in
        Prims.op_Hat "new_effect " uu____7667
    | NewEffect (RedefineEffect (i, uu____7669, uu____7670)) ->
        let uu____7675 = FStar_Ident.string_of_id i in
        Prims.op_Hat "new_effect " uu____7675
    | LayeredEffect (DefineEffect (i, uu____7677, uu____7678, uu____7679)) ->
        let uu____7688 = FStar_Ident.string_of_id i in
        Prims.op_Hat "layered_effect " uu____7688
    | LayeredEffect (RedefineEffect (i, uu____7690, uu____7691)) ->
        let uu____7696 = FStar_Ident.string_of_id i in
        Prims.op_Hat "layered_effect " uu____7696
    | Polymonadic_bind (l1, l2, l3, uu____7700) ->
        let uu____7701 = FStar_Ident.string_of_lid l1 in
        let uu____7702 = FStar_Ident.string_of_lid l2 in
        let uu____7703 = FStar_Ident.string_of_lid l3 in
        FStar_Util.format3 "polymonadic_bind (%s, %s) |> %s" uu____7701
          uu____7702 uu____7703
    | Polymonadic_subcomp (l1, l2, uu____7706) ->
        let uu____7707 = FStar_Ident.string_of_lid l1 in
        let uu____7708 = FStar_Ident.string_of_lid l2 in
        FStar_Util.format2 "polymonadic_subcomp %s <: %s" uu____7707
          uu____7708
    | Splice (ids, t) ->
        let uu____7715 =
          let uu____7716 =
            let uu____7717 =
              FStar_List.map (fun i -> FStar_Ident.string_of_id i) ids in
            FStar_All.pipe_left (FStar_String.concat ";") uu____7717 in
          let uu____7724 =
            let uu____7725 =
              let uu____7726 = term_to_string t in
              Prims.op_Hat uu____7726 ")" in
            Prims.op_Hat "] (" uu____7725 in
          Prims.op_Hat uu____7716 uu____7724 in
        Prims.op_Hat "splice[" uu____7715
    | SubEffect uu____7727 -> "sub_effect"
    | Pragma uu____7728 -> "pragma"
let (modul_to_string : modul -> Prims.string) =
  fun m ->
    match m with
    | Module (uu____7734, decls) ->
        let uu____7740 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____7740 (FStar_String.concat "\n")
    | Interface (uu____7749, decls, uu____7751) ->
        let uu____7756 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____7756 (FStar_String.concat "\n")
let (decl_is_val : FStar_Ident.ident -> decl -> Prims.bool) =
  fun id ->
    fun decl1 ->
      match decl1.d with
      | Val (id', uu____7776) -> FStar_Ident.ident_equals id id'
      | uu____7777 -> false
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
              | Annotated (i, uu____7812) -> i
              | TAnnotated (i, uu____7814) -> i
              | NoName uu____7815 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_MissingQuantifierBinder,
                      "Wildcard binders in quantifiers are not allowed") r))