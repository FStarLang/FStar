open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let (uu___is_Un : level -> Prims.bool) =
  fun projectee  -> match projectee with | Un  -> true | uu____26 -> false 
let (uu___is_Expr : level -> Prims.bool) =
  fun projectee  -> match projectee with | Expr  -> true | uu____37 -> false 
let (uu___is_Type_level : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____48 -> false
  
let (uu___is_Kind : level -> Prims.bool) =
  fun projectee  -> match projectee with | Kind  -> true | uu____59 -> false 
let (uu___is_Formula : level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____70 -> false
  
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let (uu___is_NoLetQualifier : let_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____81 -> false
  
let (uu___is_Rec : let_qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | Rec  -> true | uu____92 -> false 
type quote_kind =
  | Static 
  | Dynamic 
let (uu___is_Static : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Static  -> true | uu____103 -> false
  
let (uu___is_Dynamic : quote_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dynamic  -> true | uu____114 -> false
  
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
  | Sum of ((binder,term) FStar_Util.either Prims.list * term) 
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
  | Meta of term 
and imp =
  | FsTypApp 
  | Hash 
  | UnivApp 
  | HashBrace of term 
  | Infix 
  | Nothing 
let (uu___is_Wild : term' -> Prims.bool) =
  fun projectee  -> match projectee with | Wild  -> true | uu____733 -> false 
let (uu___is_Const : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____745 -> false
  
let (__proj__Const__item___0 : term' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee  -> match projectee with | Op _0 -> true | uu____770 -> false 
let (__proj__Op__item___0 : term' -> (FStar_Ident.ident * term Prims.list)) =
  fun projectee  -> match projectee with | Op _0 -> _0 
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____807 -> false
  
let (__proj__Tvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Tvar _0 -> _0 
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____826 -> false
  
let (__proj__Uvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Uvar _0 -> _0 
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____845 -> false
  
let (__proj__Var__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____864 -> false
  
let (__proj__Name__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Name _0 -> _0 
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____887 -> false
  
let (__proj__Projector__item___0 :
  term' -> (FStar_Ident.lid * FStar_Ident.ident)) =
  fun projectee  -> match projectee with | Projector _0 -> _0 
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____928 -> false
  
let (__proj__Construct__item___0 :
  term' -> (FStar_Ident.lid * (term * imp) Prims.list)) =
  fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____983 -> false
  
let (__proj__Abs__item___0 : term' -> (pattern Prims.list * term)) =
  fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1026 -> false
  
let (__proj__App__item___0 : term' -> (term * term * imp)) =
  fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1083 -> false
  
let (__proj__Let__item___0 :
  term' ->
    (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
      (pattern * term)) Prims.list * term))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____1166 -> false
  
let (__proj__LetOpen__item___0 : term' -> (FStar_Ident.lid * term)) =
  fun projectee  -> match projectee with | LetOpen _0 -> _0 
let (uu___is_Seq : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____1201 -> false
  
let (__proj__Seq__item___0 : term' -> (term * term)) =
  fun projectee  -> match projectee with | Seq _0 -> _0 
let (uu___is_Bind : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____1238 -> false
  
let (__proj__Bind__item___0 : term' -> (FStar_Ident.ident * term * term)) =
  fun projectee  -> match projectee with | Bind _0 -> _0 
let (uu___is_If : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | If _0 -> true | uu____1281 -> false
  
let (__proj__If__item___0 : term' -> (term * term * term)) =
  fun projectee  -> match projectee with | If _0 -> _0 
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____1332 -> false
  
let (__proj__Match__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_TryWith : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____1407 -> false
  
let (__proj__TryWith__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee  -> match projectee with | TryWith _0 -> _0 
let (uu___is_Ascribed : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____1476 -> false
  
let (__proj__Ascribed__item___0 :
  term' -> (term * term * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ascribed _0 -> _0 
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____1531 -> false
  
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
      Prims.list))
  = fun projectee  -> match projectee with | Record _0 -> _0 
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____1590 -> false
  
let (__proj__Project__item___0 : term' -> (term * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | Project _0 -> _0 
let (uu___is_Product : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____1627 -> false
  
let (__proj__Product__item___0 : term' -> (binder Prims.list * term)) =
  fun projectee  -> match projectee with | Product _0 -> _0 
let (uu___is_Sum : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____1674 -> false
  
let (__proj__Sum__item___0 :
  term' -> ((binder,term) FStar_Util.either Prims.list * term)) =
  fun projectee  -> match projectee with | Sum _0 -> _0 
let (uu___is_QForall : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____1741 -> false
  
let (__proj__QForall__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee  -> match projectee with | QForall _0 -> _0 
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____1832 -> false
  
let (__proj__QExists__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee  -> match projectee with | QExists _0 -> _0 
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____1909 -> false
  
let (__proj__Refine__item___0 : term' -> (binder * term)) =
  fun projectee  -> match projectee with | Refine _0 -> _0 
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____1944 -> false
  
let (__proj__NamedTyp__item___0 : term' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0 
let (uu___is_Paren : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____1975 -> false
  
let (__proj__Paren__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Paren _0 -> _0 
let (uu___is_Requires : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____2001 -> false
  
let (__proj__Requires__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Requires _0 -> _0 
let (uu___is_Ensures : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____2048 -> false
  
let (__proj__Ensures__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Ensures _0 -> _0 
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____2096 -> false
  
let (__proj__Labeled__item___0 : term' -> (term * Prims.string * Prims.bool))
  = fun projectee  -> match projectee with | Labeled _0 -> _0 
let (uu___is_Discrim : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____2139 -> false
  
let (__proj__Discrim__item___0 : term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Discrim _0 -> _0 
let (uu___is_Attributes : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____2160 -> false
  
let (__proj__Attributes__item___0 : term' -> term Prims.list) =
  fun projectee  -> match projectee with | Attributes _0 -> _0 
let (uu___is_Antiquote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Antiquote _0 -> true | uu____2185 -> false
  
let (__proj__Antiquote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | Antiquote _0 -> _0 
let (uu___is_Quote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____2208 -> false
  
let (__proj__Quote__item___0 : term' -> (term * quote_kind)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_VQuote : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VQuote _0 -> true | uu____2239 -> false
  
let (__proj__VQuote__item___0 : term' -> term) =
  fun projectee  -> match projectee with | VQuote _0 -> _0 
let (uu___is_CalcProof : term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | CalcProof _0 -> true | uu____2266 -> false
  
let (__proj__CalcProof__item___0 :
  term' -> (term * term * calc_step Prims.list)) =
  fun projectee  -> match projectee with | CalcProof _0 -> _0 
let (__proj__Mkterm__item__tm : term -> term') =
  fun projectee  -> match projectee with | { tm; range; level;_} -> tm 
let (__proj__Mkterm__item__range : term -> FStar_Range.range) =
  fun projectee  -> match projectee with | { tm; range; level;_} -> range 
let (__proj__Mkterm__item__level : term -> level) =
  fun projectee  -> match projectee with | { tm; range; level;_} -> level 
let (uu___is_CalcStep : calc_step -> Prims.bool) = fun projectee  -> true 
let (__proj__CalcStep__item___0 : calc_step -> (term * term * term)) =
  fun projectee  -> match projectee with | CalcStep _0 -> _0 
let (uu___is_Variable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____2369 -> false
  
let (__proj__Variable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Variable _0 -> _0 
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____2388 -> false
  
let (__proj__TVariable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | TVariable _0 -> _0 
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____2411 -> false
  
let (__proj__Annotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Annotated _0 -> _0 
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____2446 -> false
  
let (__proj__TAnnotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0 
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____2477 -> false
  
let (__proj__NoName__item___0 : binder' -> term) =
  fun projectee  -> match projectee with | NoName _0 -> _0 
let (__proj__Mkbinder__item__b : binder -> binder') =
  fun projectee  -> match projectee with | { b; brange; blevel; aqual;_} -> b 
let (__proj__Mkbinder__item__brange : binder -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { b; brange; blevel; aqual;_} -> brange
  
let (__proj__Mkbinder__item__blevel : binder -> level) =
  fun projectee  ->
    match projectee with | { b; brange; blevel; aqual;_} -> blevel
  
let (__proj__Mkbinder__item__aqual :
  binder -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { b; brange; blevel; aqual;_} -> aqual
  
let (uu___is_PatWild : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatWild _0 -> true | uu____2550 -> false
  
let (__proj__PatWild__item___0 :
  pattern' -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PatWild _0 -> _0 
let (uu___is_PatConst : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____2575 -> false
  
let (__proj__PatConst__item___0 : pattern' -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | PatConst _0 -> _0 
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____2600 -> false
  
let (__proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list)) =
  fun projectee  -> match projectee with | PatApp _0 -> _0 
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____2643 -> false
  
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatVar _0 -> _0 
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____2680 -> false
  
let (__proj__PatName__item___0 : pattern' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | PatName _0 -> _0 
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____2705 -> false
  
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | PatTvar _0 -> _0 
let (uu___is_PatList : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____2744 -> false
  
let (__proj__PatList__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatList _0 -> _0 
let (uu___is_PatTuple : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____2776 -> false
  
let (__proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list * Prims.bool)) =
  fun projectee  -> match projectee with | PatTuple _0 -> _0 
let (uu___is_PatRecord : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____2822 -> false
  
let (__proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list) =
  fun projectee  -> match projectee with | PatRecord _0 -> _0 
let (uu___is_PatAscribed : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____2869 -> false
  
let (__proj__PatAscribed__item___0 :
  pattern' -> (pattern * (term * term FStar_Pervasives_Native.option))) =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0 
let (uu___is_PatOr : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____2920 -> false
  
let (__proj__PatOr__item___0 : pattern' -> pattern Prims.list) =
  fun projectee  -> match projectee with | PatOr _0 -> _0 
let (uu___is_PatOp : pattern' -> Prims.bool) =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____2945 -> false
  
let (__proj__PatOp__item___0 : pattern' -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | PatOp _0 -> _0 
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee  -> match projectee with | { pat; prange;_} -> pat 
let (__proj__Mkpattern__item__prange : pattern -> FStar_Range.range) =
  fun projectee  -> match projectee with | { pat; prange;_} -> prange 
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____2979 -> false
  
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____2990 -> false
  
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____3002 -> false
  
let (__proj__Meta__item___0 : arg_qualifier -> term) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_FsTypApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____3020 -> false
  
let (uu___is_Hash : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Hash  -> true | uu____3031 -> false
  
let (uu___is_UnivApp : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____3042 -> false
  
let (uu___is_HashBrace : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | HashBrace _0 -> true | uu____3054 -> false
  
let (__proj__HashBrace__item___0 : imp -> term) =
  fun projectee  -> match projectee with | HashBrace _0 -> _0 
let (uu___is_Infix : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Infix  -> true | uu____3072 -> false
  
let (uu___is_Nothing : imp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____3083 -> false
  
type patterns = (FStar_Ident.ident Prims.list * term Prims.list Prims.list)
type attributes_ = term Prims.list
type branch = (pattern * term FStar_Pervasives_Native.option * term)
type aqual = arg_qualifier FStar_Pervasives_Native.option
type knd = term
type typ = term
type expr = term
type fsdoc = (Prims.string * (Prims.string * Prims.string) Prims.list)
type tycon =
  | TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option) 
  | TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * term) 
  | TyconRecord of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term * fsdoc
  FStar_Pervasives_Native.option) Prims.list) 
  | TyconVariant of (FStar_Ident.ident * binder Prims.list * knd
  FStar_Pervasives_Native.option * (FStar_Ident.ident * term
  FStar_Pervasives_Native.option * fsdoc FStar_Pervasives_Native.option *
  Prims.bool) Prims.list) 
let (uu___is_TyconAbstract : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____3231 -> false
  
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | TyconAbstract _0 -> _0 
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____3292 -> false
  
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * term))
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0 
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____3369 -> false
  
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term * fsdoc
      FStar_Pervasives_Native.option) Prims.list))
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0 
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____3481 -> false
  
let (__proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term
      FStar_Pervasives_Native.option * fsdoc FStar_Pervasives_Native.option *
      Prims.bool) Prims.list))
  = fun projectee  -> match projectee with | TyconVariant _0 -> _0 
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
  fun projectee  ->
    match projectee with | Private  -> true | uu____3580 -> false
  
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____3591 -> false
  
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____3602 -> false
  
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____3613 -> false
  
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____3624 -> false
  
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____3635 -> false
  
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____3646 -> false
  
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____3657 -> false
  
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee  -> match projectee with | New  -> true | uu____3668 -> false 
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____3679 -> false
  
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____3690 -> false
  
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____3701 -> false
  
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____3712 -> false
  
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____3723 -> false
  
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____3734 -> false
  
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____3745 -> false
  
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____3756 -> false
  
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____3767 -> false
  
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____3778 -> false
  
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
  | Doc of fsdoc 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____3809 -> false
  
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee  -> match projectee with | Qualifier _0 -> _0 
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____3830 -> false
  
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0 
let (uu___is_Doc : decoration -> Prims.bool) =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____3855 -> false
  
let (__proj__Doc__item___0 : decoration -> fsdoc) =
  fun projectee  -> match projectee with | Doc _0 -> _0 
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____3893 -> false
  
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0 
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____3916 -> false
  
let (__proj__ReifiableLift__item___0 : lift_op -> (term * term)) =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0 
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____3947 -> false
  
let (__proj__LiftForFree__item___0 : lift_op -> term) =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0 
type lift =
  {
  msource: FStar_Ident.lid ;
  mdest: FStar_Ident.lid ;
  lift_op: lift_op }
let (__proj__Mklift__item__msource : lift -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op;_} -> msource
  
let (__proj__Mklift__item__mdest : lift -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op;_} -> mdest
  
let (__proj__Mklift__item__lift_op : lift -> lift_op) =
  fun projectee  ->
    match projectee with | { msource; mdest; lift_op;_} -> lift_op
  
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | PushOptions of Prims.string FStar_Pervasives_Native.option 
  | PopOptions 
  | RestartSolver 
  | LightOff 
let (uu___is_SetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____4031 -> false
  
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____4056 -> false
  
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushOptions _0 -> true | uu____4087 -> false
  
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | PushOptions _0 -> _0 
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | PopOptions  -> true | uu____4114 -> false
  
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | RestartSolver  -> true | uu____4125 -> false
  
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____4136 -> false
  
type decl' =
  | TopLevelModule of FStar_Ident.lid 
  | Open of FStar_Ident.lid 
  | Friend of FStar_Ident.lid 
  | Include of FStar_Ident.lid 
  | ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid) 
  | TopLevelLet of (let_qualifier * (pattern * term) Prims.list) 
  | Main of term 
  | Tycon of (Prims.bool * Prims.bool * (tycon * fsdoc
  FStar_Pervasives_Native.option) Prims.list) 
  | Val of (FStar_Ident.ident * term) 
  | Exception of (FStar_Ident.ident * term FStar_Pervasives_Native.option) 
  | NewEffect of effect_decl 
  | LayeredEffect of effect_decl 
  | SubEffect of lift 
  | Pragma of pragma 
  | Fsdoc of fsdoc 
  | Assume of (FStar_Ident.ident * term) 
  | Splice of (FStar_Ident.ident Prims.list * term) 
and decl =
  {
  d: decl' ;
  drange: FStar_Range.range ;
  doc: fsdoc FStar_Pervasives_Native.option ;
  quals: qualifiers ;
  attrs: attributes_ }
and effect_decl =
  | DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl
  Prims.list) 
  | RedefineEffect of (FStar_Ident.ident * binder Prims.list * term) 
let (uu___is_TopLevelModule : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____4340 -> false
  
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0 
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____4359 -> false
  
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Open _0 -> _0 
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Friend _0 -> true | uu____4378 -> false
  
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Friend _0 -> _0 
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____4397 -> false
  
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Include _0 -> _0 
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____4420 -> false
  
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0 
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____4461 -> false
  
let (__proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list)) =
  fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_Main : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____4510 -> false
  
let (__proj__Main__item___0 : decl' -> term) =
  fun projectee  -> match projectee with | Main _0 -> _0 
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____4545 -> false
  
let (__proj__Tycon__item___0 :
  decl' ->
    (Prims.bool * Prims.bool * (tycon * fsdoc FStar_Pervasives_Native.option)
      Prims.list))
  = fun projectee  -> match projectee with | Tycon _0 -> _0 
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____4616 -> false
  
let (__proj__Val__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Val _0 -> _0 
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____4653 -> false
  
let (__proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term FStar_Pervasives_Native.option)) =
  fun projectee  -> match projectee with | Exception _0 -> _0 
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____4690 -> false
  
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee  -> match projectee with | NewEffect _0 -> _0 
let (uu___is_LayeredEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LayeredEffect _0 -> true | uu____4709 -> false
  
let (__proj__LayeredEffect__item___0 : decl' -> effect_decl) =
  fun projectee  -> match projectee with | LayeredEffect _0 -> _0 
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____4728 -> false
  
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee  -> match projectee with | SubEffect _0 -> _0 
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____4747 -> false
  
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee  -> match projectee with | Pragma _0 -> _0 
let (uu___is_Fsdoc : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____4766 -> false
  
let (__proj__Fsdoc__item___0 : decl' -> fsdoc) =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0 
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____4789 -> false
  
let (__proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Splice _0 -> true | uu____4826 -> false
  
let (__proj__Splice__item___0 :
  decl' -> (FStar_Ident.ident Prims.list * term)) =
  fun projectee  -> match projectee with | Splice _0 -> _0 
let (__proj__Mkdecl__item__d : decl -> decl') =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> d
  
let (__proj__Mkdecl__item__drange : decl -> FStar_Range.range) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> drange
  
let (__proj__Mkdecl__item__doc :
  decl -> fsdoc FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> doc1
  
let (__proj__Mkdecl__item__quals : decl -> qualifiers) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> quals
  
let (__proj__Mkdecl__item__attrs : decl -> attributes_) =
  fun projectee  ->
    match projectee with | { d; drange; doc = doc1; quals; attrs;_} -> attrs
  
let (uu___is_DefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____4944 -> false
  
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0 
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____5007 -> false
  
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term)) =
  fun projectee  -> match projectee with | RedefineEffect _0 -> _0 
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____5081 -> false
  
let (__proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list))
  = fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____5127 -> false
  
let (__proj__Interface__item___0 :
  modul -> (FStar_Ident.lid * decl Prims.list * Prims.bool)) =
  fun projectee  -> match projectee with | Interface _0 -> _0 
type file = modul
type inputFragment = (file,decl Prims.list) FStar_Util.either
let (decl_drange : decl -> FStar_Range.range) = fun decl  -> decl.drange 
let (check_id : FStar_Ident.ident -> unit) =
  fun id1  ->
    let first_char =
      FStar_String.substring id1.FStar_Ident.idText Prims.int_zero
        Prims.int_one
       in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____5189 =
         let uu____5195 =
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             id1.FStar_Ident.idText
            in
         (FStar_Errors.Fatal_InvalidIdentifier, uu____5195)  in
       FStar_Errors.raise_error uu____5189 id1.FStar_Ident.idRange)
  
let at_most_one :
  'Auu____5208 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____5208 Prims.list ->
          'Auu____5208 FStar_Pervasives_Native.option
  =
  fun s  ->
    fun r  ->
      fun l  ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____5233 ->
            let uu____5236 =
              let uu____5242 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s
                 in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu____5242)  in
            FStar_Errors.raise_error uu____5236 r
  
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____5271 =
            FStar_List.choose
              (fun uu___0_5276  ->
                 match uu___0_5276 with
                 | Doc d1 -> FStar_Pervasives_Native.Some d1
                 | uu____5280 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "fsdoc" r uu____5271  in
        let attributes_ =
          let uu____5287 =
            FStar_List.choose
              (fun uu___1_5296  ->
                 match uu___1_5296 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____5306 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "attribute set" r uu____5287  in
        let attributes_1 = FStar_Util.dflt [] attributes_  in
        let qualifiers =
          FStar_List.choose
            (fun uu___2_5322  ->
               match uu___2_5322 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____5326 -> FStar_Pervasives_Native.None) decorations
           in
        { d; drange = r; doc = doc1; quals = qualifiers; attrs = attributes_1
        }
  
let (mk_binder :
  binder' ->
    FStar_Range.range ->
      level -> arg_qualifier FStar_Pervasives_Native.option -> binder)
  =
  fun b  ->
    fun r  -> fun l  -> fun i  -> { b; brange = r; blevel = l; aqual = i }
  
let (mk_term : term' -> FStar_Range.range -> level -> term) =
  fun t  -> fun r  -> fun l  -> { tm = t; range = r; level = l } 
let (mk_uminus :
  term -> FStar_Range.range -> FStar_Range.range -> level -> term) =
  fun t  ->
    fun rminus  ->
      fun r  ->
        fun l  ->
          let t1 =
            match t.tm with
            | Const (FStar_Const.Const_int
                (s,FStar_Pervasives_Native.Some (FStar_Const.Signed ,width)))
                ->
                Const
                  (FStar_Const.Const_int
                     ((Prims.op_Hat "-" s),
                       (FStar_Pervasives_Native.Some
                          (FStar_Const.Signed, width))))
            | uu____5416 ->
                let uu____5417 =
                  let uu____5424 = FStar_Ident.mk_ident ("-", rminus)  in
                  (uu____5424, [t])  in
                Op uu____5417
             in
          mk_term t1 r l
  
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p  -> fun r  -> { pat = p; prange = r } 
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____5463 -> Abs (ps, body)
  
let (mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = FStar_Ident.gen r1  in
        let uu____5503 =
          let uu____5504 =
            let uu____5511 =
              let uu____5512 =
                let uu____5513 =
                  let uu____5528 =
                    let uu____5529 =
                      let uu____5530 = FStar_Ident.lid_of_ids [x]  in
                      Var uu____5530  in
                    mk_term uu____5529 r1 Expr  in
                  (uu____5528, branches)  in
                Match uu____5513  in
              mk_term uu____5512 r2 Expr  in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____5511)
             in
          Abs uu____5504  in
        mk_term uu____5503 r2 Expr
  
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____5568,Abs (pats,body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____5587 -> FStar_Pervasives_Native.None
  
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid  ->
    fun r  ->
      let uu____5607 = FStar_Ident.path_of_lid lid  in
      FStar_Ident.lid_of_path uu____5607 r
  
let (consPat : FStar_Range.range -> pattern -> pattern -> pattern') =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        PatApp
          ((mk_pattern (PatName FStar_Parser_Const.cons_lid) r), [hd1; tl1])
  
let (consTerm : FStar_Range.range -> term -> term -> term) =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.cons_lid, [(hd1, Nothing); (tl1, Nothing)]))
          r Expr
  
let (lexConsTerm : FStar_Range.range -> term -> term -> term) =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.lexcons_lid,
               [(hd1, Nothing); (tl1, Nothing)])) r Expr
  
let (mkConsList : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let nil = mk_term (Construct (FStar_Parser_Const.nil_lid, [])) r Expr
         in
      FStar_List.fold_right (fun e  -> fun tl1  -> consTerm r e tl1) elts nil
  
let (mkLexList : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let nil =
        mk_term (Construct (FStar_Parser_Const.lextop_lid, [])) r Expr  in
      FStar_List.fold_right (fun e  -> fun tl1  -> lexConsTerm r e tl1) elts
        nil
  
let (ml_comp : term -> term) =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_ML_lid) t.range Expr  in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let (tot_comp : term -> term) =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_Tot_lid) t.range Expr
       in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let (mkApp : term -> (term * imp) Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____5802 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____5816 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____5826  ->
                        match uu____5826 with
                        | (a,imp) -> mk_term (App (t1, a, imp)) r Un) t args)
  
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r  ->
    fun elts  ->
      let uu____5848 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid)
         in
      match uu____5848 with
      | (empty_lid,singleton_lid,union_lid,addr_of_lid) ->
          let empty1 =
            let uu____5862 =
              let uu____5863 = FStar_Ident.set_lid_range empty_lid r  in
              Var uu____5863  in
            mk_term uu____5862 r Expr  in
          let addr_of =
            let uu____5865 =
              let uu____5866 = FStar_Ident.set_lid_range addr_of_lid r  in
              Var uu____5866  in
            mk_term uu____5865 r Expr  in
          let singleton1 =
            let uu____5868 =
              let uu____5869 = FStar_Ident.set_lid_range singleton_lid r  in
              Var uu____5869  in
            mk_term uu____5868 r Expr  in
          let union1 =
            let uu____5871 =
              let uu____5872 = FStar_Ident.set_lid_range union_lid r  in
              Var uu____5872  in
            mk_term uu____5871 r Expr  in
          FStar_List.fold_right
            (fun e  ->
               fun tl1  ->
                 let e1 = mkApp addr_of [(e, Nothing)] r  in
                 let single_e = mkApp singleton1 [(e1, Nothing)] r  in
                 mkApp union1 [(single_e, Nothing); (tl1, Nothing)] r) elts
            empty1
  
let (mkExplicitApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____5929 ->
            (match t.tm with
             | Name s ->
                 let uu____5933 =
                   let uu____5934 =
                     let uu____5945 =
                       FStar_List.map (fun a  -> (a, Nothing)) args  in
                     (s, uu____5945)  in
                   Construct uu____5934  in
                 mk_term uu____5933 r Un
             | uu____5964 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
  
let (unit_const : FStar_Range.range -> term) =
  fun r  -> mk_term (Const FStar_Const.Const_unit) r Expr 
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r  ->
    let admit1 =
      let admit_name =
        let uu____5983 =
          let uu____5984 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r  in
          Var uu____5984  in
        mk_term uu____5983 r Expr  in
      mkExplicitApp admit_name [unit_const r] r  in
    let magic1 =
      let magic_name =
        let uu____5987 =
          let uu____5988 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r  in
          Var uu____5988  in
        mk_term uu____5987 r Expr  in
      mkExplicitApp magic_name [unit_const r] r  in
    let admit_magic = mk_term (Seq (admit1, magic1)) r Expr  in admit_magic
  
let mkWildAdmitMagic :
  'Auu____5995 .
    FStar_Range.range ->
      (pattern * 'Auu____5995 FStar_Pervasives_Native.option * term)
  =
  fun r  ->
    let uu____6009 = mkAdmitMagic r  in
    ((mk_pattern (PatWild FStar_Pervasives_Native.None) r),
      FStar_Pervasives_Native.None, uu____6009)
  
let focusBranches :
  'Auu____6019 .
    (Prims.bool * (pattern * 'Auu____6019 FStar_Pervasives_Native.option *
      term)) Prims.list ->
      FStar_Range.range ->
        (pattern * 'Auu____6019 FStar_Pervasives_Native.option * term)
          Prims.list
  =
  fun branches  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some FStar_Pervasives_Native.fst branches  in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered, "Focusing on only some cases");
         (let focussed =
            let uu____6119 =
              FStar_List.filter FStar_Pervasives_Native.fst branches  in
            FStar_All.pipe_right uu____6119
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          let uu____6212 =
            let uu____6223 = mkWildAdmitMagic r  in [uu____6223]  in
          FStar_List.append focussed uu____6212))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusLetBindings :
  'Auu____6320 .
    (Prims.bool * ('Auu____6320 * term)) Prims.list ->
      FStar_Range.range -> ('Auu____6320 * term) Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter = FStar_Util.for_some FStar_Pervasives_Native.fst lbs
         in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____6401  ->
              match uu____6401 with
              | (f,lb) ->
                  if f
                  then lb
                  else
                    (let uu____6434 = mkAdmitMagic r  in
                     ((FStar_Pervasives_Native.fst lb), uu____6434))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusAttrLetBindings :
  'Auu____6481 'Auu____6482 .
    ('Auu____6481 * (Prims.bool * ('Auu____6482 * term))) Prims.list ->
      FStar_Range.range -> ('Auu____6481 * ('Auu____6482 * term)) Prims.list
  =
  fun lbs  ->
    fun r  ->
      let should_filter =
        FStar_Util.for_some
          (fun uu____6552  ->
             match uu____6552 with | (attr,(focus,uu____6569)) -> focus) lbs
         in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____6628  ->
              match uu____6628 with
              | (attr,(f,lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu____6687 =
                       let uu____6692 = mkAdmitMagic r  in
                       ((FStar_Pervasives_Native.fst lb), uu____6692)  in
                     (attr, uu____6687))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu____6749  ->
                match uu____6749 with | (attr,(uu____6772,lb)) -> (attr, lb)))
  
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____6817 = FStar_List.map (fun a  -> (a, FsTypApp)) args  in
        mkApp t uu____6817 r
  
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r  in
      let uu____6846 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____6846 r
  
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r  in
      let uu____6875 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____6875 r
  
let (mkRefinedBinder :
  FStar_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range ->
            arg_qualifier FStar_Pervasives_Native.option -> binder)
  =
  fun id1  ->
    fun t  ->
      fun should_bind_var  ->
        fun refopt  ->
          fun m  ->
            fun implicit  ->
              let b = mk_binder (Annotated (id1, t)) m Type_level implicit
                 in
              match refopt with
              | FStar_Pervasives_Native.None  -> b
              | FStar_Pervasives_Native.Some phi ->
                  if should_bind_var
                  then
                    mk_binder
                      (Annotated
                         (id1, (mk_term (Refine (b, phi)) m Type_level))) m
                      Type_level implicit
                  else
                    (let x = FStar_Ident.gen t.range  in
                     let b1 =
                       mk_binder (Annotated (x, t)) m Type_level implicit  in
                     mk_binder
                       (Annotated
                          (id1, (mk_term (Refine (b1, phi)) m Type_level))) m
                       Type_level implicit)
  
let (mkRefinedPattern :
  pattern ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> FStar_Range.range -> pattern)
  =
  fun pat  ->
    fun t  ->
      fun should_bind_pat  ->
        fun phi_opt  ->
          fun t_range  ->
            fun range  ->
              let t1 =
                match phi_opt with
                | FStar_Pervasives_Native.None  -> t
                | FStar_Pervasives_Native.Some phi ->
                    if should_bind_pat
                    then
                      (match pat.pat with
                       | PatVar (x,uu____6977) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____6982 ->
                           let x = FStar_Ident.gen t_range  in
                           let phi1 =
                             let x_var =
                               let uu____6986 =
                                 let uu____6987 = FStar_Ident.lid_of_ids [x]
                                    in
                                 Var uu____6987  in
                               mk_term uu____6986 phi.range Formula  in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi)  in
                             let otherwise_branch =
                               let uu____7008 =
                                 let uu____7009 =
                                   let uu____7010 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range
                                      in
                                   Name uu____7010  in
                                 mk_term uu____7009 phi.range Formula  in
                               ((mk_pattern
                                   (PatWild FStar_Pervasives_Native.None)
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu____7008)
                                in
                             mk_term
                               (Match (x_var, [pat_branch; otherwise_branch]))
                               phi.range Formula
                              in
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi1)) range Type_level)
                    else
                      (let x = FStar_Ident.gen t.range  in
                       mk_term
                         (Refine
                            ((mk_binder (Annotated (x, t)) t_range Type_level
                                FStar_Pervasives_Native.None), phi)) range
                         Type_level)
                 in
              mk_pattern
                (PatAscribed (pat, (t1, FStar_Pervasives_Native.None))) range
  
let rec (extract_named_refinement :
  term ->
    (FStar_Ident.ident * term * term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) ->
        FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____7101; blevel = uu____7102;
           aqual = uu____7103;_},t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____7118 -> FStar_Pervasives_Native.None
  
let rec (as_mlist :
  ((FStar_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul) =
  fun cur  ->
    fun ds  ->
      let uu____7162 = cur  in
      match uu____7162 with
      | ((m_name,m_decl),cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu____7193 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
  
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____7222 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag  in
        match uu____7222 with
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____7260 =
                       mk_decl (Pragma LightOff) light_range []  in
                     uu____7260 :: ds1
                   else ds1  in
                 let m1 = as_mlist ((m, d), []) ds2  in FStar_Util.Inl m1
             | uu____7272 ->
                 let ds2 = d :: ds1  in
                 (FStar_List.iter
                    (fun uu___3_7283  ->
                       match uu___3_7283 with
                       | { d = TopLevelModule uu____7284; drange = r;
                           doc = uu____7286; quals = uu____7287;
                           attrs = uu____7288;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu____7293 -> ()) ds2;
                  FStar_Util.Inr ds2))
  
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity  ->
    fun s  ->
      fun r  ->
        let name_of_char uu___4_7324 =
          match uu___4_7324 with
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
                     (Prims.op_Hat (FStar_Util.string_of_char c) "'"))) r
           in
        match s with
        | ".[]<-" -> "op_String_Assignment"
        | ".()<-" -> "op_Array_Assignment"
        | ".[||]<-" -> "op_Brack_Lens_Assignment"
        | ".(||)<-" -> "op_Lens_Assignment"
        | ".[]" -> "op_String_Access"
        | ".()" -> "op_Array_Access"
        | ".[||]" -> "op_Brack_Lens_Access"
        | ".(||)" -> "op_Lens_Access"
        | uu____7394 ->
            let uu____7396 =
              let uu____7398 =
                let uu____7402 = FStar_String.list_of_string s  in
                FStar_List.map name_of_char uu____7402  in
              FStar_String.concat "_" uu____7398  in
            Prims.op_Hat "op_" uu____7396
  
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s  -> fun r  -> compile_op (~- Prims.int_one) s r 
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu____7444  ->
    match uu____7444 with
    | (comment,keywords) ->
        let uu____7479 =
          let uu____7481 =
            FStar_List.map
              (fun uu____7495  ->
                 match uu____7495 with
                 | (k,v1) -> Prims.op_Hat k (Prims.op_Hat "->" v1)) keywords
             in
          FStar_String.concat "," uu____7481  in
        Prims.op_Hat comment uu____7479
  
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___5_7517  ->
    match uu___5_7517 with | NoLetQualifier  -> "" | Rec  -> "rec"
  
let to_string_l :
  'Auu____7530 .
    Prims.string ->
      ('Auu____7530 -> Prims.string) ->
        'Auu____7530 Prims.list -> Prims.string
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____7560 = FStar_List.map f l  in
        FStar_String.concat sep uu____7560
  
let (imp_to_string : imp -> Prims.string) =
  fun uu___6_7571  ->
    match uu___6_7571 with | Hash  -> "#" | uu____7574 -> ""
  
let rec (term_to_string : term -> Prims.string) =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____7617) ->
        let uu____7624 = term_to_string t  in
        FStar_Util.format1 "(requires %s)" uu____7624
    | Ensures (t,uu____7628) ->
        let uu____7635 = term_to_string t  in
        FStar_Util.format1 "(ensures %s)" uu____7635
    | Labeled (t,l,uu____7640) ->
        let uu____7645 = term_to_string t  in
        FStar_Util.format2 "(labeled %s %s)" l uu____7645
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____7655 = FStar_Ident.text_of_id s  in
        let uu____7657 =
          let uu____7659 =
            FStar_List.map
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs
             in
          FStar_String.concat ", " uu____7659  in
        FStar_Util.format2 "%s(%s)" uu____7655 uu____7657
    | Tvar id1 -> id1.FStar_Ident.idText
    | Uvar id1 -> id1.FStar_Ident.idText
    | Var l -> l.FStar_Ident.str
    | Name l -> l.FStar_Ident.str
    | Projector (rec_lid,field_id) ->
        let uu____7675 = FStar_Ident.string_of_lid rec_lid  in
        FStar_Util.format2 "%s?.%s" uu____7675 field_id.FStar_Ident.idText
    | Construct (l,args) ->
        let uu____7692 =
          to_string_l " "
            (fun uu____7703  ->
               match uu____7703 with
               | (a,imp) ->
                   let uu____7711 = term_to_string a  in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____7711)
            args
           in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____7692
    | Abs (pats,t) ->
        let uu____7721 = to_string_l " " pat_to_string pats  in
        let uu____7724 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(fun %s -> %s)" uu____7721 uu____7724
    | App (t1,t2,imp) ->
        let uu____7731 = FStar_All.pipe_right t1 term_to_string  in
        let uu____7734 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format3 "%s %s%s" uu____7731 (imp_to_string imp)
          uu____7734
    | Let (Rec ,(a,(p,b))::lbs,body) ->
        let uu____7795 = attrs_opt_to_string a  in
        let uu____7797 =
          let uu____7799 = FStar_All.pipe_right p pat_to_string  in
          let uu____7802 = FStar_All.pipe_right b term_to_string  in
          FStar_Util.format2 "%s=%s" uu____7799 uu____7802  in
        let uu____7806 =
          to_string_l " "
            (fun uu____7828  ->
               match uu____7828 with
               | (a1,(p1,b1)) ->
                   let uu____7857 = attrs_opt_to_string a1  in
                   let uu____7859 = FStar_All.pipe_right p1 pat_to_string  in
                   let uu____7862 = FStar_All.pipe_right b1 term_to_string
                      in
                   FStar_Util.format3 "%sand %s=%s" uu____7857 uu____7859
                     uu____7862) lbs
           in
        let uu____7866 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format4 "%slet rec %s%s in %s" uu____7795 uu____7797
          uu____7806 uu____7866
    | Let (q,(attrs,(pat,tm))::[],body) ->
        let uu____7925 = attrs_opt_to_string attrs  in
        let uu____7927 = FStar_All.pipe_right pat pat_to_string  in
        let uu____7930 = FStar_All.pipe_right tm term_to_string  in
        let uu____7933 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu____7925
          (string_of_let_qualifier q) uu____7927 uu____7930 uu____7933
    | Let (uu____7937,uu____7938,uu____7939) ->
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_EmptySurfaceLet,
            "Internal error: found an invalid surface Let") x.range
    | LetOpen (lid,t) ->
        let uu____7973 = FStar_Ident.string_of_lid lid  in
        let uu____7975 = term_to_string t  in
        FStar_Util.format2 "let open %s in %s" uu____7973 uu____7975
    | Seq (t1,t2) ->
        let uu____7980 = FStar_All.pipe_right t1 term_to_string  in
        let uu____7983 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "%s; %s" uu____7980 uu____7983
    | Bind (id1,t1,t2) ->
        let uu____7990 = term_to_string t1  in
        let uu____7992 = term_to_string t2  in
        FStar_Util.format3 "%s <- %s; %s" id1.FStar_Ident.idText uu____7990
          uu____7992
    | If (t1,t2,t3) ->
        let uu____7998 = FStar_All.pipe_right t1 term_to_string  in
        let uu____8001 = FStar_All.pipe_right t2 term_to_string  in
        let uu____8004 = FStar_All.pipe_right t3 term_to_string  in
        FStar_Util.format3 "if %s then %s else %s" uu____7998 uu____8001
          uu____8004
    | Match (t,branches) ->
        let s =
          match x.tm with
          | Match uu____8033 -> "match"
          | TryWith uu____8049 -> "try"
          | uu____8065 -> failwith "impossible"  in
        let uu____8068 = FStar_All.pipe_right t term_to_string  in
        let uu____8071 =
          to_string_l " | "
            (fun uu____8089  ->
               match uu____8089 with
               | (p,w,e) ->
                   let uu____8106 = FStar_All.pipe_right p pat_to_string  in
                   let uu____8109 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____8114 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____8114
                      in
                   let uu____8117 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" uu____8106 uu____8109
                     uu____8117) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____8068 uu____8071
    | TryWith (t,branches) ->
        let s =
          match x.tm with
          | Match uu____8147 -> "match"
          | TryWith uu____8163 -> "try"
          | uu____8179 -> failwith "impossible"  in
        let uu____8182 = FStar_All.pipe_right t term_to_string  in
        let uu____8185 =
          to_string_l " | "
            (fun uu____8203  ->
               match uu____8203 with
               | (p,w,e) ->
                   let uu____8220 = FStar_All.pipe_right p pat_to_string  in
                   let uu____8223 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____8228 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____8228
                      in
                   let uu____8231 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" uu____8220 uu____8223
                     uu____8231) branches
           in
        FStar_Util.format3 "%s %s with %s" s uu____8182 uu____8185
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____8240 = FStar_All.pipe_right t1 term_to_string  in
        let uu____8243 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "(%s : %s)" uu____8240 uu____8243
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____8252 = FStar_All.pipe_right t1 term_to_string  in
        let uu____8255 = FStar_All.pipe_right t2 term_to_string  in
        let uu____8258 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s : %s by %s)" uu____8252 uu____8255 uu____8258
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____8278 = FStar_All.pipe_right e term_to_string  in
        let uu____8281 =
          to_string_l " "
            (fun uu____8292  ->
               match uu____8292 with
               | (l,e1) ->
                   let uu____8300 = FStar_All.pipe_right e1 term_to_string
                      in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____8300)
            fields
           in
        FStar_Util.format2 "{%s with %s}" uu____8278 uu____8281
    | Record (FStar_Pervasives_Native.None ,fields) ->
        let uu____8320 =
          to_string_l " "
            (fun uu____8331  ->
               match uu____8331 with
               | (l,e) ->
                   let uu____8339 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____8339)
            fields
           in
        FStar_Util.format1 "{%s}" uu____8320
    | Project (e,l) ->
        let uu____8346 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format2 "%s.%s" uu____8346 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____8369 = FStar_All.pipe_right b binder_to_string  in
        let uu____8372 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s -> %s" uu____8369 uu____8372
    | Product (b::[],t) when x.level = Kind ->
        let uu____8380 = FStar_All.pipe_right b binder_to_string  in
        let uu____8383 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s => %s" uu____8380 uu____8383
    | Sum (binders,t) ->
        let uu____8401 =
          FStar_All.pipe_right (FStar_List.append binders [FStar_Util.Inr t])
            (FStar_List.map
               (fun uu___7_8433  ->
                  match uu___7_8433 with
                  | FStar_Util.Inl b -> binder_to_string b
                  | FStar_Util.Inr t1 -> term_to_string t1))
           in
        FStar_All.pipe_right uu____8401 (FStar_String.concat " & ")
    | QForall (bs,(uu____8447,pats),t) ->
        let uu____8476 = to_string_l " " binder_to_string bs  in
        let uu____8479 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____8485 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____8476 uu____8479
          uu____8485
    | QExists (bs,(uu____8490,pats),t) ->
        let uu____8519 = to_string_l " " binder_to_string bs  in
        let uu____8522 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____8528 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____8519 uu____8522
          uu____8528
    | Refine (b,t) ->
        let uu____8534 = FStar_All.pipe_right b binder_to_string  in
        let uu____8537 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:{%s}" uu____8534 uu____8537
    | NamedTyp (x1,t) ->
        let uu____8543 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____8543
    | Paren t ->
        let uu____8548 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format1 "(%s)" uu____8548
    | Product (bs,t) ->
        let uu____8558 =
          let uu____8560 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string)  in
          FStar_All.pipe_right uu____8560 (FStar_String.concat ",")  in
        let uu____8575 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____8558
          uu____8575
    | Discrim lid ->
        let uu____8580 = FStar_Ident.string_of_lid lid  in
        FStar_Util.format1 "%s?" uu____8580
    | Attributes ts ->
        let uu____8586 =
          let uu____8588 = FStar_List.map term_to_string ts  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____8588  in
        FStar_Util.format1 "(attributes %s)" uu____8586
    | Antiquote t ->
        let uu____8600 = term_to_string t  in
        FStar_Util.format1 "(`#%s)" uu____8600
    | Quote (t,Static ) ->
        let uu____8604 = term_to_string t  in
        FStar_Util.format1 "(`(%s))" uu____8604
    | Quote (t,Dynamic ) ->
        let uu____8608 = term_to_string t  in
        FStar_Util.format1 "quote (%s)" uu____8608
    | VQuote t ->
        let uu____8612 = term_to_string t  in
        FStar_Util.format1 "`%%%s" uu____8612
    | CalcProof (rel,init1,steps) ->
        let uu____8622 = term_to_string rel  in
        let uu____8624 = term_to_string init1  in
        let uu____8626 =
          let uu____8628 = FStar_List.map calc_step_to_string steps  in
          FStar_All.pipe_left (FStar_String.concat " ") uu____8628  in
        FStar_Util.format3 "calc (%s) { %s %s }" uu____8622 uu____8624
          uu____8626

and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu____8639  ->
    match uu____8639 with
    | CalcStep (rel,just,next) ->
        let uu____8644 = term_to_string rel  in
        let uu____8646 = term_to_string just  in
        let uu____8648 = term_to_string next  in
        FStar_Util.format3 "%s{ %s } %s" uu____8644 uu____8646 uu____8648

and (binder_to_string : binder -> Prims.string) =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t) ->
          let uu____8660 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____8660
      | Annotated (i,t) ->
          let uu____8666 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____8666
      | NoName t -> FStar_All.pipe_right t term_to_string  in
    let uu____8672 = aqual_to_string x.aqual  in
    FStar_Util.format2 "%s%s" uu____8672 s

and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___8_8675  ->
    match uu___8_8675 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____8681 -> ""

and (pat_to_string : pattern -> Prims.string) =
  fun x  ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None ) -> "_"
    | PatWild uu____8688 -> "#_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
        let uu____8699 = FStar_All.pipe_right p pat_to_string  in
        let uu____8702 = to_string_l " " pat_to_string ps  in
        FStar_Util.format2 "(%s %s)" uu____8699 uu____8702
    | PatTvar (i,aq) ->
        let uu____8712 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____8712 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____8721 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____8721 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____8728 = to_string_l "; " pat_to_string l  in
        FStar_Util.format1 "[%s]" uu____8728
    | PatTuple (l,false ) ->
        let uu____8739 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(%s)" uu____8739
    | PatTuple (l,true ) ->
        let uu____8750 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(|%s|)" uu____8750
    | PatRecord l ->
        let uu____8761 =
          to_string_l "; "
            (fun uu____8772  ->
               match uu____8772 with
               | (f,e) ->
                   let uu____8780 = FStar_All.pipe_right e pat_to_string  in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____8780) l
           in
        FStar_Util.format1 "{%s}" uu____8761
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu____8790 = FStar_Ident.text_of_id op  in
        FStar_Util.format1 "(%s)" uu____8790
    | PatAscribed (p,(t,FStar_Pervasives_Native.None )) ->
        let uu____8803 = FStar_All.pipe_right p pat_to_string  in
        let uu____8806 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(%s:%s)" uu____8803 uu____8806
    | PatAscribed (p,(t,FStar_Pervasives_Native.Some tac)) ->
        let uu____8821 = FStar_All.pipe_right p pat_to_string  in
        let uu____8824 = FStar_All.pipe_right t term_to_string  in
        let uu____8827 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s:%s by %s)" uu____8821 uu____8824 uu____8827

and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___9_8831  ->
    match uu___9_8831 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu____8845 =
          let uu____8847 = FStar_List.map term_to_string attrs  in
          FStar_All.pipe_right uu____8847 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____8845

let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____8870) ->
        let uu____8875 = FStar_Ident.lid_of_ids [i]  in [uu____8875]
    | PatApp (p1,uu____8877) -> head_id_of_pat p1
    | PatAscribed (p1,uu____8883) -> head_id_of_pat p1
    | uu____8896 -> []
  
let lids_of_let :
  'Auu____8902 .
    (pattern * 'Auu____8902) Prims.list -> FStar_Ident.lident Prims.list
  =
  fun defs  ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____8937  ->
            match uu____8937 with | (p,uu____8945) -> head_id_of_pat p))
  
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___10_8952  ->
    match uu___10_8952 with
    | TyconAbstract (i,uu____8955,uu____8956) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____8966,uu____8967,uu____8968) ->
        i.FStar_Ident.idText
    | TyconRecord (i,uu____8978,uu____8979,uu____8980) ->
        i.FStar_Ident.idText
    | TyconVariant (i,uu____9010,uu____9011,uu____9012) ->
        i.FStar_Ident.idText
  
let (decl_to_string : decl -> Prims.string) =
  fun d  ->
    match d.d with
    | TopLevelModule l -> Prims.op_Hat "module " l.FStar_Ident.str
    | Open l -> Prims.op_Hat "open " l.FStar_Ident.str
    | Friend l -> Prims.op_Hat "friend " l.FStar_Ident.str
    | Include l -> Prims.op_Hat "include " l.FStar_Ident.str
    | ModuleAbbrev (i,l) ->
        FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText
          l.FStar_Ident.str
    | TopLevelLet (uu____9070,pats) ->
        let uu____9084 =
          let uu____9086 =
            let uu____9090 = lids_of_let pats  in
            FStar_All.pipe_right uu____9090
              (FStar_List.map (fun l  -> l.FStar_Ident.str))
             in
          FStar_All.pipe_right uu____9086 (FStar_String.concat ", ")  in
        Prims.op_Hat "let " uu____9084
    | Main uu____9107 -> "main ..."
    | Assume (i,uu____9110) -> Prims.op_Hat "assume " i.FStar_Ident.idText
    | Tycon (uu____9112,uu____9113,tys) ->
        let uu____9135 =
          let uu____9137 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____9162  ->
                    match uu____9162 with | (x,uu____9171) -> id_of_tycon x))
             in
          FStar_All.pipe_right uu____9137 (FStar_String.concat ", ")  in
        Prims.op_Hat "type " uu____9135
    | Val (i,uu____9183) -> Prims.op_Hat "val " i.FStar_Ident.idText
    | Exception (i,uu____9186) ->
        Prims.op_Hat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,uu____9193,uu____9194,uu____9195)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | NewEffect (RedefineEffect (i,uu____9206,uu____9207)) ->
        Prims.op_Hat "new_effect " i.FStar_Ident.idText
    | Splice (ids,t) ->
        let uu____9219 =
          let uu____9221 =
            let uu____9223 =
              FStar_List.map (fun i  -> i.FStar_Ident.idText) ids  in
            FStar_All.pipe_left (FStar_String.concat ";") uu____9223  in
          let uu____9235 =
            let uu____9237 =
              let uu____9239 = term_to_string t  in
              Prims.op_Hat uu____9239 ")"  in
            Prims.op_Hat "] (" uu____9237  in
          Prims.op_Hat uu____9221 uu____9235  in
        Prims.op_Hat "splice[" uu____9219
    | SubEffect uu____9244 -> "sub_effect"
    | Pragma uu____9246 -> "pragma"
    | Fsdoc uu____9248 -> "fsdoc"
  
let (modul_to_string : modul -> Prims.string) =
  fun m  ->
    match m with
    | Module (uu____9258,decls) ->
        let uu____9264 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____9264 (FStar_String.concat "\n")
    | Interface (uu____9279,decls,uu____9281) ->
        let uu____9288 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____9288 (FStar_String.concat "\n")
  
let (decl_is_val : FStar_Ident.ident -> decl -> Prims.bool) =
  fun id1  ->
    fun decl  ->
      match decl.d with
      | Val (id',uu____9317) -> FStar_Ident.ident_equals id1 id'
      | uu____9318 -> false
  
let (thunk : term -> term) =
  fun ens  ->
    let wildpat = mk_pattern (PatWild FStar_Pervasives_Native.None) ens.range
       in
    mk_term (Abs ([wildpat], ens)) ens.range Expr
  
let (idents_of_binders :
  binder Prims.list -> FStar_Range.range -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    fun r  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun b  ->
              match b.b with
              | Variable i -> i
              | TVariable i -> i
              | Annotated (i,uu____9356) -> i
              | TAnnotated (i,uu____9358) -> i
              | NoName uu____9359 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_MissingQuantifierBinder,
                      "Wildcard binders in quantifiers are not allowed") r))
  