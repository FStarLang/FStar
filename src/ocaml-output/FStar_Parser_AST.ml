open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let (uu___is_Un : level -> Prims.bool) =
  fun projectee -> match projectee with | Un -> true | uu____25 -> false
let (uu___is_Expr : level -> Prims.bool) =
  fun projectee -> match projectee with | Expr -> true | uu____36 -> false
let (uu___is_Type_level : level -> Prims.bool) =
  fun projectee ->
    match projectee with | Type_level -> true | uu____47 -> false
let (uu___is_Kind : level -> Prims.bool) =
  fun projectee -> match projectee with | Kind -> true | uu____58 -> false
let (uu___is_Formula : level -> Prims.bool) =
  fun projectee -> match projectee with | Formula -> true | uu____69 -> false
type let_qualifier =
  | NoLetQualifier 
  | Rec 
let (uu___is_NoLetQualifier : let_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | NoLetQualifier -> true | uu____80 -> false
let (uu___is_Rec : let_qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Rec -> true | uu____91 -> false
type quote_kind =
  | Static 
  | Dynamic 
let (uu___is_Static : quote_kind -> Prims.bool) =
  fun projectee -> match projectee with | Static -> true | uu____102 -> false
let (uu___is_Dynamic : quote_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Dynamic -> true | uu____113 -> false
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
  fun projectee -> match projectee with | Wild -> true | uu____742 -> false
let (uu___is_Const : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____754 -> false
let (__proj__Const__item___0 : term' -> FStar_Const.sconst) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Op : term' -> Prims.bool) =
  fun projectee -> match projectee with | Op _0 -> true | uu____779 -> false
let (__proj__Op__item___0 : term' -> (FStar_Ident.ident * term Prims.list)) =
  fun projectee -> match projectee with | Op _0 -> _0
let (uu___is_Tvar : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tvar _0 -> true | uu____816 -> false
let (__proj__Tvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Tvar _0 -> _0
let (uu___is_Uvar : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Uvar _0 -> true | uu____835 -> false
let (__proj__Uvar__item___0 : term' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Uvar _0 -> _0
let (uu___is_Var : term' -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu____854 -> false
let (__proj__Var__item___0 : term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Name : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Name _0 -> true | uu____873 -> false
let (__proj__Name__item___0 : term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_Projector : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Projector _0 -> true | uu____896 -> false
let (__proj__Projector__item___0 :
  term' -> (FStar_Ident.lid * FStar_Ident.ident)) =
  fun projectee -> match projectee with | Projector _0 -> _0
let (uu___is_Construct : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Construct _0 -> true | uu____937 -> false
let (__proj__Construct__item___0 :
  term' -> (FStar_Ident.lid * (term * imp) Prims.list)) =
  fun projectee -> match projectee with | Construct _0 -> _0
let (uu___is_Abs : term' -> Prims.bool) =
  fun projectee -> match projectee with | Abs _0 -> true | uu____992 -> false
let (__proj__Abs__item___0 : term' -> (pattern Prims.list * term)) =
  fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | App _0 -> true | uu____1035 -> false
let (__proj__App__item___0 : term' -> (term * term * imp)) =
  fun projectee -> match projectee with | App _0 -> _0
let (uu___is_Let : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Let _0 -> true | uu____1092 -> false
let (__proj__Let__item___0 :
  term' ->
    (let_qualifier * (term Prims.list FStar_Pervasives_Native.option *
      (pattern * term)) Prims.list * term))
  = fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_LetOpen : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | LetOpen _0 -> true | uu____1175 -> false
let (__proj__LetOpen__item___0 : term' -> (FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | LetOpen _0 -> _0
let (uu___is_Seq : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Seq _0 -> true | uu____1210 -> false
let (__proj__Seq__item___0 : term' -> (term * term)) =
  fun projectee -> match projectee with | Seq _0 -> _0
let (uu___is_Bind : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Bind _0 -> true | uu____1247 -> false
let (__proj__Bind__item___0 : term' -> (FStar_Ident.ident * term * term)) =
  fun projectee -> match projectee with | Bind _0 -> _0
let (uu___is_If : term' -> Prims.bool) =
  fun projectee -> match projectee with | If _0 -> true | uu____1290 -> false
let (__proj__If__item___0 : term' -> (term * term * term)) =
  fun projectee -> match projectee with | If _0 -> _0
let (uu___is_Match : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Match _0 -> true | uu____1341 -> false
let (__proj__Match__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_TryWith : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | TryWith _0 -> true | uu____1416 -> false
let (__proj__TryWith__item___0 :
  term' ->
    (term * (pattern * term FStar_Pervasives_Native.option * term)
      Prims.list))
  = fun projectee -> match projectee with | TryWith _0 -> _0
let (uu___is_Ascribed : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Ascribed _0 -> true | uu____1485 -> false
let (__proj__Ascribed__item___0 :
  term' -> (term * term * term FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Ascribed _0 -> _0
let (uu___is_Record : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Record _0 -> true | uu____1540 -> false
let (__proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option * (FStar_Ident.lid * term)
      Prims.list))
  = fun projectee -> match projectee with | Record _0 -> _0
let (uu___is_Project : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Project _0 -> true | uu____1599 -> false
let (__proj__Project__item___0 : term' -> (term * FStar_Ident.lid)) =
  fun projectee -> match projectee with | Project _0 -> _0
let (uu___is_Product : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Product _0 -> true | uu____1636 -> false
let (__proj__Product__item___0 : term' -> (binder Prims.list * term)) =
  fun projectee -> match projectee with | Product _0 -> _0
let (uu___is_Sum : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Sum _0 -> true | uu____1683 -> false
let (__proj__Sum__item___0 :
  term' -> ((binder, term) FStar_Util.either Prims.list * term)) =
  fun projectee -> match projectee with | Sum _0 -> _0
let (uu___is_QForall : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | QForall _0 -> true | uu____1750 -> false
let (__proj__QForall__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee -> match projectee with | QForall _0 -> _0
let (uu___is_QExists : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | QExists _0 -> true | uu____1841 -> false
let (__proj__QExists__item___0 :
  term' ->
    (binder Prims.list * (FStar_Ident.ident Prims.list * term Prims.list
      Prims.list) * term))
  = fun projectee -> match projectee with | QExists _0 -> _0
let (uu___is_Refine : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Refine _0 -> true | uu____1918 -> false
let (__proj__Refine__item___0 : term' -> (binder * term)) =
  fun projectee -> match projectee with | Refine _0 -> _0
let (uu___is_NamedTyp : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NamedTyp _0 -> true | uu____1953 -> false
let (__proj__NamedTyp__item___0 : term' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | NamedTyp _0 -> _0
let (uu___is_Paren : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Paren _0 -> true | uu____1984 -> false
let (__proj__Paren__item___0 : term' -> term) =
  fun projectee -> match projectee with | Paren _0 -> _0
let (uu___is_Requires : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Requires _0 -> true | uu____2010 -> false
let (__proj__Requires__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Requires _0 -> _0
let (uu___is_Ensures : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Ensures _0 -> true | uu____2057 -> false
let (__proj__Ensures__item___0 :
  term' -> (term * Prims.string FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Ensures _0 -> _0
let (uu___is_Labeled : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Labeled _0 -> true | uu____2105 -> false
let (__proj__Labeled__item___0 : term' -> (term * Prims.string * Prims.bool))
  = fun projectee -> match projectee with | Labeled _0 -> _0
let (uu___is_Discrim : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Discrim _0 -> true | uu____2148 -> false
let (__proj__Discrim__item___0 : term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Discrim _0 -> _0
let (uu___is_Attributes : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Attributes _0 -> true | uu____2169 -> false
let (__proj__Attributes__item___0 : term' -> term Prims.list) =
  fun projectee -> match projectee with | Attributes _0 -> _0
let (uu___is_Antiquote : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Antiquote _0 -> true | uu____2194 -> false
let (__proj__Antiquote__item___0 : term' -> term) =
  fun projectee -> match projectee with | Antiquote _0 -> _0
let (uu___is_Quote : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | Quote _0 -> true | uu____2217 -> false
let (__proj__Quote__item___0 : term' -> (term * quote_kind)) =
  fun projectee -> match projectee with | Quote _0 -> _0
let (uu___is_VQuote : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | VQuote _0 -> true | uu____2248 -> false
let (__proj__VQuote__item___0 : term' -> term) =
  fun projectee -> match projectee with | VQuote _0 -> _0
let (uu___is_CalcProof : term' -> Prims.bool) =
  fun projectee ->
    match projectee with | CalcProof _0 -> true | uu____2275 -> false
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
    match projectee with | Variable _0 -> true | uu____2378 -> false
let (__proj__Variable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Variable _0 -> _0
let (uu___is_TVariable : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | TVariable _0 -> true | uu____2397 -> false
let (__proj__TVariable__item___0 : binder' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | TVariable _0 -> _0
let (uu___is_Annotated : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | Annotated _0 -> true | uu____2420 -> false
let (__proj__Annotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Annotated _0 -> _0
let (uu___is_TAnnotated : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | TAnnotated _0 -> true | uu____2455 -> false
let (__proj__TAnnotated__item___0 : binder' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | TAnnotated _0 -> _0
let (uu___is_NoName : binder' -> Prims.bool) =
  fun projectee ->
    match projectee with | NoName _0 -> true | uu____2486 -> false
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
    match projectee with | PatWild _0 -> true | uu____2559 -> false
let (__proj__PatWild__item___0 :
  pattern' -> arg_qualifier FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | PatWild _0 -> _0
let (uu___is_PatConst : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatConst _0 -> true | uu____2584 -> false
let (__proj__PatConst__item___0 : pattern' -> FStar_Const.sconst) =
  fun projectee -> match projectee with | PatConst _0 -> _0
let (uu___is_PatApp : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatApp _0 -> true | uu____2609 -> false
let (__proj__PatApp__item___0 : pattern' -> (pattern * pattern Prims.list)) =
  fun projectee -> match projectee with | PatApp _0 -> _0
let (uu___is_PatVar : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatVar _0 -> true | uu____2652 -> false
let (__proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | PatVar _0 -> _0
let (uu___is_PatName : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatName _0 -> true | uu____2689 -> false
let (__proj__PatName__item___0 : pattern' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | PatName _0 -> _0
let (uu___is_PatTvar : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatTvar _0 -> true | uu____2714 -> false
let (__proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident * arg_qualifier FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | PatTvar _0 -> _0
let (uu___is_PatList : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatList _0 -> true | uu____2753 -> false
let (__proj__PatList__item___0 : pattern' -> pattern Prims.list) =
  fun projectee -> match projectee with | PatList _0 -> _0
let (uu___is_PatTuple : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatTuple _0 -> true | uu____2785 -> false
let (__proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list * Prims.bool)) =
  fun projectee -> match projectee with | PatTuple _0 -> _0
let (uu___is_PatRecord : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatRecord _0 -> true | uu____2831 -> false
let (__proj__PatRecord__item___0 :
  pattern' -> (FStar_Ident.lid * pattern) Prims.list) =
  fun projectee -> match projectee with | PatRecord _0 -> _0
let (uu___is_PatAscribed : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatAscribed _0 -> true | uu____2878 -> false
let (__proj__PatAscribed__item___0 :
  pattern' -> (pattern * (term * term FStar_Pervasives_Native.option))) =
  fun projectee -> match projectee with | PatAscribed _0 -> _0
let (uu___is_PatOr : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatOr _0 -> true | uu____2929 -> false
let (__proj__PatOr__item___0 : pattern' -> pattern Prims.list) =
  fun projectee -> match projectee with | PatOr _0 -> _0
let (uu___is_PatOp : pattern' -> Prims.bool) =
  fun projectee ->
    match projectee with | PatOp _0 -> true | uu____2954 -> false
let (__proj__PatOp__item___0 : pattern' -> FStar_Ident.ident) =
  fun projectee -> match projectee with | PatOp _0 -> _0
let (__proj__Mkpattern__item__pat : pattern -> pattern') =
  fun projectee -> match projectee with | { pat; prange;_} -> pat
let (__proj__Mkpattern__item__prange : pattern -> FStar_Range.range) =
  fun projectee -> match projectee with | { pat; prange;_} -> prange
let (uu___is_Implicit : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Implicit -> true | uu____2988 -> false
let (uu___is_Equality : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Equality -> true | uu____2999 -> false
let (uu___is_Meta : arg_qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Meta _0 -> true | uu____3011 -> false
let (__proj__Meta__item___0 : arg_qualifier -> arg_qualifier_meta_t) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Arg_qualifier_meta_tac : arg_qualifier_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Arg_qualifier_meta_tac _0 -> true
    | uu____3030 -> false
let (__proj__Arg_qualifier_meta_tac__item___0 : arg_qualifier_meta_t -> term)
  = fun projectee -> match projectee with | Arg_qualifier_meta_tac _0 -> _0
let (uu___is_Arg_qualifier_meta_attr : arg_qualifier_meta_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Arg_qualifier_meta_attr _0 -> true
    | uu____3049 -> false
let (__proj__Arg_qualifier_meta_attr__item___0 :
  arg_qualifier_meta_t -> term) =
  fun projectee -> match projectee with | Arg_qualifier_meta_attr _0 -> _0
let (uu___is_FsTypApp : imp -> Prims.bool) =
  fun projectee ->
    match projectee with | FsTypApp -> true | uu____3067 -> false
let (uu___is_Hash : imp -> Prims.bool) =
  fun projectee -> match projectee with | Hash -> true | uu____3078 -> false
let (uu___is_UnivApp : imp -> Prims.bool) =
  fun projectee ->
    match projectee with | UnivApp -> true | uu____3089 -> false
let (uu___is_HashBrace : imp -> Prims.bool) =
  fun projectee ->
    match projectee with | HashBrace _0 -> true | uu____3101 -> false
let (__proj__HashBrace__item___0 : imp -> term) =
  fun projectee -> match projectee with | HashBrace _0 -> _0
let (uu___is_Infix : imp -> Prims.bool) =
  fun projectee -> match projectee with | Infix -> true | uu____3119 -> false
let (uu___is_Nothing : imp -> Prims.bool) =
  fun projectee ->
    match projectee with | Nothing -> true | uu____3130 -> false
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
    match projectee with | TyconAbstract _0 -> true | uu____3257 -> false
let (__proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | TyconAbstract _0 -> _0
let (uu___is_TyconAbbrev : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconAbbrev _0 -> true | uu____3318 -> false
let (__proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * term))
  = fun projectee -> match projectee with | TyconAbbrev _0 -> _0
let (uu___is_TyconRecord : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconRecord _0 -> true | uu____3391 -> false
let (__proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident * binder Prims.list * knd
      FStar_Pervasives_Native.option * (FStar_Ident.ident * term) Prims.list))
  = fun projectee -> match projectee with | TyconRecord _0 -> _0
let (uu___is_TyconVariant : tycon -> Prims.bool) =
  fun projectee ->
    match projectee with | TyconVariant _0 -> true | uu____3487 -> false
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
    match projectee with | Private -> true | uu____3574 -> false
let (uu___is_Abstract : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Abstract -> true | uu____3585 -> false
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Noeq -> true | uu____3596 -> false
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Unopteq -> true | uu____3607 -> false
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Assumption -> true | uu____3618 -> false
let (uu___is_DefaultEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | DefaultEffect -> true | uu____3629 -> false
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | TotalEffect -> true | uu____3640 -> false
let (uu___is_Effect_qual : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Effect_qual -> true | uu____3651 -> false
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | New -> true | uu____3662 -> false
let (uu___is_Inline : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Inline -> true | uu____3673 -> false
let (uu___is_Visible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Visible -> true | uu____3684 -> false
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Unfold_for_unification_and_vcgen -> true
    | uu____3695 -> false
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Inline_for_extraction -> true
    | uu____3706 -> false
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Irreducible -> true | uu____3717 -> false
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | NoExtract -> true | uu____3728 -> false
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reifiable -> true | uu____3739 -> false
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reflectable -> true | uu____3750 -> false
let (uu___is_Opaque : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Opaque -> true | uu____3761 -> false
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Logic -> true | uu____3772 -> false
type qualifiers = qualifier Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
let (uu___is_Qualifier : decoration -> Prims.bool) =
  fun projectee ->
    match projectee with | Qualifier _0 -> true | uu____3798 -> false
let (__proj__Qualifier__item___0 : decoration -> qualifier) =
  fun projectee -> match projectee with | Qualifier _0 -> _0
let (uu___is_DeclAttributes : decoration -> Prims.bool) =
  fun projectee ->
    match projectee with | DeclAttributes _0 -> true | uu____3819 -> false
let (__proj__DeclAttributes__item___0 : decoration -> term Prims.list) =
  fun projectee -> match projectee with | DeclAttributes _0 -> _0
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term * term) 
  | LiftForFree of term 
let (uu___is_NonReifiableLift : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | NonReifiableLift _0 -> true | uu____3863 -> false
let (__proj__NonReifiableLift__item___0 : lift_op -> term) =
  fun projectee -> match projectee with | NonReifiableLift _0 -> _0
let (uu___is_ReifiableLift : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | ReifiableLift _0 -> true | uu____3886 -> false
let (__proj__ReifiableLift__item___0 : lift_op -> (term * term)) =
  fun projectee -> match projectee with | ReifiableLift _0 -> _0
let (uu___is_LiftForFree : lift_op -> Prims.bool) =
  fun projectee ->
    match projectee with | LiftForFree _0 -> true | uu____3917 -> false
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
    match projectee with | SetOptions _0 -> true | uu____4001 -> false
let (__proj__SetOptions__item___0 : pragma -> Prims.string) =
  fun projectee -> match projectee with | SetOptions _0 -> _0
let (uu___is_ResetOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | ResetOptions _0 -> true | uu____4026 -> false
let (__proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | ResetOptions _0 -> _0
let (uu___is_PushOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PushOptions _0 -> true | uu____4057 -> false
let (__proj__PushOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | PushOptions _0 -> _0
let (uu___is_PopOptions : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | PopOptions -> true | uu____4084 -> false
let (uu___is_RestartSolver : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | RestartSolver -> true | uu____4095 -> false
let (uu___is_LightOff : pragma -> Prims.bool) =
  fun projectee ->
    match projectee with | LightOff -> true | uu____4106 -> false
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
    match projectee with | TopLevelModule _0 -> true | uu____4300 -> false
let (__proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TopLevelModule _0 -> _0
let (uu___is_Open : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Open _0 -> true | uu____4319 -> false
let (__proj__Open__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Open _0 -> _0
let (uu___is_Friend : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Friend _0 -> true | uu____4338 -> false
let (__proj__Friend__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Friend _0 -> _0
let (uu___is_Include : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Include _0 -> true | uu____4357 -> false
let (__proj__Include__item___0 : decl' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Include _0 -> _0
let (uu___is_ModuleAbbrev : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | ModuleAbbrev _0 -> true | uu____4380 -> false
let (__proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident * FStar_Ident.lid)) =
  fun projectee -> match projectee with | ModuleAbbrev _0 -> _0
let (uu___is_TopLevelLet : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelLet _0 -> true | uu____4421 -> false
let (__proj__TopLevelLet__item___0 :
  decl' -> (let_qualifier * (pattern * term) Prims.list)) =
  fun projectee -> match projectee with | TopLevelLet _0 -> _0
let (uu___is_Tycon : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Tycon _0 -> true | uu____4480 -> false
let (__proj__Tycon__item___0 :
  decl' -> (Prims.bool * Prims.bool * tycon Prims.list)) =
  fun projectee -> match projectee with | Tycon _0 -> _0
let (uu___is_Val : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Val _0 -> true | uu____4533 -> false
let (__proj__Val__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Val _0 -> _0
let (uu___is_Exception : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Exception _0 -> true | uu____4570 -> false
let (__proj__Exception__item___0 :
  decl' -> (FStar_Ident.ident * term FStar_Pervasives_Native.option)) =
  fun projectee -> match projectee with | Exception _0 -> _0
let (uu___is_NewEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | NewEffect _0 -> true | uu____4607 -> false
let (__proj__NewEffect__item___0 : decl' -> effect_decl) =
  fun projectee -> match projectee with | NewEffect _0 -> _0
let (uu___is_LayeredEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | LayeredEffect _0 -> true | uu____4626 -> false
let (__proj__LayeredEffect__item___0 : decl' -> effect_decl) =
  fun projectee -> match projectee with | LayeredEffect _0 -> _0
let (uu___is_SubEffect : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | SubEffect _0 -> true | uu____4645 -> false
let (__proj__SubEffect__item___0 : decl' -> lift) =
  fun projectee -> match projectee with | SubEffect _0 -> _0
let (uu___is_Polymonadic_bind : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Polymonadic_bind _0 -> true | uu____4672 -> false
let (__proj__Polymonadic_bind__item___0 :
  decl' -> (FStar_Ident.lid * FStar_Ident.lid * FStar_Ident.lid * term)) =
  fun projectee -> match projectee with | Polymonadic_bind _0 -> _0
let (uu___is_Pragma : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Pragma _0 -> true | uu____4715 -> false
let (__proj__Pragma__item___0 : decl' -> pragma) =
  fun projectee -> match projectee with | Pragma _0 -> _0
let (uu___is_Assume : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Assume _0 -> true | uu____4738 -> false
let (__proj__Assume__item___0 : decl' -> (FStar_Ident.ident * term)) =
  fun projectee -> match projectee with | Assume _0 -> _0
let (uu___is_Splice : decl' -> Prims.bool) =
  fun projectee ->
    match projectee with | Splice _0 -> true | uu____4775 -> false
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
    match projectee with | DefineEffect _0 -> true | uu____4864 -> false
let (__proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident * binder Prims.list * term * decl Prims.list))
  = fun projectee -> match projectee with | DefineEffect _0 -> _0
let (uu___is_RedefineEffect : effect_decl -> Prims.bool) =
  fun projectee ->
    match projectee with | RedefineEffect _0 -> true | uu____4927 -> false
let (__proj__RedefineEffect__item___0 :
  effect_decl -> (FStar_Ident.ident * binder Prims.list * term)) =
  fun projectee -> match projectee with | RedefineEffect _0 -> _0
type modul =
  | Module of (FStar_Ident.lid * decl Prims.list) 
  | Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool) 
let (uu___is_Module : modul -> Prims.bool) =
  fun projectee ->
    match projectee with | Module _0 -> true | uu____5001 -> false
let (__proj__Module__item___0 : modul -> (FStar_Ident.lid * decl Prims.list))
  = fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Interface : modul -> Prims.bool) =
  fun projectee ->
    match projectee with | Interface _0 -> true | uu____5047 -> false
let (__proj__Interface__item___0 :
  modul -> (FStar_Ident.lid * decl Prims.list * Prims.bool)) =
  fun projectee -> match projectee with | Interface _0 -> _0
type file = modul
type inputFragment = (file, decl Prims.list) FStar_Util.either
let (decl_drange : decl -> FStar_Range.range) = fun decl1 -> decl1.drange
let (check_id : FStar_Ident.ident -> unit) =
  fun id ->
    let first_char =
      let uu____5103 = FStar_Ident.string_of_id id in
      FStar_String.substring uu____5103 Prims.int_zero Prims.int_one in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____5111 =
         let uu____5117 =
           let uu____5119 = FStar_Ident.string_of_id id in
           FStar_Util.format1
             "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
             uu____5119 in
         (FStar_Errors.Fatal_InvalidIdentifier, uu____5117) in
       let uu____5123 = FStar_Ident.range_of_id id in
       FStar_Errors.raise_error uu____5111 uu____5123)
let at_most_one :
  'uuuuuu5133 .
    Prims.string ->
      FStar_Range.range ->
        'uuuuuu5133 Prims.list -> 'uuuuuu5133 FStar_Pervasives_Native.option
  =
  fun s ->
    fun r ->
      fun l ->
        match l with
        | x::[] -> FStar_Pervasives_Native.Some x
        | [] -> FStar_Pervasives_Native.None
        | uu____5158 ->
            let uu____5161 =
              let uu____5167 =
                FStar_Util.format1
                  "At most one %s is allowed on declarations" s in
              (FStar_Errors.Fatal_MoreThanOneDeclaration, uu____5167) in
            FStar_Errors.raise_error uu____5161 r
let (mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl) =
  fun d ->
    fun r ->
      fun decorations ->
        let attributes_1 =
          let uu____5198 =
            FStar_List.choose
              (fun uu___0_5207 ->
                 match uu___0_5207 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____5217 -> FStar_Pervasives_Native.None) decorations in
          at_most_one "attribute set" r uu____5198 in
        let attributes_2 = FStar_Util.dflt [] attributes_1 in
        let qualifiers1 =
          FStar_List.choose
            (fun uu___1_5233 ->
               match uu___1_5233 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____5237 -> FStar_Pervasives_Native.None) decorations in
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
            | uu____5327 ->
                let uu____5328 =
                  let uu____5335 = FStar_Ident.mk_ident ("-", rminus) in
                  (uu____5335, [t]) in
                Op uu____5328 in
          mk_term t1 r l
let (mk_pattern : pattern' -> FStar_Range.range -> pattern) =
  fun p -> fun r -> { pat = p; prange = r }
let (un_curry_abs : pattern Prims.list -> term -> term') =
  fun ps ->
    fun body ->
      match body.tm with
      | Abs (p', body') -> Abs ((FStar_List.append ps p'), body')
      | uu____5374 -> Abs (ps, body)
let (mk_function :
  (pattern * term FStar_Pervasives_Native.option * term) Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term)
  =
  fun branches ->
    fun r1 ->
      fun r2 ->
        let x = FStar_Ident.gen r1 in
        let uu____5414 =
          let uu____5415 =
            let uu____5422 =
              let uu____5423 =
                let uu____5424 =
                  let uu____5439 =
                    let uu____5440 =
                      let uu____5441 = FStar_Ident.lid_of_ids [x] in
                      Var uu____5441 in
                    mk_term uu____5440 r1 Expr in
                  (uu____5439, branches) in
                Match uu____5424 in
              mk_term uu____5423 r2 Expr in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____5422) in
          Abs uu____5415 in
        mk_term uu____5414 r2 Expr
let (un_function :
  pattern -> term -> (pattern * term) FStar_Pervasives_Native.option) =
  fun p ->
    fun tm ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____5479, Abs (pats, body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____5498 -> FStar_Pervasives_Native.None
let (lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident) =
  fun lid ->
    fun r ->
      let uu____5518 = FStar_Ident.path_of_lid lid in
      FStar_Ident.lid_of_path uu____5518 r
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
        | uu____5713 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____5727 ->
                 FStar_List.fold_left
                   (fun t1 ->
                      fun uu____5737 ->
                        match uu____5737 with
                        | (a, imp1) -> mk_term (App (t1, a, imp1)) r Un) t
                   args)
let (mkRefSet : FStar_Range.range -> term Prims.list -> term) =
  fun r ->
    fun elts ->
      let uu____5759 =
        (FStar_Parser_Const.set_empty, FStar_Parser_Const.set_singleton,
          FStar_Parser_Const.set_union, FStar_Parser_Const.heap_addr_of_lid) in
      match uu____5759 with
      | (empty_lid, singleton_lid, union_lid, addr_of_lid) ->
          let empty =
            let uu____5773 =
              let uu____5774 = FStar_Ident.set_lid_range empty_lid r in
              Var uu____5774 in
            mk_term uu____5773 r Expr in
          let addr_of =
            let uu____5776 =
              let uu____5777 = FStar_Ident.set_lid_range addr_of_lid r in
              Var uu____5777 in
            mk_term uu____5776 r Expr in
          let singleton =
            let uu____5779 =
              let uu____5780 = FStar_Ident.set_lid_range singleton_lid r in
              Var uu____5780 in
            mk_term uu____5779 r Expr in
          let union =
            let uu____5782 =
              let uu____5783 = FStar_Ident.set_lid_range union_lid r in
              Var uu____5783 in
            mk_term uu____5782 r Expr in
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
        | uu____5840 ->
            (match t.tm with
             | Name s ->
                 let uu____5844 =
                   let uu____5845 =
                     let uu____5856 =
                       FStar_List.map (fun a -> (a, Nothing)) args in
                     (s, uu____5856) in
                   Construct uu____5845 in
                 mk_term uu____5844 r Un
             | uu____5875 ->
                 FStar_List.fold_left
                   (fun t1 -> fun a -> mk_term (App (t1, a, Nothing)) r Un) t
                   args)
let (unit_const : FStar_Range.range -> term) =
  fun r -> mk_term (Const FStar_Const.Const_unit) r Expr
let (mkAdmitMagic : FStar_Range.range -> term) =
  fun r ->
    let admit =
      let admit_name =
        let uu____5894 =
          let uu____5895 =
            FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r in
          Var uu____5895 in
        mk_term uu____5894 r Expr in
      mkExplicitApp admit_name [unit_const r] r in
    let magic =
      let magic_name =
        let uu____5898 =
          let uu____5899 =
            FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r in
          Var uu____5899 in
        mk_term uu____5898 r Expr in
      mkExplicitApp magic_name [unit_const r] r in
    let admit_magic = mk_term (Seq (admit, magic)) r Expr in admit_magic
let mkWildAdmitMagic :
  'uuuuuu5906 .
    FStar_Range.range ->
      (pattern * 'uuuuuu5906 FStar_Pervasives_Native.option * term)
  =
  fun r ->
    let uu____5920 = mkAdmitMagic r in
    ((mk_pattern (PatWild FStar_Pervasives_Native.None) r),
      FStar_Pervasives_Native.None, uu____5920)
let focusBranches :
  'uuuuuu5930 .
    (Prims.bool * (pattern * 'uuuuuu5930 FStar_Pervasives_Native.option *
      term)) Prims.list ->
      FStar_Range.range ->
        (pattern * 'uuuuuu5930 FStar_Pervasives_Native.option * term)
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
            let uu____6030 =
              FStar_List.filter FStar_Pervasives_Native.fst branches in
            FStar_All.pipe_right uu____6030
              (FStar_List.map FStar_Pervasives_Native.snd) in
          let uu____6123 =
            let uu____6134 = mkWildAdmitMagic r in [uu____6134] in
          FStar_List.append focussed uu____6123))
      else
        FStar_All.pipe_right branches
          (FStar_List.map FStar_Pervasives_Native.snd)
let focusLetBindings :
  'uuuuuu6231 .
    (Prims.bool * ('uuuuuu6231 * term)) Prims.list ->
      FStar_Range.range -> ('uuuuuu6231 * term) Prims.list
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
           (fun uu____6312 ->
              match uu____6312 with
              | (f, lb) ->
                  if f
                  then lb
                  else
                    (let uu____6345 = mkAdmitMagic r in
                     ((FStar_Pervasives_Native.fst lb), uu____6345))) lbs)
      else
        FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd)
let focusAttrLetBindings :
  'uuuuuu6392 'uuuuuu6393 .
    ('uuuuuu6392 * (Prims.bool * ('uuuuuu6393 * term))) Prims.list ->
      FStar_Range.range -> ('uuuuuu6392 * ('uuuuuu6393 * term)) Prims.list
  =
  fun lbs ->
    fun r ->
      let should_filter =
        FStar_Util.for_some
          (fun uu____6463 ->
             match uu____6463 with | (attr, (focus, uu____6480)) -> focus)
          lbs in
      if should_filter
      then
        (FStar_Errors.log_issue r
           (FStar_Errors.Warning_Filtered,
             "Focusing on only some cases in this (mutually) recursive definition");
         FStar_List.map
           (fun uu____6539 ->
              match uu____6539 with
              | (attr, (f, lb)) ->
                  if f
                  then (attr, lb)
                  else
                    (let uu____6598 =
                       let uu____6603 = mkAdmitMagic r in
                       ((FStar_Pervasives_Native.fst lb), uu____6603) in
                     (attr, uu____6598))) lbs)
      else
        FStar_All.pipe_right lbs
          (FStar_List.map
             (fun uu____6660 ->
                match uu____6660 with
                | (attr, (uu____6683, lb)) -> (attr, lb)))
let (mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term) =
  fun t ->
    fun args ->
      fun r ->
        let uu____6728 = FStar_List.map (fun a -> (a, FsTypApp)) args in
        mkApp t uu____6728 r
let (mkTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args ->
    fun r ->
      let cons =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r in
      let uu____6757 = FStar_List.map (fun x -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu____6757 r
let (mkDTuple : term Prims.list -> FStar_Range.range -> term) =
  fun args ->
    fun r ->
      let cons =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r in
      let uu____6786 = FStar_List.map (fun x -> (x, Nothing)) args in
      mkApp (mk_term (Name cons) r Expr) uu____6786 r
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
                       | PatVar (x, uu____6888) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____6893 ->
                           let x = FStar_Ident.gen t_range in
                           let phi1 =
                             let x_var =
                               let uu____6897 =
                                 let uu____6898 = FStar_Ident.lid_of_ids [x] in
                                 Var uu____6898 in
                               mk_term uu____6897 phi.range Formula in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi) in
                             let otherwise_branch =
                               let uu____6919 =
                                 let uu____6920 =
                                   let uu____6921 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range in
                                   Name uu____6921 in
                                 mk_term uu____6920 phi.range Formula in
                               ((mk_pattern
                                   (PatWild FStar_Pervasives_Native.None)
                                   phi.range), FStar_Pervasives_Native.None,
                                 uu____6919) in
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
        ({ b = Annotated (x, t); brange = uu____7012; blevel = uu____7013;
           aqual = uu____7014;_},
         t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____7029 -> FStar_Pervasives_Native.None
let rec (as_mlist :
  ((FStar_Ident.lid * decl) * decl Prims.list) -> decl Prims.list -> modul) =
  fun cur ->
    fun ds ->
      let uu____7073 = cur in
      match uu____7073 with
      | ((m_name, m_decl), cur1) ->
          (match ds with
           | [] -> Module (m_name, (m_decl :: (FStar_List.rev cur1)))
           | d::ds1 ->
               (match d.d with
                | TopLevelModule m' ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                        "Unexpected module declaration") d.drange
                | uu____7104 -> as_mlist ((m_name, m_decl), (d :: cur1)) ds1))
let (as_frag :
  Prims.bool -> FStar_Range.range -> decl Prims.list -> inputFragment) =
  fun is_light ->
    fun light_range ->
      fun ds ->
        let uu____7133 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> FStar_Exn.raise FStar_Errors.Empty_frag in
        match uu____7133 with
        | (d, ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____7171 =
                       mk_decl (Pragma LightOff) light_range [] in
                     uu____7171 :: ds1
                   else ds1 in
                 let m1 = as_mlist ((m, d), []) ds2 in FStar_Util.Inl m1
             | uu____7183 ->
                 let ds2 = d :: ds1 in
                 (FStar_List.iter
                    (fun uu___2_7193 ->
                       match uu___2_7193 with
                       | { d = TopLevelModule uu____7194; drange = r;
                           quals = uu____7196; attrs = uu____7197;_} ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_UnexpectedModuleDeclaration,
                               "Unexpected module declaration") r
                       | uu____7200 -> ()) ds2;
                  FStar_Util.Inr ds2))
let (compile_op :
  Prims.int -> Prims.string -> FStar_Range.range -> Prims.string) =
  fun arity ->
    fun s ->
      fun r ->
        let name_of_char uu___3_7231 =
          match uu___3_7231 with
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
        | uu____7301 ->
            let uu____7303 =
              let uu____7305 =
                let uu____7309 = FStar_String.list_of_string s in
                FStar_List.map name_of_char uu____7309 in
              FStar_String.concat "_" uu____7305 in
            Prims.op_Hat "op_" uu____7303
let (compile_op' : Prims.string -> FStar_Range.range -> Prims.string) =
  fun s -> fun r -> compile_op (~- Prims.int_one) s r
let (string_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) -> Prims.string)
  =
  fun uu____7351 ->
    match uu____7351 with
    | (comment, keywords) ->
        let uu____7386 =
          let uu____7388 =
            FStar_List.map
              (fun uu____7402 ->
                 match uu____7402 with
                 | (k, v) -> Prims.op_Hat k (Prims.op_Hat "->" v)) keywords in
          FStar_String.concat "," uu____7388 in
        Prims.op_Hat comment uu____7386
let (string_of_let_qualifier : let_qualifier -> Prims.string) =
  fun uu___4_7424 ->
    match uu___4_7424 with | NoLetQualifier -> "" | Rec -> "rec"
let to_string_l :
  'uuuuuu7437 .
    Prims.string ->
      ('uuuuuu7437 -> Prims.string) -> 'uuuuuu7437 Prims.list -> Prims.string
  =
  fun sep ->
    fun f ->
      fun l ->
        let uu____7467 = FStar_List.map f l in
        FStar_String.concat sep uu____7467
let (imp_to_string : imp -> Prims.string) =
  fun uu___5_7478 -> match uu___5_7478 with | Hash -> "#" | uu____7481 -> ""
let rec (term_to_string : term -> Prims.string) =
  fun x ->
    match x.tm with
    | Wild -> "_"
    | Requires (t, uu____7524) ->
        let uu____7531 = term_to_string t in
        FStar_Util.format1 "(requires %s)" uu____7531
    | Ensures (t, uu____7535) ->
        let uu____7542 = term_to_string t in
        FStar_Util.format1 "(ensures %s)" uu____7542
    | Labeled (t, l, uu____7547) ->
        let uu____7552 = term_to_string t in
        FStar_Util.format2 "(labeled %s %s)" l uu____7552
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s, xs) ->
        let uu____7562 = FStar_Ident.string_of_id s in
        let uu____7564 =
          let uu____7566 =
            FStar_List.map (fun x1 -> FStar_All.pipe_right x1 term_to_string)
              xs in
          FStar_String.concat ", " uu____7566 in
        FStar_Util.format2 "%s(%s)" uu____7562 uu____7564
    | Tvar id -> FStar_Ident.string_of_id id
    | Uvar id -> FStar_Ident.string_of_id id
    | Var l -> FStar_Ident.string_of_lid l
    | Name l -> FStar_Ident.string_of_lid l
    | Projector (rec_lid, field_id) ->
        let uu____7582 = FStar_Ident.string_of_lid rec_lid in
        let uu____7584 = FStar_Ident.string_of_id field_id in
        FStar_Util.format2 "%s?.%s" uu____7582 uu____7584
    | Construct (l, args) ->
        let uu____7601 = FStar_Ident.string_of_lid l in
        let uu____7603 =
          to_string_l " "
            (fun uu____7614 ->
               match uu____7614 with
               | (a, imp1) ->
                   let uu____7622 = term_to_string a in
                   FStar_Util.format2 "%s%s" (imp_to_string imp1) uu____7622)
            args in
        FStar_Util.format2 "(%s %s)" uu____7601 uu____7603
    | Abs (pats, t) ->
        let uu____7632 = to_string_l " " pat_to_string pats in
        let uu____7635 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(fun %s -> %s)" uu____7632 uu____7635
    | App (t1, t2, imp1) ->
        let uu____7642 = FStar_All.pipe_right t1 term_to_string in
        let uu____7645 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format3 "%s %s%s" uu____7642 (imp_to_string imp1)
          uu____7645
    | Let (Rec, (a, (p, b))::lbs, body) ->
        let uu____7706 = attrs_opt_to_string a in
        let uu____7708 =
          let uu____7710 = FStar_All.pipe_right p pat_to_string in
          let uu____7713 = FStar_All.pipe_right b term_to_string in
          FStar_Util.format2 "%s=%s" uu____7710 uu____7713 in
        let uu____7717 =
          to_string_l " "
            (fun uu____7739 ->
               match uu____7739 with
               | (a1, (p1, b1)) ->
                   let uu____7768 = attrs_opt_to_string a1 in
                   let uu____7770 = FStar_All.pipe_right p1 pat_to_string in
                   let uu____7773 = FStar_All.pipe_right b1 term_to_string in
                   FStar_Util.format3 "%sand %s=%s" uu____7768 uu____7770
                     uu____7773) lbs in
        let uu____7777 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format4 "%slet rec %s%s in %s" uu____7706 uu____7708
          uu____7717 uu____7777
    | Let (q, (attrs, (pat, tm))::[], body) ->
        let uu____7836 = attrs_opt_to_string attrs in
        let uu____7838 = FStar_All.pipe_right pat pat_to_string in
        let uu____7841 = FStar_All.pipe_right tm term_to_string in
        let uu____7844 = FStar_All.pipe_right body term_to_string in
        FStar_Util.format5 "%slet %s %s = %s in %s" uu____7836
          (string_of_let_qualifier q) uu____7838 uu____7841 uu____7844
    | Let (uu____7848, uu____7849, uu____7850) ->
        FStar_Errors.raise_error
          (FStar_Errors.Fatal_EmptySurfaceLet,
            "Internal error: found an invalid surface Let") x.range
    | LetOpen (lid, t) ->
        let uu____7884 = FStar_Ident.string_of_lid lid in
        let uu____7886 = term_to_string t in
        FStar_Util.format2 "let open %s in %s" uu____7884 uu____7886
    | Seq (t1, t2) ->
        let uu____7891 = FStar_All.pipe_right t1 term_to_string in
        let uu____7894 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "%s; %s" uu____7891 uu____7894
    | Bind (id, t1, t2) ->
        let uu____7901 = FStar_Ident.string_of_id id in
        let uu____7903 = term_to_string t1 in
        let uu____7905 = term_to_string t2 in
        FStar_Util.format3 "%s <- %s; %s" uu____7901 uu____7903 uu____7905
    | If (t1, t2, t3) ->
        let uu____7911 = FStar_All.pipe_right t1 term_to_string in
        let uu____7914 = FStar_All.pipe_right t2 term_to_string in
        let uu____7917 = FStar_All.pipe_right t3 term_to_string in
        FStar_Util.format3 "if %s then %s else %s" uu____7911 uu____7914
          uu____7917
    | Match (t, branches) ->
        let s =
          match x.tm with
          | Match uu____7946 -> "match"
          | TryWith uu____7962 -> "try"
          | uu____7978 -> failwith "impossible" in
        let uu____7981 = FStar_All.pipe_right t term_to_string in
        let uu____7984 =
          to_string_l " | "
            (fun uu____8002 ->
               match uu____8002 with
               | (p, w, e) ->
                   let uu____8019 = FStar_All.pipe_right p pat_to_string in
                   let uu____8022 =
                     match w with
                     | FStar_Pervasives_Native.None -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____8027 = term_to_string e1 in
                         FStar_Util.format1 "when %s" uu____8027 in
                   let uu____8030 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____8019 uu____8022
                     uu____8030) branches in
        FStar_Util.format3 "%s %s with %s" s uu____7981 uu____7984
    | TryWith (t, branches) ->
        let s =
          match x.tm with
          | Match uu____8060 -> "match"
          | TryWith uu____8076 -> "try"
          | uu____8092 -> failwith "impossible" in
        let uu____8095 = FStar_All.pipe_right t term_to_string in
        let uu____8098 =
          to_string_l " | "
            (fun uu____8116 ->
               match uu____8116 with
               | (p, w, e) ->
                   let uu____8133 = FStar_All.pipe_right p pat_to_string in
                   let uu____8136 =
                     match w with
                     | FStar_Pervasives_Native.None -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____8141 = term_to_string e1 in
                         FStar_Util.format1 "when %s" uu____8141 in
                   let uu____8144 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format3 "%s %s -> %s" uu____8133 uu____8136
                     uu____8144) branches in
        FStar_Util.format3 "%s %s with %s" s uu____8095 uu____8098
    | Ascribed (t1, t2, FStar_Pervasives_Native.None) ->
        let uu____8153 = FStar_All.pipe_right t1 term_to_string in
        let uu____8156 = FStar_All.pipe_right t2 term_to_string in
        FStar_Util.format2 "(%s : %s)" uu____8153 uu____8156
    | Ascribed (t1, t2, FStar_Pervasives_Native.Some tac) ->
        let uu____8165 = FStar_All.pipe_right t1 term_to_string in
        let uu____8168 = FStar_All.pipe_right t2 term_to_string in
        let uu____8171 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s : %s by %s)" uu____8165 uu____8168 uu____8171
    | Record (FStar_Pervasives_Native.Some e, fields) ->
        let uu____8191 = FStar_All.pipe_right e term_to_string in
        let uu____8194 =
          to_string_l " "
            (fun uu____8206 ->
               match uu____8206 with
               | (l, e1) ->
                   let uu____8214 = FStar_Ident.string_of_lid l in
                   let uu____8216 = FStar_All.pipe_right e1 term_to_string in
                   FStar_Util.format2 "%s=%s" uu____8214 uu____8216) fields in
        FStar_Util.format2 "{%s with %s}" uu____8191 uu____8194
    | Record (FStar_Pervasives_Native.None, fields) ->
        let uu____8236 =
          to_string_l " "
            (fun uu____8248 ->
               match uu____8248 with
               | (l, e) ->
                   let uu____8256 = FStar_Ident.string_of_lid l in
                   let uu____8258 = FStar_All.pipe_right e term_to_string in
                   FStar_Util.format2 "%s=%s" uu____8256 uu____8258) fields in
        FStar_Util.format1 "{%s}" uu____8236
    | Project (e, l) ->
        let uu____8265 = FStar_All.pipe_right e term_to_string in
        let uu____8268 = FStar_Ident.string_of_lid l in
        FStar_Util.format2 "%s.%s" uu____8265 uu____8268
    | Product ([], t) -> term_to_string t
    | Product (b::hd::tl, t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd :: tl), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[], t) when x.level = Type_level ->
        let uu____8290 = FStar_All.pipe_right b binder_to_string in
        let uu____8293 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s -> %s" uu____8290 uu____8293
    | Product (b::[], t) when x.level = Kind ->
        let uu____8301 = FStar_All.pipe_right b binder_to_string in
        let uu____8304 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s => %s" uu____8301 uu____8304
    | Sum (binders, t) ->
        let uu____8322 =
          FStar_All.pipe_right (FStar_List.append binders [FStar_Util.Inr t])
            (FStar_List.map
               (fun uu___6_8354 ->
                  match uu___6_8354 with
                  | FStar_Util.Inl b -> binder_to_string b
                  | FStar_Util.Inr t1 -> term_to_string t1)) in
        FStar_All.pipe_right uu____8322 (FStar_String.concat " & ")
    | QForall (bs, (uu____8368, pats), t) ->
        let uu____8397 = to_string_l " " binder_to_string bs in
        let uu____8400 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____8406 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____8397 uu____8400
          uu____8406
    | QExists (bs, (uu____8411, pats), t) ->
        let uu____8440 = to_string_l " " binder_to_string bs in
        let uu____8443 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats in
        let uu____8449 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____8440 uu____8443
          uu____8449
    | Refine (b, t) ->
        let uu____8455 = FStar_All.pipe_right b binder_to_string in
        let uu____8458 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:{%s}" uu____8455 uu____8458
    | NamedTyp (x1, t) ->
        let uu____8464 = FStar_Ident.string_of_id x1 in
        let uu____8466 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "%s:%s" uu____8464 uu____8466
    | Paren t ->
        let uu____8471 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format1 "(%s)" uu____8471
    | Product (bs, t) ->
        let uu____8481 =
          let uu____8483 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
          FStar_All.pipe_right uu____8483 (FStar_String.concat ",") in
        let uu____8498 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____8481
          uu____8498
    | Discrim lid ->
        let uu____8503 = FStar_Ident.string_of_lid lid in
        FStar_Util.format1 "%s?" uu____8503
    | Attributes ts ->
        let uu____8509 =
          let uu____8511 = FStar_List.map term_to_string ts in
          FStar_All.pipe_left (FStar_String.concat " ") uu____8511 in
        FStar_Util.format1 "(attributes %s)" uu____8509
    | Antiquote t ->
        let uu____8523 = term_to_string t in
        FStar_Util.format1 "(`#%s)" uu____8523
    | Quote (t, Static) ->
        let uu____8527 = term_to_string t in
        FStar_Util.format1 "(`(%s))" uu____8527
    | Quote (t, Dynamic) ->
        let uu____8531 = term_to_string t in
        FStar_Util.format1 "quote (%s)" uu____8531
    | VQuote t ->
        let uu____8535 = term_to_string t in
        FStar_Util.format1 "`%%%s" uu____8535
    | CalcProof (rel, init, steps) ->
        let uu____8545 = term_to_string rel in
        let uu____8547 = term_to_string init in
        let uu____8549 =
          let uu____8551 = FStar_List.map calc_step_to_string steps in
          FStar_All.pipe_left (FStar_String.concat " ") uu____8551 in
        FStar_Util.format3 "calc (%s) { %s %s }" uu____8545 uu____8547
          uu____8549
and (calc_step_to_string : calc_step -> Prims.string) =
  fun uu____8562 ->
    match uu____8562 with
    | CalcStep (rel, just, next) ->
        let uu____8567 = term_to_string rel in
        let uu____8569 = term_to_string just in
        let uu____8571 = term_to_string next in
        FStar_Util.format3 "%s{ %s } %s" uu____8567 uu____8569 uu____8571
and (binder_to_string : binder -> Prims.string) =
  fun x ->
    let s =
      match x.b with
      | Variable i -> FStar_Ident.string_of_id i
      | TVariable i ->
          let uu____8580 = FStar_Ident.string_of_id i in
          FStar_Util.format1 "%s:_" uu____8580
      | TAnnotated (i, t) ->
          let uu____8585 = FStar_Ident.string_of_id i in
          let uu____8587 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" uu____8585 uu____8587
      | Annotated (i, t) ->
          let uu____8593 = FStar_Ident.string_of_id i in
          let uu____8595 = FStar_All.pipe_right t term_to_string in
          FStar_Util.format2 "%s:%s" uu____8593 uu____8595
      | NoName t -> FStar_All.pipe_right t term_to_string in
    let uu____8601 = aqual_to_string x.aqual in
    FStar_Util.format2 "%s%s" uu____8601 s
and (aqual_to_string :
  arg_qualifier FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___7_8604 ->
    match uu___7_8604 with
    | FStar_Pervasives_Native.Some (Equality) -> "$"
    | FStar_Pervasives_Native.Some (Implicit) -> "#"
    | uu____8610 -> ""
and (pat_to_string : pattern -> Prims.string) =
  fun x ->
    match x.pat with
    | PatWild (FStar_Pervasives_Native.None) -> "_"
    | PatWild uu____8617 -> "#_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p, ps) ->
        let uu____8628 = FStar_All.pipe_right p pat_to_string in
        let uu____8631 = to_string_l " " pat_to_string ps in
        FStar_Util.format2 "(%s %s)" uu____8628 uu____8631
    | PatTvar (i, aq) ->
        let uu____8641 = aqual_to_string aq in
        let uu____8643 = FStar_Ident.string_of_id i in
        FStar_Util.format2 "%s%s" uu____8641 uu____8643
    | PatVar (i, aq) ->
        let uu____8652 = aqual_to_string aq in
        let uu____8654 = FStar_Ident.string_of_id i in
        FStar_Util.format2 "%s%s" uu____8652 uu____8654
    | PatName l -> FStar_Ident.string_of_lid l
    | PatList l ->
        let uu____8661 = to_string_l "; " pat_to_string l in
        FStar_Util.format1 "[%s]" uu____8661
    | PatTuple (l, false) ->
        let uu____8672 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(%s)" uu____8672
    | PatTuple (l, true) ->
        let uu____8683 = to_string_l ", " pat_to_string l in
        FStar_Util.format1 "(|%s|)" uu____8683
    | PatRecord l ->
        let uu____8694 =
          to_string_l "; "
            (fun uu____8706 ->
               match uu____8706 with
               | (f, e) ->
                   let uu____8714 = FStar_Ident.string_of_lid f in
                   let uu____8716 = FStar_All.pipe_right e pat_to_string in
                   FStar_Util.format2 "%s=%s" uu____8714 uu____8716) l in
        FStar_Util.format1 "{%s}" uu____8694
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op ->
        let uu____8726 = FStar_Ident.string_of_id op in
        FStar_Util.format1 "(%s)" uu____8726
    | PatAscribed (p, (t, FStar_Pervasives_Native.None)) ->
        let uu____8739 = FStar_All.pipe_right p pat_to_string in
        let uu____8742 = FStar_All.pipe_right t term_to_string in
        FStar_Util.format2 "(%s:%s)" uu____8739 uu____8742
    | PatAscribed (p, (t, FStar_Pervasives_Native.Some tac)) ->
        let uu____8757 = FStar_All.pipe_right p pat_to_string in
        let uu____8760 = FStar_All.pipe_right t term_to_string in
        let uu____8763 = FStar_All.pipe_right tac term_to_string in
        FStar_Util.format3 "(%s:%s by %s)" uu____8757 uu____8760 uu____8763
and (attrs_opt_to_string :
  term Prims.list FStar_Pervasives_Native.option -> Prims.string) =
  fun uu___8_8767 ->
    match uu___8_8767 with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some attrs ->
        let uu____8781 =
          let uu____8783 = FStar_List.map term_to_string attrs in
          FStar_All.pipe_right uu____8783 (FStar_String.concat "; ") in
        FStar_Util.format1 "[@ %s]" uu____8781
let rec (head_id_of_pat : pattern -> FStar_Ident.lident Prims.list) =
  fun p ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i, uu____8806) ->
        let uu____8811 = FStar_Ident.lid_of_ids [i] in [uu____8811]
    | PatApp (p1, uu____8813) -> head_id_of_pat p1
    | PatAscribed (p1, uu____8819) -> head_id_of_pat p1
    | uu____8832 -> []
let lids_of_let :
  'uuuuuu8838 .
    (pattern * 'uuuuuu8838) Prims.list -> FStar_Ident.lident Prims.list
  =
  fun defs ->
    FStar_All.pipe_right defs
      (FStar_List.collect
         (fun uu____8873 ->
            match uu____8873 with | (p, uu____8881) -> head_id_of_pat p))
let (id_of_tycon : tycon -> Prims.string) =
  fun uu___9_8888 ->
    match uu___9_8888 with
    | TyconAbstract (i, uu____8891, uu____8892) -> FStar_Ident.string_of_id i
    | TyconAbbrev (i, uu____8902, uu____8903, uu____8904) ->
        FStar_Ident.string_of_id i
    | TyconRecord (i, uu____8914, uu____8915, uu____8916) ->
        FStar_Ident.string_of_id i
    | TyconVariant (i, uu____8938, uu____8939, uu____8940) ->
        FStar_Ident.string_of_id i
let (decl_to_string : decl -> Prims.string) =
  fun d ->
    match d.d with
    | TopLevelModule l ->
        let uu____8980 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "module " uu____8980
    | Open l ->
        let uu____8984 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "open " uu____8984
    | Friend l ->
        let uu____8988 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "friend " uu____8988
    | Include l ->
        let uu____8992 = FStar_Ident.string_of_lid l in
        Prims.op_Hat "include " uu____8992
    | ModuleAbbrev (i, l) ->
        let uu____8997 = FStar_Ident.string_of_id i in
        let uu____8999 = FStar_Ident.string_of_lid l in
        FStar_Util.format2 "module %s = %s" uu____8997 uu____8999
    | TopLevelLet (uu____9002, pats) ->
        let uu____9016 =
          let uu____9018 =
            let uu____9022 = lids_of_let pats in
            FStar_All.pipe_right uu____9022
              (FStar_List.map (fun l -> FStar_Ident.string_of_lid l)) in
          FStar_All.pipe_right uu____9018 (FStar_String.concat ", ") in
        Prims.op_Hat "let " uu____9016
    | Assume (i, uu____9040) ->
        let uu____9041 = FStar_Ident.string_of_id i in
        Prims.op_Hat "assume " uu____9041
    | Tycon (uu____9044, uu____9045, tys) ->
        let uu____9055 =
          let uu____9057 =
            FStar_All.pipe_right tys (FStar_List.map id_of_tycon) in
          FStar_All.pipe_right uu____9057 (FStar_String.concat ", ") in
        Prims.op_Hat "type " uu____9055
    | Val (i, uu____9074) ->
        let uu____9075 = FStar_Ident.string_of_id i in
        Prims.op_Hat "val " uu____9075
    | Exception (i, uu____9079) ->
        let uu____9084 = FStar_Ident.string_of_id i in
        Prims.op_Hat "exception " uu____9084
    | NewEffect (DefineEffect (i, uu____9088, uu____9089, uu____9090)) ->
        let uu____9099 = FStar_Ident.string_of_id i in
        Prims.op_Hat "new_effect " uu____9099
    | NewEffect (RedefineEffect (i, uu____9103, uu____9104)) ->
        let uu____9109 = FStar_Ident.string_of_id i in
        Prims.op_Hat "new_effect " uu____9109
    | LayeredEffect (DefineEffect (i, uu____9113, uu____9114, uu____9115)) ->
        let uu____9124 = FStar_Ident.string_of_id i in
        Prims.op_Hat "layered_effect " uu____9124
    | LayeredEffect (RedefineEffect (i, uu____9128, uu____9129)) ->
        let uu____9134 = FStar_Ident.string_of_id i in
        Prims.op_Hat "layered_effect " uu____9134
    | Polymonadic_bind (l1, l2, l3, uu____9140) ->
        let uu____9141 = FStar_Ident.string_of_lid l1 in
        let uu____9143 = FStar_Ident.string_of_lid l2 in
        let uu____9145 = FStar_Ident.string_of_lid l3 in
        FStar_Util.format3 "polymonadic_bind (%s, %s) |> %s" uu____9141
          uu____9143 uu____9145
    | Splice (ids, t) ->
        let uu____9154 =
          let uu____9156 =
            let uu____9158 =
              FStar_List.map (fun i -> FStar_Ident.string_of_id i) ids in
            FStar_All.pipe_left (FStar_String.concat ";") uu____9158 in
          let uu____9170 =
            let uu____9172 =
              let uu____9174 = term_to_string t in
              Prims.op_Hat uu____9174 ")" in
            Prims.op_Hat "] (" uu____9172 in
          Prims.op_Hat uu____9156 uu____9170 in
        Prims.op_Hat "splice[" uu____9154
    | SubEffect uu____9179 -> "sub_effect"
    | Pragma uu____9181 -> "pragma"
let (modul_to_string : modul -> Prims.string) =
  fun m ->
    match m with
    | Module (uu____9191, decls) ->
        let uu____9197 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____9197 (FStar_String.concat "\n")
    | Interface (uu____9212, decls, uu____9214) ->
        let uu____9221 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string) in
        FStar_All.pipe_right uu____9221 (FStar_String.concat "\n")
let (decl_is_val : FStar_Ident.ident -> decl -> Prims.bool) =
  fun id ->
    fun decl1 ->
      match decl1.d with
      | Val (id', uu____9250) -> FStar_Ident.ident_equals id id'
      | uu____9251 -> false
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
              | Annotated (i, uu____9289) -> i
              | TAnnotated (i, uu____9291) -> i
              | NoName uu____9292 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_MissingQuantifierBinder,
                      "Wildcard binders in quantifiers are not allowed") r))