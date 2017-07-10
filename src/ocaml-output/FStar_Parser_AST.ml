open Prims
type level =
  | Un 
  | Expr 
  | Type_level 
  | Kind 
  | Formula 
let uu___is_Un : level -> Prims.bool =
  fun projectee  -> match projectee with | Un  -> true | uu____4 -> false 
let uu___is_Expr : level -> Prims.bool =
  fun projectee  -> match projectee with | Expr  -> true | uu____8 -> false 
let uu___is_Type_level : level -> Prims.bool =
  fun projectee  ->
    match projectee with | Type_level  -> true | uu____12 -> false
  
let uu___is_Kind : level -> Prims.bool =
  fun projectee  -> match projectee with | Kind  -> true | uu____16 -> false 
let uu___is_Formula : level -> Prims.bool =
  fun projectee  ->
    match projectee with | Formula  -> true | uu____20 -> false
  
type imp =
  | FsTypApp 
  | Hash 
  | UnivApp 
  | Nothing 
let uu___is_FsTypApp : imp -> Prims.bool =
  fun projectee  ->
    match projectee with | FsTypApp  -> true | uu____24 -> false
  
let uu___is_Hash : imp -> Prims.bool =
  fun projectee  -> match projectee with | Hash  -> true | uu____28 -> false 
let uu___is_UnivApp : imp -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivApp  -> true | uu____32 -> false
  
let uu___is_Nothing : imp -> Prims.bool =
  fun projectee  ->
    match projectee with | Nothing  -> true | uu____36 -> false
  
type arg_qualifier =
  | Implicit 
  | Equality 
let uu___is_Implicit : arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Implicit  -> true | uu____40 -> false
  
let uu___is_Equality : arg_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Equality  -> true | uu____44 -> false
  
type aqual = arg_qualifier FStar_Pervasives_Native.option
type let_qualifier =
  | NoLetQualifier 
  | Rec 
  | Mutable 
let uu___is_NoLetQualifier : let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoLetQualifier  -> true | uu____49 -> false
  
let uu___is_Rec : let_qualifier -> Prims.bool =
  fun projectee  -> match projectee with | Rec  -> true | uu____53 -> false 
let uu___is_Mutable : let_qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Mutable  -> true | uu____57 -> false
  
type term' =
  | Wild 
  | Const of FStar_Const.sconst 
  | Op of (FStar_Ident.ident,term Prims.list) FStar_Pervasives_Native.tuple2
  
  | Tvar of FStar_Ident.ident 
  | Uvar of FStar_Ident.ident 
  | Var of FStar_Ident.lid 
  | Name of FStar_Ident.lid 
  | Projector of (FStar_Ident.lid,FStar_Ident.ident)
  FStar_Pervasives_Native.tuple2 
  | Construct of
  (FStar_Ident.lid,(term,imp) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Abs of (pattern Prims.list,term) FStar_Pervasives_Native.tuple2 
  | App of (term,term,imp) FStar_Pervasives_Native.tuple3 
  | Let of
  (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list,
  term) FStar_Pervasives_Native.tuple3 
  | LetOpen of (FStar_Ident.lid,term) FStar_Pervasives_Native.tuple2 
  | Seq of (term,term) FStar_Pervasives_Native.tuple2 
  | Bind of (FStar_Ident.ident,term,term) FStar_Pervasives_Native.tuple3 
  | If of (term,term,term) FStar_Pervasives_Native.tuple3 
  | Match of
  (term,(pattern,term FStar_Pervasives_Native.option,term)
          FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | TryWith of
  (term,(pattern,term FStar_Pervasives_Native.option,term)
          FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Ascribed of (term,term,term FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3 
  | Record of
  (term FStar_Pervasives_Native.option,(FStar_Ident.lid,term)
                                         FStar_Pervasives_Native.tuple2
                                         Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Project of (term,FStar_Ident.lid) FStar_Pervasives_Native.tuple2 
  | Product of (binder Prims.list,term) FStar_Pervasives_Native.tuple2 
  | Sum of (binder Prims.list,term) FStar_Pervasives_Native.tuple2 
  | QForall of (binder Prims.list,term Prims.list Prims.list,term)
  FStar_Pervasives_Native.tuple3 
  | QExists of (binder Prims.list,term Prims.list Prims.list,term)
  FStar_Pervasives_Native.tuple3 
  | Refine of (binder,term) FStar_Pervasives_Native.tuple2 
  | NamedTyp of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | Paren of term 
  | Requires of (term,Prims.string FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | Ensures of (term,Prims.string FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | Labeled of (term,Prims.string,Prims.bool) FStar_Pervasives_Native.tuple3
  
  | Assign of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | Discrim of FStar_Ident.lid 
  | Attributes of term Prims.list 
and term = {
  tm: term' ;
  range: FStar_Range.range ;
  level: level }
and binder' =
  | Variable of FStar_Ident.ident 
  | TVariable of FStar_Ident.ident 
  | Annotated of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | TAnnotated of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | NoName of term 
and binder =
  {
  b: binder' ;
  brange: FStar_Range.range ;
  blevel: level ;
  aqual: aqual }
and pattern' =
  | PatWild 
  | PatConst of FStar_Const.sconst 
  | PatApp of (pattern,pattern Prims.list) FStar_Pervasives_Native.tuple2 
  | PatVar of
  (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | PatName of FStar_Ident.lid 
  | PatTvar of
  (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | PatList of pattern Prims.list 
  | PatTuple of (pattern Prims.list,Prims.bool)
  FStar_Pervasives_Native.tuple2 
  | PatRecord of (FStar_Ident.lid,pattern) FStar_Pervasives_Native.tuple2
  Prims.list 
  | PatAscribed of (pattern,term) FStar_Pervasives_Native.tuple2 
  | PatOr of pattern Prims.list 
  | PatOp of FStar_Ident.ident 
and pattern = {
  pat: pattern' ;
  prange: FStar_Range.range }
let uu___is_Wild : term' -> Prims.bool =
  fun projectee  -> match projectee with | Wild  -> true | uu____408 -> false 
let uu___is_Const : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____413 -> false
  
let __proj__Const__item___0 : term' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | Const _0 -> _0 
let uu___is_Op : term' -> Prims.bool =
  fun projectee  -> match projectee with | Op _0 -> true | uu____428 -> false 
let __proj__Op__item___0 :
  term' -> (FStar_Ident.ident,term Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Op _0 -> _0 
let uu___is_Tvar : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tvar _0 -> true | uu____449 -> false
  
let __proj__Tvar__item___0 : term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Tvar _0 -> _0 
let uu___is_Uvar : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Uvar _0 -> true | uu____461 -> false
  
let __proj__Uvar__item___0 : term' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Uvar _0 -> _0 
let uu___is_Var : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____473 -> false
  
let __proj__Var__item___0 : term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Var _0 -> _0 
let uu___is_Name : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____485 -> false
  
let __proj__Name__item___0 : term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0 
let uu___is_Projector : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Projector _0 -> true | uu____499 -> false
  
let __proj__Projector__item___0 :
  term' -> (FStar_Ident.lid,FStar_Ident.ident) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Projector _0 -> _0 
let uu___is_Construct : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____522 -> false
  
let __proj__Construct__item___0 :
  term' ->
    (FStar_Ident.lid,(term,imp) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let uu___is_Abs : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____552 -> false
  
let __proj__Abs__item___0 :
  term' -> (pattern Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Abs _0 -> _0 
let uu___is_App : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____576 -> false
  
let __proj__App__item___0 :
  term' -> (term,term,imp) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Let : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____603 -> false
  
let __proj__Let__item___0 :
  term' ->
    (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list,
      term) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_LetOpen : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LetOpen _0 -> true | uu____635 -> false
  
let __proj__LetOpen__item___0 :
  term' -> (FStar_Ident.lid,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LetOpen _0 -> _0 
let uu___is_Seq : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Seq _0 -> true | uu____655 -> false
  
let __proj__Seq__item___0 :
  term' -> (term,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Seq _0 -> _0 
let uu___is_Bind : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Bind _0 -> true | uu____676 -> false
  
let __proj__Bind__item___0 :
  term' -> (FStar_Ident.ident,term,term) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | Bind _0 -> _0 
let uu___is_If : term' -> Prims.bool =
  fun projectee  -> match projectee with | If _0 -> true | uu____700 -> false 
let __proj__If__item___0 :
  term' -> (term,term,term) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | If _0 -> _0 
let uu___is_Match : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____728 -> false
  
let __proj__Match__item___0 :
  term' ->
    (term,(pattern,term FStar_Pervasives_Native.option,term)
            FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Match _0 -> _0 
let uu___is_TryWith : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TryWith _0 -> true | uu____768 -> false
  
let __proj__TryWith__item___0 :
  term' ->
    (term,(pattern,term FStar_Pervasives_Native.option,term)
            FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TryWith _0 -> _0 
let uu___is_Ascribed : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ascribed _0 -> true | uu____805 -> false
  
let __proj__Ascribed__item___0 :
  term' ->
    (term,term,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Ascribed _0 -> _0 
let uu___is_Record : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Record _0 -> true | uu____835 -> false
  
let __proj__Record__item___0 :
  term' ->
    (term FStar_Pervasives_Native.option,(FStar_Ident.lid,term)
                                           FStar_Pervasives_Native.tuple2
                                           Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Record _0 -> _0 
let uu___is_Project : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Project _0 -> true | uu____867 -> false
  
let __proj__Project__item___0 :
  term' -> (term,FStar_Ident.lid) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Project _0 -> _0 
let uu___is_Product : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Product _0 -> true | uu____888 -> false
  
let __proj__Product__item___0 :
  term' -> (binder Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Product _0 -> _0 
let uu___is_Sum : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Sum _0 -> true | uu____912 -> false
  
let __proj__Sum__item___0 :
  term' -> (binder Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Sum _0 -> _0 
let uu___is_QForall : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QForall _0 -> true | uu____939 -> false
  
let __proj__QForall__item___0 :
  term' ->
    (binder Prims.list,term Prims.list Prims.list,term)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QForall _0 -> _0 
let uu___is_QExists : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | QExists _0 -> true | uu____975 -> false
  
let __proj__QExists__item___0 :
  term' ->
    (binder Prims.list,term Prims.list Prims.list,term)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | QExists _0 -> _0 
let uu___is_Refine : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Refine _0 -> true | uu____1007 -> false
  
let __proj__Refine__item___0 :
  term' -> (binder,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Refine _0 -> _0 
let uu___is_NamedTyp : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NamedTyp _0 -> true | uu____1027 -> false
  
let __proj__NamedTyp__item___0 :
  term' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | NamedTyp _0 -> _0 
let uu___is_Paren : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Paren _0 -> true | uu____1045 -> false
  
let __proj__Paren__item___0 : term' -> term =
  fun projectee  -> match projectee with | Paren _0 -> _0 
let uu___is_Requires : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Requires _0 -> true | uu____1060 -> false
  
let __proj__Requires__item___0 :
  term' ->
    (term,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Requires _0 -> _0 
let uu___is_Ensures : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Ensures _0 -> true | uu____1084 -> false
  
let __proj__Ensures__item___0 :
  term' ->
    (term,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Ensures _0 -> _0 
let uu___is_Labeled : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____1108 -> false
  
let __proj__Labeled__item___0 :
  term' -> (term,Prims.string,Prims.bool) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let uu___is_Assign : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assign _0 -> true | uu____1131 -> false
  
let __proj__Assign__item___0 :
  term' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Assign _0 -> _0 
let uu___is_Discrim : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Discrim _0 -> true | uu____1149 -> false
  
let __proj__Discrim__item___0 : term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Discrim _0 -> _0 
let uu___is_Attributes : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Attributes _0 -> true | uu____1162 -> false
  
let __proj__Attributes__item___0 : term' -> term Prims.list =
  fun projectee  -> match projectee with | Attributes _0 -> _0 
let uu___is_Variable : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Variable _0 -> true | uu____1189 -> false
  
let __proj__Variable__item___0 : binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Variable _0 -> _0 
let uu___is_TVariable : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TVariable _0 -> true | uu____1201 -> false
  
let __proj__TVariable__item___0 : binder' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | TVariable _0 -> _0 
let uu___is_Annotated : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | Annotated _0 -> true | uu____1215 -> false
  
let __proj__Annotated__item___0 :
  binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Annotated _0 -> _0 
let uu___is_TAnnotated : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | TAnnotated _0 -> true | uu____1235 -> false
  
let __proj__TAnnotated__item___0 :
  binder' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | TAnnotated _0 -> _0 
let uu___is_NoName : binder' -> Prims.bool =
  fun projectee  ->
    match projectee with | NoName _0 -> true | uu____1253 -> false
  
let __proj__NoName__item___0 : binder' -> term =
  fun projectee  -> match projectee with | NoName _0 -> _0 
let uu___is_PatWild : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatWild  -> true | uu____1280 -> false
  
let uu___is_PatConst : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatConst _0 -> true | uu____1285 -> false
  
let __proj__PatConst__item___0 : pattern' -> FStar_Const.sconst =
  fun projectee  -> match projectee with | PatConst _0 -> _0 
let uu___is_PatApp : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatApp _0 -> true | uu____1300 -> false
  
let __proj__PatApp__item___0 :
  pattern' -> (pattern,pattern Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | PatApp _0 -> _0 
let uu___is_PatVar : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatVar _0 -> true | uu____1324 -> false
  
let __proj__PatVar__item___0 :
  pattern' ->
    (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PatVar _0 -> _0 
let uu___is_PatName : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatName _0 -> true | uu____1345 -> false
  
let __proj__PatName__item___0 : pattern' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | PatName _0 -> _0 
let uu___is_PatTvar : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTvar _0 -> true | uu____1360 -> false
  
let __proj__PatTvar__item___0 :
  pattern' ->
    (FStar_Ident.ident,arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PatTvar _0 -> _0 
let uu___is_PatList : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatList _0 -> true | uu____1382 -> false
  
let __proj__PatList__item___0 : pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatList _0 -> _0 
let uu___is_PatTuple : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatTuple _0 -> true | uu____1400 -> false
  
let __proj__PatTuple__item___0 :
  pattern' -> (pattern Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PatTuple _0 -> _0 
let uu___is_PatRecord : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatRecord _0 -> true | uu____1424 -> false
  
let __proj__PatRecord__item___0 :
  pattern' ->
    (FStar_Ident.lid,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PatRecord _0 -> _0 
let uu___is_PatAscribed : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatAscribed _0 -> true | uu____1447 -> false
  
let __proj__PatAscribed__item___0 :
  pattern' -> (pattern,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | PatAscribed _0 -> _0 
let uu___is_PatOr : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOr _0 -> true | uu____1466 -> false
  
let __proj__PatOr__item___0 : pattern' -> pattern Prims.list =
  fun projectee  -> match projectee with | PatOr _0 -> _0 
let uu___is_PatOp : pattern' -> Prims.bool =
  fun projectee  ->
    match projectee with | PatOp _0 -> true | uu____1481 -> false
  
let __proj__PatOp__item___0 : pattern' -> FStar_Ident.ident =
  fun projectee  -> match projectee with | PatOp _0 -> _0 
type branch =
  (pattern,term FStar_Pervasives_Native.option,term)
    FStar_Pervasives_Native.tuple3
type knd = term
type typ = term
type expr = term
type fsdoc =
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2
type tycon =
  | TyconAbstract of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple3 
  | TyconAbbrev of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
  term) FStar_Pervasives_Native.tuple4 
  | TyconRecord of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
  (FStar_Ident.ident,term,fsdoc FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 Prims.list)
  FStar_Pervasives_Native.tuple4 
  | TyconVariant of
  (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
  (FStar_Ident.ident,term FStar_Pervasives_Native.option,fsdoc
                                                           FStar_Pervasives_Native.option,
    Prims.bool) FStar_Pervasives_Native.tuple4 Prims.list)
  FStar_Pervasives_Native.tuple4 
let uu___is_TyconAbstract : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbstract _0 -> true | uu____1566 -> false
  
let __proj__TyconAbstract__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | TyconAbstract _0 -> _0 
let uu___is_TyconAbbrev : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconAbbrev _0 -> true | uu____1599 -> false
  
let __proj__TyconAbbrev__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      term) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | TyconAbbrev _0 -> _0 
let uu___is_TyconRecord : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconRecord _0 -> true | uu____1640 -> false
  
let __proj__TyconRecord__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      (FStar_Ident.ident,term,fsdoc FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | TyconRecord _0 -> _0 
let uu___is_TyconVariant : tycon -> Prims.bool =
  fun projectee  ->
    match projectee with | TyconVariant _0 -> true | uu____1698 -> false
  
let __proj__TyconVariant__item___0 :
  tycon ->
    (FStar_Ident.ident,binder Prims.list,knd FStar_Pervasives_Native.option,
      (FStar_Ident.ident,term FStar_Pervasives_Native.option,fsdoc
                                                               FStar_Pervasives_Native.option,
        Prims.bool) FStar_Pervasives_Native.tuple4 Prims.list)
      FStar_Pervasives_Native.tuple4
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
let uu___is_Private : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1748 -> false
  
let uu___is_Abstract : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1752 -> false
  
let uu___is_Noeq : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Noeq  -> true | uu____1756 -> false
  
let uu___is_Unopteq : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Unopteq  -> true | uu____1760 -> false
  
let uu___is_Assumption : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Assumption  -> true | uu____1764 -> false
  
let uu___is_DefaultEffect : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | DefaultEffect  -> true | uu____1768 -> false
  
let uu___is_TotalEffect : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | TotalEffect  -> true | uu____1772 -> false
  
let uu___is_Effect_qual : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Effect_qual  -> true | uu____1776 -> false
  
let uu___is_New : qualifier -> Prims.bool =
  fun projectee  -> match projectee with | New  -> true | uu____1780 -> false 
let uu___is_Inline : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Inline  -> true | uu____1784 -> false
  
let uu___is_Visible : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Visible  -> true | uu____1788 -> false
  
let uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Unfold_for_unification_and_vcgen  -> true
    | uu____1792 -> false
  
let uu___is_Inline_for_extraction : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Inline_for_extraction  -> true
    | uu____1796 -> false
  
let uu___is_Irreducible : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Irreducible  -> true | uu____1800 -> false
  
let uu___is_NoExtract : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1804 -> false
  
let uu___is_Reifiable : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reifiable  -> true | uu____1808 -> false
  
let uu___is_Reflectable : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Reflectable  -> true | uu____1812 -> false
  
let uu___is_Opaque : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Opaque  -> true | uu____1816 -> false
  
let uu___is_Logic : qualifier -> Prims.bool =
  fun projectee  ->
    match projectee with | Logic  -> true | uu____1820 -> false
  
type qualifiers = qualifier Prims.list
type attributes_ = term Prims.list
type decoration =
  | Qualifier of qualifier 
  | DeclAttributes of term Prims.list 
  | Doc of fsdoc 
let uu___is_Qualifier : decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Qualifier _0 -> true | uu____1840 -> false
  
let __proj__Qualifier__item___0 : decoration -> qualifier =
  fun projectee  -> match projectee with | Qualifier _0 -> _0 
let uu___is_DeclAttributes : decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclAttributes _0 -> true | uu____1853 -> false
  
let __proj__DeclAttributes__item___0 : decoration -> term Prims.list =
  fun projectee  -> match projectee with | DeclAttributes _0 -> _0 
let uu___is_Doc : decoration -> Prims.bool =
  fun projectee  ->
    match projectee with | Doc _0 -> true | uu____1868 -> false
  
let __proj__Doc__item___0 : decoration -> fsdoc =
  fun projectee  -> match projectee with | Doc _0 -> _0 
type lift_op =
  | NonReifiableLift of term 
  | ReifiableLift of (term,term) FStar_Pervasives_Native.tuple2 
  | LiftForFree of term 
let uu___is_NonReifiableLift : lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | NonReifiableLift _0 -> true | uu____1894 -> false
  
let __proj__NonReifiableLift__item___0 : lift_op -> term =
  fun projectee  -> match projectee with | NonReifiableLift _0 -> _0 
let uu___is_ReifiableLift : lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | ReifiableLift _0 -> true | uu____1908 -> false
  
let __proj__ReifiableLift__item___0 :
  lift_op -> (term,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ReifiableLift _0 -> _0 
let uu___is_LiftForFree : lift_op -> Prims.bool =
  fun projectee  ->
    match projectee with | LiftForFree _0 -> true | uu____1926 -> false
  
let __proj__LiftForFree__item___0 : lift_op -> term =
  fun projectee  -> match projectee with | LiftForFree _0 -> _0 
type lift =
  {
  msource: FStar_Ident.lid ;
  mdest: FStar_Ident.lid ;
  lift_op: lift_op }
type pragma =
  | SetOptions of Prims.string 
  | ResetOptions of Prims.string FStar_Pervasives_Native.option 
  | LightOff 
let uu___is_SetOptions : pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOptions _0 -> true | uu____1971 -> false
  
let __proj__SetOptions__item___0 : pragma -> Prims.string =
  fun projectee  -> match projectee with | SetOptions _0 -> _0 
let uu___is_ResetOptions : pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | ResetOptions _0 -> true | uu____1984 -> false
  
let __proj__ResetOptions__item___0 :
  pragma -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  -> match projectee with | ResetOptions _0 -> _0 
let uu___is_LightOff : pragma -> Prims.bool =
  fun projectee  ->
    match projectee with | LightOff  -> true | uu____1998 -> false
  
type decl' =
  | TopLevelModule of FStar_Ident.lid 
  | Open of FStar_Ident.lid 
  | Include of FStar_Ident.lid 
  | ModuleAbbrev of (FStar_Ident.ident,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple2 
  | TopLevelLet of
  (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Main of term 
  | Tycon of
  (Prims.bool,(tycon,fsdoc FStar_Pervasives_Native.option)
                FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Val of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
  | Exception of (FStar_Ident.ident,term FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | NewEffect of effect_decl 
  | SubEffect of lift 
  | Pragma of pragma 
  | Fsdoc of fsdoc 
  | Assume of (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 
and decl =
  {
  d: decl' ;
  drange: FStar_Range.range ;
  doc: fsdoc FStar_Pervasives_Native.option ;
  quals: qualifiers ;
  attrs: attributes_ }
and effect_decl =
  | DefineEffect of
  (FStar_Ident.ident,binder Prims.list,term,decl Prims.list)
  FStar_Pervasives_Native.tuple4 
  | RedefineEffect of (FStar_Ident.ident,binder Prims.list,term)
  FStar_Pervasives_Native.tuple3 
let uu___is_TopLevelModule : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelModule _0 -> true | uu____2118 -> false
  
let __proj__TopLevelModule__item___0 : decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TopLevelModule _0 -> _0 
let uu___is_Open : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Open _0 -> true | uu____2130 -> false
  
let __proj__Open__item___0 : decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Open _0 -> _0 
let uu___is_Include : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Include _0 -> true | uu____2142 -> false
  
let __proj__Include__item___0 : decl' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Include _0 -> _0 
let uu___is_ModuleAbbrev : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleAbbrev _0 -> true | uu____2156 -> false
  
let __proj__ModuleAbbrev__item___0 :
  decl' -> (FStar_Ident.ident,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | ModuleAbbrev _0 -> _0 
let uu___is_TopLevelLet : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____2179 -> false
  
let __proj__TopLevelLet__item___0 :
  decl' ->
    (let_qualifier,(pattern,term) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let uu___is_Main : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Main _0 -> true | uu____2206 -> false
  
let __proj__Main__item___0 : decl' -> term =
  fun projectee  -> match projectee with | Main _0 -> _0 
let uu___is_Tycon : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Tycon _0 -> true | uu____2224 -> false
  
let __proj__Tycon__item___0 :
  decl' ->
    (Prims.bool,(tycon,fsdoc FStar_Pervasives_Native.option)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tycon _0 -> _0 
let uu___is_Val : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Val _0 -> true | uu____2256 -> false
  
let __proj__Val__item___0 :
  decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Val _0 -> _0 
let uu___is_Exception : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exception _0 -> true | uu____2277 -> false
  
let __proj__Exception__item___0 :
  decl' ->
    (FStar_Ident.ident,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Exception _0 -> _0 
let uu___is_NewEffect : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | NewEffect _0 -> true | uu____2298 -> false
  
let __proj__NewEffect__item___0 : decl' -> effect_decl =
  fun projectee  -> match projectee with | NewEffect _0 -> _0 
let uu___is_SubEffect : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | SubEffect _0 -> true | uu____2310 -> false
  
let __proj__SubEffect__item___0 : decl' -> lift =
  fun projectee  -> match projectee with | SubEffect _0 -> _0 
let uu___is_Pragma : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Pragma _0 -> true | uu____2322 -> false
  
let __proj__Pragma__item___0 : decl' -> pragma =
  fun projectee  -> match projectee with | Pragma _0 -> _0 
let uu___is_Fsdoc : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Fsdoc _0 -> true | uu____2334 -> false
  
let __proj__Fsdoc__item___0 : decl' -> fsdoc =
  fun projectee  -> match projectee with | Fsdoc _0 -> _0 
let uu___is_Assume : decl' -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____2348 -> false
  
let __proj__Assume__item___0 :
  decl' -> (FStar_Ident.ident,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let uu___is_DefineEffect : effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineEffect _0 -> true | uu____2394 -> false
  
let __proj__DefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident,binder Prims.list,term,decl Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DefineEffect _0 -> _0 
let uu___is_RedefineEffect : effect_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RedefineEffect _0 -> true | uu____2428 -> false
  
let __proj__RedefineEffect__item___0 :
  effect_decl ->
    (FStar_Ident.ident,binder Prims.list,term) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | RedefineEffect _0 -> _0 
type modul =
  | Module of (FStar_Ident.lid,decl Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Interface of (FStar_Ident.lid,decl Prims.list,Prims.bool)
  FStar_Pervasives_Native.tuple3 
let uu___is_Module : modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____2470 -> false
  
let __proj__Module__item___0 :
  modul -> (FStar_Ident.lid,decl Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Module _0 -> _0 
let uu___is_Interface : modul -> Prims.bool =
  fun projectee  ->
    match projectee with | Interface _0 -> true | uu____2495 -> false
  
let __proj__Interface__item___0 :
  modul ->
    (FStar_Ident.lid,decl Prims.list,Prims.bool)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Interface _0 -> _0 
type file = modul Prims.list
type inputFragment = (file,decl Prims.list) FStar_Util.either
let check_id : FStar_Ident.ident -> Prims.unit =
  fun id  ->
    let first_char =
      FStar_String.substring id.FStar_Ident.idText (Prims.parse_int "0")
        (Prims.parse_int "1")
       in
    if (FStar_String.lowercase first_char) = first_char
    then ()
    else
      (let uu____2524 =
         let uu____2525 =
           let uu____2528 =
             FStar_Util.format1
               "Invalid identifer '%s'; expected a symbol that begins with a lower-case character"
               id.FStar_Ident.idText
              in
           (uu____2528, (id.FStar_Ident.idRange))  in
         FStar_Errors.Error uu____2525  in
       raise uu____2524)
  
let at_most_one s r l =
  match l with
  | x::[] -> FStar_Pervasives_Native.Some x
  | [] -> FStar_Pervasives_Native.None
  | uu____2550 ->
      let uu____2552 =
        let uu____2553 =
          let uu____2556 =
            FStar_Util.format1 "At most one %s is allowed on declarations" s
             in
          (uu____2556, r)  in
        FStar_Errors.Error uu____2553  in
      raise uu____2552
  
let mk_decl : decl' -> FStar_Range.range -> decoration Prims.list -> decl =
  fun d  ->
    fun r  ->
      fun decorations  ->
        let doc1 =
          let uu____2571 =
            FStar_List.choose
              (fun uu___75_2573  ->
                 match uu___75_2573 with
                 | Doc d1 -> FStar_Pervasives_Native.Some d1
                 | uu____2576 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "fsdoc" r uu____2571  in
        let attributes_ =
          let uu____2580 =
            FStar_List.choose
              (fun uu___76_2584  ->
                 match uu___76_2584 with
                 | DeclAttributes a -> FStar_Pervasives_Native.Some a
                 | uu____2590 -> FStar_Pervasives_Native.None) decorations
             in
          at_most_one "attribute set" r uu____2580  in
        let attributes_1 = FStar_Util.dflt [] attributes_  in
        let qualifiers =
          FStar_List.choose
            (fun uu___77_2598  ->
               match uu___77_2598 with
               | Qualifier q -> FStar_Pervasives_Native.Some q
               | uu____2601 -> FStar_Pervasives_Native.None) decorations
           in
        { d; drange = r; doc = doc1; quals = qualifiers; attrs = attributes_1
        }
  
let mk_binder : binder' -> FStar_Range.range -> level -> aqual -> binder =
  fun b  ->
    fun r  -> fun l  -> fun i  -> { b; brange = r; blevel = l; aqual = i }
  
let mk_term : term' -> FStar_Range.range -> level -> term =
  fun t  -> fun r  -> fun l  -> { tm = t; range = r; level = l } 
let mk_uminus :
  term -> FStar_Range.range -> FStar_Range.range -> level -> term =
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
                     ((Prims.strcat "-" s),
                       (FStar_Pervasives_Native.Some
                          (FStar_Const.Signed, width))))
            | uu____2648 -> Op ((FStar_Ident.mk_ident ("-", rminus)), [t])
             in
          mk_term t1 r l
  
let mk_pattern : pattern' -> FStar_Range.range -> pattern =
  fun p  -> fun r  -> { pat = p; prange = r } 
let un_curry_abs : pattern Prims.list -> term -> term' =
  fun ps  ->
    fun body  ->
      match body.tm with
      | Abs (p',body') -> Abs ((FStar_List.append ps p'), body')
      | uu____2669 -> Abs (ps, body)
  
let mk_function :
  (pattern,term FStar_Pervasives_Native.option,term)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    FStar_Range.range -> FStar_Range.range -> term
  =
  fun branches  ->
    fun r1  ->
      fun r2  ->
        let x = let i = FStar_Parser_Const.next_id ()  in FStar_Ident.gen r1
           in
        let uu____2692 =
          let uu____2693 =
            let uu____2697 =
              let uu____2698 =
                let uu____2699 =
                  let uu____2707 =
                    let uu____2708 =
                      let uu____2709 = FStar_Ident.lid_of_ids [x]  in
                      Var uu____2709  in
                    mk_term uu____2708 r1 Expr  in
                  (uu____2707, branches)  in
                Match uu____2699  in
              mk_term uu____2698 r2 Expr  in
            ([mk_pattern (PatVar (x, FStar_Pervasives_Native.None)) r1],
              uu____2697)
             in
          Abs uu____2693  in
        mk_term uu____2692 r2 Expr
  
let un_function :
  pattern ->
    term ->
      (pattern,term) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun p  ->
    fun tm  ->
      match ((p.pat), (tm.tm)) with
      | (PatVar uu____2729,Abs (pats,body)) ->
          FStar_Pervasives_Native.Some
            ((mk_pattern (PatApp (p, pats)) p.prange), body)
      | uu____2740 -> FStar_Pervasives_Native.None
  
let lid_with_range :
  FStar_Ident.lident -> FStar_Range.range -> FStar_Ident.lident =
  fun lid  ->
    fun r  ->
      let uu____2751 = FStar_Ident.path_of_lid lid  in
      FStar_Ident.lid_of_path uu____2751 r
  
let consPat : FStar_Range.range -> pattern -> pattern -> pattern' =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        PatApp
          ((mk_pattern (PatName FStar_Parser_Const.cons_lid) r), [hd1; tl1])
  
let consTerm : FStar_Range.range -> term -> term -> term =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.cons_lid, [(hd1, Nothing); (tl1, Nothing)]))
          r Expr
  
let lexConsTerm : FStar_Range.range -> term -> term -> term =
  fun r  ->
    fun hd1  ->
      fun tl1  ->
        mk_term
          (Construct
             (FStar_Parser_Const.lexcons_lid,
               [(hd1, Nothing); (tl1, Nothing)])) r Expr
  
let mkConsList : FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let nil = mk_term (Construct (FStar_Parser_Const.nil_lid, [])) r Expr
         in
      FStar_List.fold_right (fun e  -> fun tl1  -> consTerm r e tl1) elts nil
  
let mkLexList : FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let nil =
        mk_term (Construct (FStar_Parser_Const.lextop_lid, [])) r Expr  in
      FStar_List.fold_right (fun e  -> fun tl1  -> lexConsTerm r e tl1) elts
        nil
  
let ml_comp : term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_ML_lid) t.range Expr  in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let tot_comp : term -> term =
  fun t  ->
    let ml = mk_term (Name FStar_Parser_Const.effect_Tot_lid) t.range Expr
       in
    let t1 = mk_term (App (ml, t, Nothing)) t.range Expr  in t1
  
let mkApp :
  term ->
    (term,imp) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range -> term
  =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____2858 ->
            (match t.tm with
             | Name s -> mk_term (Construct (s, args)) r Un
             | uu____2866 ->
                 FStar_List.fold_left
                   (fun t1  ->
                      fun uu____2870  ->
                        match uu____2870 with
                        | (a,imp) -> mk_term (App (t1, a, imp)) r Un) t args)
  
let mkRefSet : FStar_Range.range -> term Prims.list -> term =
  fun r  ->
    fun elts  ->
      let uu____2883 =
        (FStar_Parser_Const.tset_empty, FStar_Parser_Const.tset_singleton,
          FStar_Parser_Const.tset_union)
         in
      match uu____2883 with
      | (empty_lid,singleton_lid,union_lid) ->
          let empty1 =
            mk_term (Var (FStar_Ident.set_lid_range empty_lid r)) r Expr  in
          let ref_constr =
            mk_term
              (Var (FStar_Ident.set_lid_range FStar_Parser_Const.heap_ref r))
              r Expr
             in
          let singleton1 =
            mk_term (Var (FStar_Ident.set_lid_range singleton_lid r)) r Expr
             in
          let union1 =
            mk_term (Var (FStar_Ident.set_lid_range union_lid r)) r Expr  in
          FStar_List.fold_right
            (fun e  ->
               fun tl1  ->
                 let e1 = mkApp ref_constr [(e, Nothing)] r  in
                 let single_e = mkApp singleton1 [(e1, Nothing)] r  in
                 mkApp union1 [(single_e, Nothing); (tl1, Nothing)] r) elts
            empty1
  
let mkExplicitApp : term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        match args with
        | [] -> t
        | uu____2923 ->
            (match t.tm with
             | Name s ->
                 let uu____2926 =
                   let uu____2927 =
                     let uu____2933 =
                       FStar_List.map (fun a  -> (a, Nothing)) args  in
                     (s, uu____2933)  in
                   Construct uu____2927  in
                 mk_term uu____2926 r Un
             | uu____2943 ->
                 FStar_List.fold_left
                   (fun t1  -> fun a  -> mk_term (App (t1, a, Nothing)) r Un)
                   t args)
  
let mkAdmitMagic : FStar_Range.range -> term =
  fun r  ->
    let unit_const = mk_term (Const FStar_Const.Const_unit) r Expr  in
    let admit1 =
      let admit_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Parser_Const.admit_lid r)) r
          Expr
         in
      mkExplicitApp admit_name [unit_const] r  in
    let magic1 =
      let magic_name =
        mk_term
          (Var (FStar_Ident.set_lid_range FStar_Parser_Const.magic_lid r)) r
          Expr
         in
      mkExplicitApp magic_name [unit_const] r  in
    let admit_magic = mk_term (Seq (admit1, magic1)) r Expr  in admit_magic
  
let mkWildAdmitMagic r =
  let uu____2966 = mkAdmitMagic r  in
  ((mk_pattern PatWild r), FStar_Pervasives_Native.None, uu____2966) 
let focusBranches branches r =
  let should_filter =
    FStar_Util.for_some FStar_Pervasives_Native.fst branches  in
  if should_filter
  then
    (FStar_Errors.warn r "Focusing on only some cases";
     (let focussed =
        let uu____3022 =
          FStar_List.filter FStar_Pervasives_Native.fst branches  in
        FStar_All.pipe_right uu____3022
          (FStar_List.map FStar_Pervasives_Native.snd)
         in
      let uu____3066 = let uu____3072 = mkWildAdmitMagic r  in [uu____3072]
         in
      FStar_List.append focussed uu____3066))
  else
    FStar_All.pipe_right branches
      (FStar_List.map FStar_Pervasives_Native.snd)
  
let focusLetBindings lbs r =
  let should_filter = FStar_Util.for_some FStar_Pervasives_Native.fst lbs  in
  if should_filter
  then
    (FStar_Errors.warn r
       "Focusing on only some cases in this (mutually) recursive definition";
     FStar_List.map
       (fun uu____3158  ->
          match uu____3158 with
          | (f,lb) ->
              if f
              then lb
              else
                (let uu____3174 = mkAdmitMagic r  in
                 ((FStar_Pervasives_Native.fst lb), uu____3174))) lbs)
  else FStar_All.pipe_right lbs (FStar_List.map FStar_Pervasives_Native.snd) 
let mkFsTypApp : term -> term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun args  ->
      fun r  ->
        let uu____3203 = FStar_List.map (fun a  -> (a, FsTypApp)) args  in
        mkApp t uu____3203 r
  
let mkTuple : term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args) r  in
      let uu____3222 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____3222 r
  
let mkDTuple : term Prims.list -> FStar_Range.range -> term =
  fun args  ->
    fun r  ->
      let cons1 =
        FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args) r  in
      let uu____3241 = FStar_List.map (fun x  -> (x, Nothing)) args  in
      mkApp (mk_term (Name cons1) r Expr) uu____3241 r
  
let mkRefinedBinder :
  FStar_Ident.ident ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> aqual -> binder
  =
  fun id  ->
    fun t  ->
      fun should_bind_var  ->
        fun refopt  ->
          fun m  ->
            fun implicit  ->
              let b = mk_binder (Annotated (id, t)) m Type_level implicit  in
              match refopt with
              | FStar_Pervasives_Native.None  -> b
              | FStar_Pervasives_Native.Some phi ->
                  if should_bind_var
                  then
                    mk_binder
                      (Annotated
                         (id, (mk_term (Refine (b, phi)) m Type_level))) m
                      Type_level implicit
                  else
                    (let x = FStar_Ident.gen t.range  in
                     let b1 =
                       mk_binder (Annotated (x, t)) m Type_level implicit  in
                     mk_binder
                       (Annotated
                          (id, (mk_term (Refine (b1, phi)) m Type_level))) m
                       Type_level implicit)
  
let mkRefinedPattern :
  pattern ->
    term ->
      Prims.bool ->
        term FStar_Pervasives_Native.option ->
          FStar_Range.range -> FStar_Range.range -> pattern
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
                       | PatVar (x,uu____3296) ->
                           mk_term
                             (Refine
                                ((mk_binder (Annotated (x, t)) t_range
                                    Type_level FStar_Pervasives_Native.None),
                                  phi)) range Type_level
                       | uu____3299 ->
                           let x = FStar_Ident.gen t_range  in
                           let phi1 =
                             let x_var =
                               let uu____3303 =
                                 let uu____3304 = FStar_Ident.lid_of_ids [x]
                                    in
                                 Var uu____3304  in
                               mk_term uu____3303 phi.range Formula  in
                             let pat_branch =
                               (pat, FStar_Pervasives_Native.None, phi)  in
                             let otherwise_branch =
                               let uu____3316 =
                                 let uu____3317 =
                                   let uu____3318 =
                                     FStar_Ident.lid_of_path ["False"]
                                       phi.range
                                      in
                                   Name uu____3318  in
                                 mk_term uu____3317 phi.range Formula  in
                               ((mk_pattern PatWild phi.range),
                                 FStar_Pervasives_Native.None, uu____3316)
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
              mk_pattern (PatAscribed (pat, t1)) range
  
let rec extract_named_refinement :
  term ->
    (FStar_Ident.ident,term,term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun t1  ->
    match t1.tm with
    | NamedTyp (x,t) ->
        FStar_Pervasives_Native.Some (x, t, FStar_Pervasives_Native.None)
    | Refine
        ({ b = Annotated (x,t); brange = uu____3361; blevel = uu____3362;
           aqual = uu____3363;_},t')
        ->
        FStar_Pervasives_Native.Some
          (x, t, (FStar_Pervasives_Native.Some t'))
    | Paren t -> extract_named_refinement t
    | uu____3371 -> FStar_Pervasives_Native.None
  
let rec as_mlist :
  modul Prims.list ->
    ((FStar_Ident.lid,decl) FStar_Pervasives_Native.tuple2,decl Prims.list)
      FStar_Pervasives_Native.tuple2 -> decl Prims.list -> modul Prims.list
  =
  fun out  ->
    fun cur  ->
      fun ds  ->
        let uu____3401 = cur  in
        match uu____3401 with
        | ((m_name,m_decl),cur1) ->
            (match ds with
             | [] ->
                 FStar_List.rev
                   ((Module (m_name, (m_decl :: (FStar_List.rev cur1)))) ::
                   out)
             | d::ds1 ->
                 (match d.d with
                  | TopLevelModule m' ->
                      as_mlist
                        ((Module (m_name, (m_decl :: (FStar_List.rev cur1))))
                        :: out) ((m', d), []) ds1
                  | uu____3426 ->
                      as_mlist out ((m_name, m_decl), (d :: cur1)) ds1))
  
let as_frag :
  Prims.bool ->
    FStar_Range.range ->
      decl Prims.list -> (modul Prims.list,decl Prims.list) FStar_Util.either
  =
  fun is_light  ->
    fun light_range  ->
      fun ds  ->
        let uu____3449 =
          match ds with
          | d::ds1 -> (d, ds1)
          | [] -> raise FStar_Errors.Empty_frag  in
        match uu____3449 with
        | (d,ds1) ->
            (match d.d with
             | TopLevelModule m ->
                 let ds2 =
                   if is_light
                   then
                     let uu____3479 =
                       mk_decl (Pragma LightOff) light_range []  in
                     uu____3479 :: ds1
                   else ds1  in
                 let ms = as_mlist [] ((m, d), []) ds2  in
                 ((let uu____3487 = FStar_List.tl ms  in
                   match uu____3487 with
                   | (Module (m',uu____3490))::uu____3491 ->
                       let msg =
                         "Support for more than one module in a file is deprecated"
                          in
                       let uu____3496 =
                         FStar_Range.string_of_range
                           (FStar_Ident.range_of_lid m')
                          in
                       FStar_Util.print2_warning "%s (Warning): %s\n"
                         uu____3496 msg
                   | uu____3497 -> ());
                  FStar_Util.Inl ms)
             | uu____3501 ->
                 let ds2 = d :: ds1  in
                 (FStar_List.iter
                    (fun uu___78_3505  ->
                       match uu___78_3505 with
                       | { d = TopLevelModule uu____3506; drange = r;
                           doc = uu____3508; quals = uu____3509;
                           attrs = uu____3510;_} ->
                           raise
                             (FStar_Errors.Error
                                ("Unexpected module declaration", r))
                       | uu____3512 -> ()) ds2;
                  FStar_Util.Inr ds2))
  
let compile_op : Prims.int -> Prims.string -> Prims.string =
  fun arity  ->
    fun s  ->
      let name_of_char uu___79_3524 =
        match uu___79_3524 with
        | '&' -> "Amp"
        | '@' -> "At"
        | '+' -> "Plus"
        | '-' when arity = (Prims.parse_int "1") -> "Minus"
        | '-' -> "Subtraction"
        | '/' -> "Slash"
        | '<' -> "Less"
        | '=' -> "Equals"
        | '>' -> "Greater"
        | '_' -> "Underscore"
        | '|' -> "Bar"
        | '!' -> "Bang"
        | '^' -> "Hat"
        | '%' -> "Percent"
        | '*' -> "Star"
        | '?' -> "Question"
        | ':' -> "Colon"
        | uu____3525 -> "UNKNOWN"  in
      match s with
      | ".[]<-" -> "op_String_Assignment"
      | ".()<-" -> "op_Array_Assignment"
      | ".[]" -> "op_String_Access"
      | ".()" -> "op_Array_Access"
      | uu____3526 ->
          let uu____3527 =
            let uu____3528 =
              let uu____3530 = FStar_String.list_of_string s  in
              FStar_List.map name_of_char uu____3530  in
            FStar_String.concat "_" uu____3528  in
          Prims.strcat "op_" uu____3527
  
let compile_op' : Prims.string -> Prims.string =
  fun s  -> compile_op (~- (Prims.parse_int "1")) s 
let string_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu____3542  ->
    match uu____3542 with
    | (comment,keywords) ->
        let uu____3556 =
          let uu____3557 =
            FStar_List.map
              (fun uu____3561  ->
                 match uu____3561 with
                 | (k,v1) -> Prims.strcat k (Prims.strcat "->" v1)) keywords
             in
          FStar_String.concat "," uu____3557  in
        Prims.strcat comment uu____3556
  
let string_of_let_qualifier : let_qualifier -> Prims.string =
  fun uu___80_3568  ->
    match uu___80_3568 with
    | NoLetQualifier  -> ""
    | Rec  -> "rec"
    | Mutable  -> "mutable"
  
let to_string_l sep f l =
  let uu____3593 = FStar_List.map f l  in FStar_String.concat sep uu____3593 
let imp_to_string : imp -> Prims.string =
  fun uu___81_3597  ->
    match uu___81_3597 with | Hash  -> "#" | uu____3598 -> ""
  
let rec term_to_string : term -> Prims.string =
  fun x  ->
    match x.tm with
    | Wild  -> "_"
    | Requires (t,uu____3609) ->
        let uu____3612 = term_to_string t  in
        FStar_Util.format1 "(requires %s)" uu____3612
    | Ensures (t,uu____3614) ->
        let uu____3617 = term_to_string t  in
        FStar_Util.format1 "(ensures %s)" uu____3617
    | Labeled (t,l,uu____3620) ->
        let uu____3621 = term_to_string t  in
        FStar_Util.format2 "(labeled %s %s)" l uu____3621
    | Const c -> FStar_Parser_Const.const_to_string c
    | Op (s,xs) ->
        let uu____3627 =
          let uu____3628 =
            FStar_List.map
              (fun x1  -> FStar_All.pipe_right x1 term_to_string) xs
             in
          FStar_String.concat ", " uu____3628  in
        FStar_Util.format2 "%s(%s)" (FStar_Ident.text_of_id s) uu____3627
    | Tvar id -> id.FStar_Ident.idText
    | Uvar id -> id.FStar_Ident.idText
    | Var l -> l.FStar_Ident.str
    | Name l -> l.FStar_Ident.str
    | Construct (l,args) ->
        let uu____3643 =
          to_string_l " "
            (fun uu____3646  ->
               match uu____3646 with
               | (a,imp) ->
                   let uu____3651 = term_to_string a  in
                   FStar_Util.format2 "%s%s" (imp_to_string imp) uu____3651)
            args
           in
        FStar_Util.format2 "(%s %s)" l.FStar_Ident.str uu____3643
    | Abs (pats,t) ->
        let uu____3656 = to_string_l " " pat_to_string pats  in
        let uu____3657 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(fun %s -> %s)" uu____3656 uu____3657
    | App (t1,t2,imp) ->
        let uu____3661 = FStar_All.pipe_right t1 term_to_string  in
        let uu____3662 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format3 "%s %s%s" uu____3661 (imp_to_string imp)
          uu____3662
    | Let (Rec ,lbs,body) ->
        let uu____3671 =
          to_string_l " and "
            (fun uu____3674  ->
               match uu____3674 with
               | (p,b) ->
                   let uu____3679 = FStar_All.pipe_right p pat_to_string  in
                   let uu____3680 = FStar_All.pipe_right b term_to_string  in
                   FStar_Util.format2 "%s=%s" uu____3679 uu____3680) lbs
           in
        let uu____3681 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format2 "let rec %s in %s" uu____3671 uu____3681
    | Let (q,(pat,tm)::[],body) ->
        let uu____3693 = FStar_All.pipe_right pat pat_to_string  in
        let uu____3694 = FStar_All.pipe_right tm term_to_string  in
        let uu____3695 = FStar_All.pipe_right body term_to_string  in
        FStar_Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q)
          uu____3693 uu____3694 uu____3695
    | Seq (t1,t2) ->
        let uu____3698 = FStar_All.pipe_right t1 term_to_string  in
        let uu____3699 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "%s; %s" uu____3698 uu____3699
    | If (t1,t2,t3) ->
        let uu____3703 = FStar_All.pipe_right t1 term_to_string  in
        let uu____3704 = FStar_All.pipe_right t2 term_to_string  in
        let uu____3705 = FStar_All.pipe_right t3 term_to_string  in
        FStar_Util.format3 "if %s then %s else %s" uu____3703 uu____3704
          uu____3705
    | Match (t,branches) ->
        let uu____3718 = FStar_All.pipe_right t term_to_string  in
        let uu____3719 =
          to_string_l " | "
            (fun uu____3724  ->
               match uu____3724 with
               | (p,w,e) ->
                   let uu____3734 = FStar_All.pipe_right p pat_to_string  in
                   let uu____3735 =
                     match w with
                     | FStar_Pervasives_Native.None  -> ""
                     | FStar_Pervasives_Native.Some e1 ->
                         let uu____3737 = term_to_string e1  in
                         FStar_Util.format1 "when %s" uu____3737
                      in
                   let uu____3738 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format3 "%s %s -> %s" uu____3734 uu____3735
                     uu____3738) branches
           in
        FStar_Util.format2 "match %s with %s" uu____3718 uu____3719
    | Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
        let uu____3742 = FStar_All.pipe_right t1 term_to_string  in
        let uu____3743 = FStar_All.pipe_right t2 term_to_string  in
        FStar_Util.format2 "(%s : %s)" uu____3742 uu____3743
    | Ascribed (t1,t2,FStar_Pervasives_Native.Some tac) ->
        let uu____3748 = FStar_All.pipe_right t1 term_to_string  in
        let uu____3749 = FStar_All.pipe_right t2 term_to_string  in
        let uu____3750 = FStar_All.pipe_right tac term_to_string  in
        FStar_Util.format3 "(%s : %s by %s)" uu____3748 uu____3749 uu____3750
    | Record (FStar_Pervasives_Native.Some e,fields) ->
        let uu____3760 = FStar_All.pipe_right e term_to_string  in
        let uu____3761 =
          to_string_l " "
            (fun uu____3764  ->
               match uu____3764 with
               | (l,e1) ->
                   let uu____3769 = FStar_All.pipe_right e1 term_to_string
                      in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____3769)
            fields
           in
        FStar_Util.format2 "{%s with %s}" uu____3760 uu____3761
    | Record (FStar_Pervasives_Native.None ,fields) ->
        let uu____3778 =
          to_string_l " "
            (fun uu____3781  ->
               match uu____3781 with
               | (l,e) ->
                   let uu____3786 = FStar_All.pipe_right e term_to_string  in
                   FStar_Util.format2 "%s=%s" l.FStar_Ident.str uu____3786)
            fields
           in
        FStar_Util.format1 "{%s}" uu____3778
    | Project (e,l) ->
        let uu____3789 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format2 "%s.%s" uu____3789 l.FStar_Ident.str
    | Product ([],t) -> term_to_string t
    | Product (b::hd1::tl1,t) ->
        term_to_string
          (mk_term
             (Product
                ([b], (mk_term (Product ((hd1 :: tl1), t)) x.range x.level)))
             x.range x.level)
    | Product (b::[],t) when x.level = Type_level ->
        let uu____3803 = FStar_All.pipe_right b binder_to_string  in
        let uu____3804 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s -> %s" uu____3803 uu____3804
    | Product (b::[],t) when x.level = Kind ->
        let uu____3808 = FStar_All.pipe_right b binder_to_string  in
        let uu____3809 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s => %s" uu____3808 uu____3809
    | Sum (binders,t) ->
        let uu____3814 =
          let uu____3815 =
            FStar_All.pipe_right binders (FStar_List.map binder_to_string)
             in
          FStar_All.pipe_right uu____3815 (FStar_String.concat " * ")  in
        let uu____3820 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s * %s" uu____3814 uu____3820
    | QForall (bs,pats,t) ->
        let uu____3830 = to_string_l " " binder_to_string bs  in
        let uu____3831 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____3833 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "forall %s.{:pattern %s} %s" uu____3830 uu____3831
          uu____3833
    | QExists (bs,pats,t) ->
        let uu____3843 = to_string_l " " binder_to_string bs  in
        let uu____3844 =
          to_string_l " \\/ " (to_string_l "; " term_to_string) pats  in
        let uu____3846 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format3 "exists %s.{:pattern %s} %s" uu____3843 uu____3844
          uu____3846
    | Refine (b,t) ->
        let uu____3849 = FStar_All.pipe_right b binder_to_string  in
        let uu____3850 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:{%s}" uu____3849 uu____3850
    | NamedTyp (x1,t) ->
        let uu____3853 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "%s:%s" x1.FStar_Ident.idText uu____3853
    | Paren t ->
        let uu____3855 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format1 "(%s)" uu____3855
    | Product (bs,t) ->
        let uu____3860 =
          let uu____3861 =
            FStar_All.pipe_right bs (FStar_List.map binder_to_string)  in
          FStar_All.pipe_right uu____3861 (FStar_String.concat ",")  in
        let uu____3866 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "Unidentified product: [%s] %s" uu____3860
          uu____3866
    | t -> "_"

and binder_to_string : binder -> Prims.string =
  fun x  ->
    let s =
      match x.b with
      | Variable i -> i.FStar_Ident.idText
      | TVariable i -> FStar_Util.format1 "%s:_" i.FStar_Ident.idText
      | TAnnotated (i,t) ->
          let uu____3874 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____3874
      | Annotated (i,t) ->
          let uu____3877 = FStar_All.pipe_right t term_to_string  in
          FStar_Util.format2 "%s:%s" i.FStar_Ident.idText uu____3877
      | NoName t -> FStar_All.pipe_right t term_to_string  in
    let uu____3879 = aqual_to_string x.aqual  in
    FStar_Util.format2 "%s%s" uu____3879 s

and aqual_to_string : aqual -> Prims.string =
  fun uu___82_3880  ->
    match uu___82_3880 with
    | FStar_Pervasives_Native.Some (Equality ) -> "$"
    | FStar_Pervasives_Native.Some (Implicit ) -> "#"
    | uu____3881 -> ""

and pat_to_string : pattern -> Prims.string =
  fun x  ->
    match x.pat with
    | PatWild  -> "_"
    | PatConst c -> FStar_Parser_Const.const_to_string c
    | PatApp (p,ps) ->
        let uu____3888 = FStar_All.pipe_right p pat_to_string  in
        let uu____3889 = to_string_l " " pat_to_string ps  in
        FStar_Util.format2 "(%s %s)" uu____3888 uu____3889
    | PatTvar (i,aq) ->
        let uu____3894 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____3894 i.FStar_Ident.idText
    | PatVar (i,aq) ->
        let uu____3899 = aqual_to_string aq  in
        FStar_Util.format2 "%s%s" uu____3899 i.FStar_Ident.idText
    | PatName l -> l.FStar_Ident.str
    | PatList l ->
        let uu____3903 = to_string_l "; " pat_to_string l  in
        FStar_Util.format1 "[%s]" uu____3903
    | PatTuple (l,false ) ->
        let uu____3907 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(%s)" uu____3907
    | PatTuple (l,true ) ->
        let uu____3911 = to_string_l ", " pat_to_string l  in
        FStar_Util.format1 "(|%s|)" uu____3911
    | PatRecord l ->
        let uu____3916 =
          to_string_l "; "
            (fun uu____3919  ->
               match uu____3919 with
               | (f,e) ->
                   let uu____3924 = FStar_All.pipe_right e pat_to_string  in
                   FStar_Util.format2 "%s=%s" f.FStar_Ident.str uu____3924) l
           in
        FStar_Util.format1 "{%s}" uu____3916
    | PatOr l -> to_string_l "|\n " pat_to_string l
    | PatOp op -> FStar_Util.format1 "(%s)" (FStar_Ident.text_of_id op)
    | PatAscribed (p,t) ->
        let uu____3930 = FStar_All.pipe_right p pat_to_string  in
        let uu____3931 = FStar_All.pipe_right t term_to_string  in
        FStar_Util.format2 "(%s:%s)" uu____3930 uu____3931

let rec head_id_of_pat : pattern -> FStar_Ident.lid Prims.list =
  fun p  ->
    match p.pat with
    | PatName l -> [l]
    | PatVar (i,uu____3939) ->
        let uu____3942 = FStar_Ident.lid_of_ids [i]  in [uu____3942]
    | PatApp (p1,uu____3944) -> head_id_of_pat p1
    | PatAscribed (p1,uu____3948) -> head_id_of_pat p1
    | uu____3949 -> []
  
let lids_of_let defs =
  FStar_All.pipe_right defs
    (FStar_List.collect
       (fun uu____3970  ->
          match uu____3970 with | (p,uu____3975) -> head_id_of_pat p))
  
let id_of_tycon : tycon -> Prims.string =
  fun uu___83_3978  ->
    match uu___83_3978 with
    | TyconAbstract (i,uu____3980,uu____3981) -> i.FStar_Ident.idText
    | TyconAbbrev (i,uu____3987,uu____3988,uu____3989) ->
        i.FStar_Ident.idText
    | TyconRecord (i,uu____3995,uu____3996,uu____3997) ->
        i.FStar_Ident.idText
    | TyconVariant (i,uu____4013,uu____4014,uu____4015) ->
        i.FStar_Ident.idText
  
let decl_to_string : decl -> Prims.string =
  fun d  ->
    match d.d with
    | TopLevelModule l -> Prims.strcat "module " l.FStar_Ident.str
    | Open l -> Prims.strcat "open " l.FStar_Ident.str
    | Include l -> Prims.strcat "include " l.FStar_Ident.str
    | ModuleAbbrev (i,l) ->
        FStar_Util.format2 "module %s = %s" i.FStar_Ident.idText
          l.FStar_Ident.str
    | TopLevelLet (uu____4042,pats) ->
        let uu____4050 =
          let uu____4051 =
            let uu____4053 = lids_of_let pats  in
            FStar_All.pipe_right uu____4053
              (FStar_List.map (fun l  -> l.FStar_Ident.str))
             in
          FStar_All.pipe_right uu____4051 (FStar_String.concat ", ")  in
        Prims.strcat "let " uu____4050
    | Main uu____4059 -> "main ..."
    | Assume (i,uu____4061) -> Prims.strcat "assume " i.FStar_Ident.idText
    | Tycon (uu____4062,tys) ->
        let uu____4072 =
          let uu____4073 =
            FStar_All.pipe_right tys
              (FStar_List.map
                 (fun uu____4083  ->
                    match uu____4083 with | (x,uu____4088) -> id_of_tycon x))
             in
          FStar_All.pipe_right uu____4073 (FStar_String.concat ", ")  in
        Prims.strcat "type " uu____4072
    | Val (i,uu____4093) -> Prims.strcat "val " i.FStar_Ident.idText
    | Exception (i,uu____4095) ->
        Prims.strcat "exception " i.FStar_Ident.idText
    | NewEffect (DefineEffect (i,uu____4099,uu____4100,uu____4101)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | NewEffect (RedefineEffect (i,uu____4107,uu____4108)) ->
        Prims.strcat "new_effect " i.FStar_Ident.idText
    | SubEffect uu____4111 -> "sub_effect"
    | Pragma uu____4112 -> "pragma"
    | Fsdoc uu____4113 -> "fsdoc"
  
let modul_to_string : modul -> Prims.string =
  fun m  ->
    match m with
    | Module (uu____4117,decls) ->
        let uu____4121 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____4121 (FStar_String.concat "\n")
    | Interface (uu____4126,decls,uu____4128) ->
        let uu____4131 =
          FStar_All.pipe_right decls (FStar_List.map decl_to_string)  in
        FStar_All.pipe_right uu____4131 (FStar_String.concat "\n")
  
let error msg tm r =
  let tm1 = FStar_All.pipe_right tm term_to_string  in
  let tm2 =
    if (FStar_String.length tm1) >= (Prims.parse_int "80")
    then
      let uu____4158 =
        FStar_Util.substring tm1 (Prims.parse_int "0") (Prims.parse_int "77")
         in
      Prims.strcat uu____4158 "..."
    else tm1  in
  raise (FStar_Errors.Error ((Prims.strcat msg (Prims.strcat "\n" tm2)), r)) 